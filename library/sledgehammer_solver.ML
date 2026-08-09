signature PHI_SLEDGEHAMMER_SOLVER = sig

val override_parser : Sledgehammer.fact_override parser

(* The single argument of both entry points.  There is deliberately NO
   `default_options`: every call site spells the whole record out, because SML
   records have neither defaults nor an update syntax and a silently-defaulted
   field here changes proof behaviour without a compile error.

   async         -- fork the search.  MUST be false wherever the caller relies on
                    observing the failure (Auto_Fail propagating): forking and
                    observable failure are incompatible.
   proof_id      -- store key; NONE derives it from the goal (see below).
   read_store    -- governs BOTH reads (the on-disk store and the in-process
                    hash table); NONE falls back to the enable_proof_store config.
   write_store   -- governs BOTH writes, symmetrically.  Store self-maintenance
                    (invalidate_proof_cache) is deliberately NOT governed by
                    either: it can only trigger after a hit, and hits are already
                    gated by read_store.
   raise_Error_instead_of_Auto_Fail
                 -- true turns Auto_Fail into a fatal ERROR (for the Isar
                    methods); false lets Auto_Fail through to the caller. *)
type options = {improved      : bool,
                async         : bool,
                fact_override : Sledgehammer.fact_override,
                proof_id      : Phi_Proof_Store.proof_id option,
                timeout       : Time.time option,
                read_store    : bool option,
                write_store   : bool option,
                raise_Error_instead_of_Auto_Fail : bool}

(* Single-goal entry: attacks the LEADING subgoal, keyed on it alone.
   Multi-goal entry: attacks EVERY subgoal, keyed on all of them at once, and
   records ONE entry whose text is the subgoal proofs composed --
   "(p1)[1], (p2)[1], ...".

   The by-product comes back as a future in both, so the synchronous and the
   asynchronous case have exactly the same shape and downstream code is written
   once (synchronously it is a Future.value and joins for free).  Do NOT join it
   on the main path -- that turns async back into sync. *)
val auto     : options -> Proof.context -> thm -> string future * thm
val all_auto : options -> Proof.context -> thm -> (Time.time * string) future * thm

(* Which subgoals one call of the solver `f` is expected to consume:
     Leading     -- the first premise only
     Each_Goal   -- one premise per call, repeated until none is left
     All_At_Once -- every premise in a single call
   `async` and the scope are orthogonal; the returned list has the same length
   and shape either way, only the futures differ in when they are fulfilled.
   The returned bool says whether this call ACTUALLY forked -- the `async`
   argument does not, because the schematic guard can send a forked request back
   to synchronous execution. *)
datatype goal_scope = Leading | Each_Goal | All_At_Once

val async_prove : bool -> goal_scope
               -> (Proof.context * thm -> 'a * thm)
               -> Proof.context * thm
               -> bool * 'a future list * thm

val sledgehammer_params : string Config.T
val classical_prover_timeout : int Config.T

(* Exposed for testing: given a raw Sledgehammer proof string (e.g. "by (metis foo bar)"),
   tokenize, strip any leading `using` keyword, detect whether the tactic head is `metis`,
   and produce both the canonical proof string (as used today) and a `smt (cvc5) …`
   variant when applicable. The smt variant is always returned when `is_metis` holds;
   call sites gate on `smt_oracle` before actually evaluating it. *)
val mk_proof_candidates :
      string -> {is_metis : bool, metis_prf : string, smt_prf_opt : string option}

(* Internal_Failure means "this is a bug in the engine, not a proof that got
   away" -- it must reach the user with its payload, never be relabelled as
   "could not prove the goal" and never be answered by calling a fallback
   backend.  Unknown carries a payload too, for unclassified failures that still
   go down the ordinary fallback path. *)
datatype fail_reason = Too_Many_Subgoals | Timeout | Application_Fails | Subgoal_unsolved
                     | Unknown of string
                     | Prelude_Timeout | Subgoal_Fail of term
                     | Internal_Failure of string
exception Auto_Fail of fail_reason

datatype type_of_rule = T_SIMP | T_INTRO | T_ELIM | T_DEST | T_CONG | T_SPLIT | T_IFF | T_UNKNOWN
val infer_type_of_rule : string -> thm -> type_of_rule
val chk_simp  : term -> bool
val chk_elim  : thm -> bool
val chk_split : thm -> bool
val with_rule : bool -> string -> thm -> Context.generic -> Context.generic
val should_be_inserted : Proof.context -> term -> bool

val need_standard_tac : Proof.context -> thm -> bool

val collapse_iv : Facts.interval list -> Facts.interval list

val hasty_mode : bool Config.T

val get_sledgehammer_params : Proof.context -> (string * string) list

val fast_mepo_max_facts : int Config.T
val fast_mepo_tac : Time.time -> Proof.context -> int -> tactic

val eval_prf_str_stat : Keyword.keywords -> int -> (unit -> string * Proof.state) option
                     -> string -> Proof.state -> string * Proof.state

(* Replay one proof text.  `n` is the number of LEADING subgoals the text is
   expected to close, and must be passed explicitly -- several call sites run on
   a state with more subgoals than the text speaks for and must keep passing 1.
   The protection it installs is what Goal.conclude later peels off; the two
   have to come in a pair. *)
val eval_prf_str : Keyword.keywords -> int (*protect n*) -> Time.time -> string
                -> context_state -> (Time.time * string) * context_state

end

structure Phi_Sledgehammer_Solver : PHI_SLEDGEHAMMER_SOLVER = struct

local
  val log_path_ref: Path.T option Unsynchronized.ref = Unsynchronized.ref NONE
  fun get_log_path () =
    case !log_path_ref of
      SOME p => p
    | NONE =>
        let val home = getenv "ISABELLE_HOME_USER"
            val dir = Path.append (Path.explode home) (Path.basic "logs")
            val _ = Isabelle_System.make_directory dir
            val p = Path.append dir (Path.basic "auto_sledgehammer.log")
            val _ = log_path_ref := SOME p
        in p end
in
  fun sh_log msg =
    \<^try>\<open>File.append (get_log_path ()) (msg ^ "\n") catch _ => ()\<close>
end

(*** Preliminaries ***)

(** Options **)

val classical_prover_timeout =
        Attrib.setup_config_int \<^binding>\<open>classical_prover_timeout\<close> (K 3)

val fast_mepo_max_facts =
  Attrib.setup_config_int \<^binding>\<open>fast_mepo_max_facts\<close> (K 32)

val sledgehammer_params_fixed = [("isar_proofs", "false")]

val sledgehammer_params = Attrib.setup_config_string \<^binding>\<open>auto_sledgehammer_params\<close> (K "")
val preplay_timeout = Attrib.setup_config_int \<^binding>\<open>auto_sledgehammer_preplay_timeout\<close> (K 10)

fun get_sledgehammer_params ctxt =
  Config.get ctxt sledgehammer_params
    |> String.tokens (fn #"," => true | _ => false)
    |> map (fn s => case String.tokens (fn #"=" => true | _ => false) s
                      of [k,v] => (Symbol.trim_blanks k, Symbol.trim_blanks v)
                       | _ => error ("Invalid auto_sledgehammer_params : " ^ s))
    |> filter (fn ("mini_use_improved_SH", _) => false
                | _ => true)
    |> (fn L => sledgehammer_params_fixed @ L)

(** Helpers **)

fun error_message ctxt sequent =
  Pretty.string_of (Pretty.chunks (
    Pretty.para "Fail to prove the goal" ::
    (case Thm.prems_of sequent
       of (x::_)
            => [Syntax.pretty_term ctxt x]
        | _ => [])))

(** Infer Type of Rule **)

datatype type_of_rule = T_SIMP | T_INTRO | T_ELIM | T_DEST | T_CONG | T_SPLIT | T_IFF | T_UNKNOWN

(* True iff the theorem's proposition mentions any class-membership constraint
   OFCLASS(_, _) anywhere (conclusion or premises). Such "of class" theorems
   (e.g. `*_class.super`, `*.intro_of_class`) have a raw Pure-prop conclusion
   `OFCLASS(?'a, c_class)` rather than `Trueprop (_::bool)`; they are useless to
   object-level proof search and, fed into `Simpdata.mk_eq` (via `chk_split` /
   `infer_type_of_rule`), make its `RS Eq_TrueI` fallback raise a raw
   `THM "RSN: no unifiers"`. We drop them at every fact entry point. *)
fun is_of_class_thm th =
  Term.exists_subterm (fn t => can Logic.dest_of_class t) (Thm.prop_of th)

fun chk_elim th =
  case Thm.concl_of th
    of \<^Const>\<open>Trueprop\<close> $ (Var C) =>
      (case Thm.prems_of th
         of (\<^Const>\<open>Trueprop\<close> $ X) :: prems =>
             is_Const (Term.head_of X) andalso
             prems
          |> forall ( Logic.strip_assums_concl
                  #> (fn \<^Const>\<open>Trueprop\<close> $ Var C' => C = C'
                       | _ => false))
          | _ => false )
     | _ => false

fun dest_eq (\<^Const>\<open>Trueprop\<close> $ X) = dest_eq X
  | dest_eq (\<^Const>\<open>HOL.eq _\<close> $ A $ B)  = SOME (A,B)
  | dest_eq (\<^Const>\<open>Pure.eq _\<close> $ A $ B) = SOME (A,B)
  | dest_eq (\<^Const>\<open>HOL.implies\<close> $ _ $ X) = dest_eq X
  | dest_eq (\<^Const>\<open>HOL.All _\<close> $ Abs (_, _, X)) = dest_eq X
  | dest_eq (Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = dest_eq X
  | dest_eq _ = NONE

val chk_simp = is_some o dest_eq
fun chk_split thm =
  (case Thm.concl_of (Simpdata.mk_eq thm) of
    \<^Const_>\<open>Pure.eq _ for \<open>Var _ $ t\<close> c\<close> =>
      (case strip_comb t of
        (Const p, _) => true
      | _ => false)
  | _ => false)
  handle THM _ => false   (* Simpdata.mk_eq's `RS Eq_TrueI` fallback fails on
                             non-Trueprop (e.g. OFCLASS) conclusions *)
       | TERM _ => false; (* fastype_of: Bound when mk_eq decomposes a quantified
                             fact whose body has loose de Bruijn indices *)

local

fun chk_cong th =
    case Thm.concl_of th
      of (\<^Const>\<open>Pure.eq _\<close> $ LHS $ RHS) =>
        let exception NO in
        let val (LH, LAS) = strip_comb LHS
            val (RH, RAS) = strip_comb RHS
            val _ = if LH = RH andalso
                       length LAS = length RAS andalso
                       forall is_Var LAS andalso
                       forall is_Var RAS andalso
                       not (has_duplicates (op =) (LAS @ RAS))
                    then () else raise NO
            val prems = Thm.prems_of th
                     |> map (fn tm =>
                        case Logic.strip_assums_concl tm
                          of \<^Const>\<open>Pure.eq _\<close> $ L $ R => (L,R)
                           | _ => raise NO)
         in eq_set (op =) (prems, LAS ~~ RAS)
        end handle NO => false
        end
       | _ => false

fun lower_name name =
  let val len = size name
   in if len < 3 then NONE
   else let
      val last = String.sub (name, len - 1)
      val (suffix_len, result) =
            if last = #"I" then
              if String.sub (name, len - 2) = #"C" then (2, T_INTRO) else (1, T_INTRO)
            else if last = #"E" then (1, T_ELIM)
            else if last = #"D" then (1, T_DEST)
            else (0, T_UNKNOWN)
    in if suffix_len = 0 then NONE
    else let
      val stop = len - suffix_len
      val N = Unsynchronized.ref 0
      val i = Unsynchronized.ref 0
    in while !i < stop do (
         if Char.isUpper (String.sub (name, !i)) then N := 0 else N := !N + 1;
         i := !i + 1);
       if !N >= 2 then SOME result else NONE
    end end
  end

in

fun infer_type_of_rule name th =
  if String.isSuffix "_intro"  name orelse
     String.isSuffix ".intro"  name orelse
     String.isSuffix "_intros" name orelse
     String.isSuffix ".intros" name
     then T_INTRO
  else if String.isSuffix "_elim"  name orelse
          String.isSuffix ".elim"  name orelse
          String.isSuffix "_elims" name orelse
          String.isSuffix ".elims" name
       then T_ELIM
  else if String.isSuffix "_simp"   name orelse
          String.isSuffix ".simp"   name orelse
          String.isSuffix "_simps"  name orelse
          String.isSuffix ".simps"  name orelse
          String.isSuffix "_iff"    name orelse
          String.isSuffix "_unfold" name
       then T_SIMP
  else if String.isSuffix "_def" name then T_IFF
  else if String.isSuffix "_split"     name orelse
          String.isSuffix ".split"     name orelse
          String.isSuffix "_splits"    name orelse
          String.isSuffix ".splits"    name orelse
          String.isSuffix "_split_asm" name orelse
          String.isSuffix ".split_asm" name
       then T_SPLIT
  else if String.isSuffix "_dest" name orelse
          String.isSuffix ".dest" name
       then T_DEST
  else if String.isSuffix "_cong" name orelse
          String.isSuffix ".cong" name
       then T_CONG
  else if chk_cong th then T_CONG
  else if chk_split th then T_SPLIT
  else if chk_elim th then T_ELIM
  else if chk_simp (Thm.concl_of th) then T_SIMP
  else (case lower_name name
    of SOME ret => ret
     | NONE => T_UNKNOWN)

local
val split_add = Simplifier.attrib Splitter.add_split;
val split_del = Simplifier.attrib Splitter.del_split;

val T_INTRO_add = Classical.unsafe_intro NONE
val T_ELIM_add  = Classical.unsafe_elim  NONE
val T_DEST_add  = Classical.unsafe_dest  NONE
(* fun comb att1 att2 (c,th) =
  let val (c',th') = att1 (c,th)
      val c' = the_default c c'
      val th' = the_default th th'
   in att2 (c',th')
  end *)
in
fun modifier_of true  T_SIMP  = Simplifier.simp_add
  | modifier_of false T_SIMP  = Simplifier.simp_del
  | modifier_of true  T_INTRO = T_INTRO_add
  | modifier_of false T_INTRO = Classical.rule_del
  | modifier_of true  T_ELIM  = T_ELIM_add
  | modifier_of false T_ELIM  = Classical.rule_del
  | modifier_of true  T_DEST  = T_DEST_add
  | modifier_of false T_DEST  = Classical.rule_del
  | modifier_of true  T_CONG  = Simplifier.cong_add
  | modifier_of false T_CONG  = Classical.rule_del
  | modifier_of true  T_SPLIT = split_add
  | modifier_of false T_SPLIT = split_del
  | modifier_of true  T_IFF   = Clasimp.iff_add
  | modifier_of false T_IFF   = Clasimp.iff_del
  | modifier_of true  T_UNKNOWN = Simplifier.simp_add
  | modifier_of false T_UNKNOWN = Simplifier.simp_del

end

fun with_rule add name rule ctxt =
  Thm.apply_attribute (modifier_of add (infer_type_of_rule name rule)) rule ctxt |> snd

fun may_entail_false prop =
  let fun go_prop (Const (\<^const_name>\<open>Trueprop\<close>, _) $ t) = go t
        | go_prop (Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ B) = go_prop B
        | go_prop (Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, t)) = go_prop t
        | go_prop _ = false
      and go (Const (\<^const_name>\<open>False\<close>, _)) = true
        | go (Const (\<^const_name>\<open>conj\<close>, _) $ A $ B) = go A orelse go B
        | go (Const (\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ B) = go B
        | go (Const (\<^const_name>\<open>All\<close>, _) $ Abs (_, _, t)) = go t
        | go (Const (\<^const_name>\<open>Ex\<close>, _) $ Abs (_, _, t)) = go t
        | go _ = false
  in go_prop prop end

fun should_be_inserted ctxt  =
  let val outter = try Local_Theory.target_of ctxt
      fun is_new name = case outter of NONE => true
                                     | SOME ctxt' => Variable.is_newly_fixed ctxt ctxt' name
   in fn rule =>
      may_entail_false rule orelse (
      Term.add_free_names rule []
   |> filter is_new
   |> null
   |> not)
  end

end

(** MePo-guided fastforce: defined later, after eval_prf_str / restore_ref /
    render_fastforce_src are in scope. **)

(** Does it need the standard tac? **)

fun need_standard_tac ctxt st =
  let val thy = Proof_Context.theory_of ctxt
      val (\<^Const>\<open>Trueprop\<close> $ goal) = Thm.major_prem_of st
      val Const(name, _) = head_of goal
      fun pass [] = []
        | pass ["class", x] = [x]
        | pass (h::L) = h :: pass L
      fun qchk [] = false
        | qchk ["class", _] = true
        | qchk (_::L) = qchk L
      val idts = Long_Name.explode name
      val name' = if qchk idts then Long_Name.implode (pass idts) else name
   in Locale.defined thy name'
  end handle Bind => false

(*** Adapter of Sledgehammer ***)

(*copied and modified from Isabelle-2022/src/HOL/Tools/Sledgehammer/sledgehammer_proof_methods.ML
  Original Author: Jasmin Blanchette, TU Muenchen
                   Steffen Juilf Smolka, TU Muenchen

  May need to be synced once updated.
*)
local open Sledgehammer_Proof_Methods

fun is_proof_method_direct (Metis_Method _) = true
  | is_proof_method_direct Meson_Method = true
  | is_proof_method_direct (SMT_Method _) = true
  | is_proof_method_direct Simp_Method = true
  | is_proof_method_direct _ = false

fun is_proof_method_multi_goal Auto_Method = true
  | is_proof_method_multi_goal _ = false

fun string_of_proof_method ss meth =
  let
    val meth_s =
      (case meth of
        Metis_Method (NONE, NONE, additional_fact_names) =>
        space_implode " " ("metis" :: additional_fact_names)
      | Metis_Method (type_enc_opt, lam_trans_opt, additional_fact_names) =>
        space_implode " "
          (("metis (" ^ commas (map_filter I [type_enc_opt, lam_trans_opt]) ^ ")")
            :: additional_fact_names)
      | Meson_Method => "meson"
      | SMT_Method SMT_Z3 => "smt (z3)"
      | SMT_Method (SMT_Verit strategy) =>
        "smt (" ^ commas ("verit" :: (if strategy = "default" then [] else [strategy])) ^ ")"
      | SATx_Method => "satx"
      | Blast_Method => "blast"
      | Simp_Method => if null ss then "simp" else "simp add:"
      | Auto_Method => "auto"
      | Fastforce_Method => "fastforce"
      | Force_Method => "force"
      | Moura_Method => "moura"
      | Linarith_Method => "linarith"
      | Presburger_Method => "presburger"
      | Algebra_Method => "algebra")
  in
    space_implode " " (meth_s :: ss)
  end

in

fun proof_method_command meth n extras =
  let
    val (indirect_ss, direct_ss) =
      if is_proof_method_direct meth then ([], extras) else (extras, [])
  in
    (if null indirect_ss then "" else "(insert " ^ space_implode " " indirect_ss ^ ")[1], ") ^
    (if is_proof_method_multi_goal meth andalso n <> 1
      then "(" ^ string_of_proof_method direct_ss meth ^ ")[1]"
      else string_of_proof_method direct_ss meth)
  end

fun one_line_proof_text (used_facts, meth, subgoal_count) =
  let val (_, extra) = List.partition (fn (_, (sc, _)) => sc = ATP_Problem_Generate.Chained) used_facts in
    map fst extra
    |> proof_method_command meth subgoal_count
  end

end

val silence_state =
      Proof.map_contexts (Try0_HOL.silence_methods #> Config.put SMT_Config.verbose false)

val debug_state =
      Proof.map_contexts (Try0_HOL.silence_methods #> Config.put SMT_Config.verbose true
          #> Config.put SMT_Config.trace true #> Config.put SMT_Config.statistics true )

fun time_ord (t1 : Time.time, t2) =
  if t1 = t2 then EQUAL else if t1 < t2 then LESS else GREATER
fun preplay_ord ((_, Sledgehammer_Proof_Methods.Played t1, _),
                 (_, Sledgehammer_Proof_Methods.Played t2, _))
      = time_ord (t1,t2)
  | preplay_ord ((_, Sledgehammer_Proof_Methods.Played _, _),
                 (_, Sledgehammer_Proof_Methods.Play_Timed_Out _, _))
      = LESS
  | preplay_ord ((_, Sledgehammer_Proof_Methods.Play_Timed_Out _, _),
                 (_, Sledgehammer_Proof_Methods.Played _, _))
      = GREATER
  | preplay_ord ((_, Sledgehammer_Proof_Methods.Play_Timed_Out _, _),
                 (_, Sledgehammer_Proof_Methods.Play_Timed_Out _, _))
      = EQUAL

datatype fail_reason = Too_Many_Subgoals | Timeout | Application_Fails | Subgoal_unsolved
                     | Unknown of string
                     | Prelude_Timeout | Subgoal_Fail of term
                     | Internal_Failure of string
exception Auto_Fail of fail_reason

(* Total order on failure reasons; merging several takes the MAXIMUM, and ties
   keep the first.  Internal_Failure outranks everything because a bug must not
   be hidden behind a proof-search verdict. *)
fun reason_rank (Internal_Failure _) = 7
  | reason_rank (Subgoal_Fail _)     = 6
  | reason_rank Too_Many_Subgoals    = 5
  | reason_rank Timeout              = 4
  | reason_rank Prelude_Timeout      = 3
  | reason_rank Application_Fails    = 2
  | reason_rank Subgoal_unsolved     = 1
  | reason_rank (Unknown _)          = 0

(* Classify ONE exception.  The interrupt test is repeated per component and is
   NOT redundant with the one in `normalise`: Par_Exn's invariant only excludes
   interrupt_PROPER, and Exn.Interrupt_Breakdown is not proper, so it may sit
   inside a Par_Exn -- while Exn.is_interrupt of the Par_Exn container itself is
   false.  Without this line a user cancellation gets reported as an engine bug. *)
fun classify exn =
      if Exn.is_interrupt exn then Exn.reraise exn
      else case exn of
             Auto_Fail r       => r
           | Timeout.TIMEOUT _ => Timeout
           | _                 => Internal_Failure (Runtime.exn_message exn)

(* Turn ANY escaping exception into the engine's own vocabulary.  Install it at
   the exits of the proof-search branches and NOWHERE inside them: the engine
   uses cancellation to say "stop, someone else won", and converting that inside
   a branch would turn an interrupt into a failure.

   Par_Exn is a CONTAINER, not a kind of failure -- open it and classify the
   contents.  Never use `Par_Exn.dest exn = SOME _` as a test for "this was a
   parallel failure": an interrupt destructures to SOME [] as well. *)
fun normalise exn =
  if Exn.is_interrupt exn then Exn.reraise exn
  else case exn of
    Auto_Fail _       => Exn.reraise exn                 (*already our vocabulary*)
  | Timeout.TIMEOUT _ => raise Auto_Fail Timeout
  | _ =>
      let val parts = case Par_Exn.dest exn of SOME (l as _::_) => l | _ => [exn]
          val worst =
            case map classify parts of
              [] => Internal_Failure (Runtime.exn_message exn)
            | r :: rs => fold (fn r' => fn acc =>
                                 if reason_rank r' > reason_rank acc then r' else acc) rs r
       in raise Auto_Fail
            (* the payload describes the ORIGINAL exception, container and all *)
            (case worst of Internal_Failure _ => Internal_Failure (Runtime.exn_message exn)
                         | r => r)
      end

fun head_only tac th =
  if Thm.nprems_of th = 0
  then all_tac th
  else Goal.protect 1 th |> tac |> Seq.map Goal.conclude

fun auto_obligation_solver (ctxt, th) = Seq.make (fn () =>
       Seq.pull (head_only (SOLVED' (fn _ => Clasimp.auto_tac ctxt) 1) th))

fun auto_obligation_solver1 (ctxt, th) = th
       |> head_only (SOLVED' (fn _ => Clasimp.auto_tac ctxt) 1)
       |> Seq.pull
       |> (fn NONE => raise Auto_Fail Application_Fails
            | SOME (th', _) => (ctxt, th'))

(* `""` is NOT a proof text.  It used to mean "originally closed by classical
   automation", and replaying it re-RAN auto -- a search instruction wearing a
   replay's clothes.  With that clause gone, `""` has no producer left, so a
   store hit can never start a proof search.  Stock `""` records need no special
   rule: the parser rejects them, which lands in the catch-all below, which the
   caching layer reads as "cached proof no longer works, search again". *)
fun eval_prf_str kws n timeout prf (ctxt,sequent) = \<^try>\<open>
      let val _ = sh_log ("[eval_prf_str] replaying: " ^ quote prf)
          val protected = Goal.protect n sequent
          val seq =
            Method.evaluate (
              Parse.read_embedded ctxt kws (Method.parser 0) (Input.string prf)
                |> fst
                |> Method.check_text ctxt
              ) ctxt [] (ctxt, protected)
        in case Timeout.apply timeout (Timing.timing (
                    Position.setmp_thread_data Position.none Seq.pull)) seq
             of ({elapsed=time,...}, SOME (Seq.Result (ctxt', sequent'), _)) =>
                  if Thm.no_prems sequent'
                  then ((time,prf), (ctxt', Goal.conclude sequent'))
                  else raise Auto_Fail Subgoal_unsolved
              | _ => raise Auto_Fail Application_Fails
      end catch Timeout.TIMEOUT _ => raise Auto_Fail Timeout
              | Auto_Fail err => Exn.reraise (Auto_Fail err)
              | err => (sh_log ("[eval_prf_str] FAILED on " ^ quote prf ^ ": " ^
                                 Runtime.exn_message err);
                         raise Auto_Fail (Unknown (Runtime.exn_message err))) \<close>


fun eval_prf_str_stat kws timeout F_None prf stat =
    let val ctxt = Proof.context_of stat
    in \<^try>\<open>
       (case Timeout.apply (Time.fromSeconds timeout)
                (Position.setmp_thread_data Position.none Seq.pull)
                (Proof.apply (Parse.read_embedded ctxt kws Method.parse
                                                  (Input.string ("(" ^ prf ^ ")"))) stat)
          of (SOME (Seq.Result stat', _)) => (prf, stat')
           | _ => case F_None of SOME f => f()
                               | NONE => raise Auto_Fail Application_Fails)
        catch Timeout.TIMEOUT _ => (
          sh_log "The proof fails due to timeout. Re-searching proofs...";
          raise Auto_Fail Timeout)
            | Auto_Fail reason => raise Auto_Fail reason
            | err => (
          sh_log ("Unexpected error, maybe a bug: " ^ Runtime.exn_message err);
          raise Auto_Fail (Unknown (Runtime.exn_message err))) \<close>
    end


(** Sledgehammer **)

val full_keywords = Thy_Header.get_keywords \<^theory>
val keywords = Keyword.no_major_keywords full_keywords

val hasty_mode = Attrib.setup_config_bool \<^binding>\<open>auto_sledgehammer_hasty\<close> (K false)

local
  fun is_open_paren  t = Token.keyword_with (fn s => s = "(") t
  fun is_close_paren t = Token.keyword_with (fn s => s = ")") t
  fun drop_leading_paren_group (t :: rest) =
        if is_open_paren t
        then let fun skip d (x :: xs) =
                      if is_open_paren  x then skip (d+1) xs
                      else if is_close_paren x then
                           if d <= 1 then xs else skip (d-1) xs
                      else skip d xs
                  | skip _ [] = []
              in skip 1 rest end
        else t :: rest
    | drop_leading_paren_group [] = []
  fun build_variant replace_metis toks1 =
    let val sep = find_index (fn tok => Token.is_command tok andalso
                                        (Token.content_of tok = "apply" orelse
                                         Token.content_of tok = "by")) toks1
        val (using, tac) = if sep = ~1 then raise Fail "internal bug #e12asfwgy44"
                           else (take sep toks1, drop (sep+1) toks1)
        val (lead_open, body) =
              case tac of
                (t :: rest) => if is_open_paren t then ([t], rest) else ([], tac)
              | [] => ([], tac)
        val (is_metis, body') =
              case body of
                (t :: rest) =>
                  if Token.content_of t = "metis" andalso not (Token.is_command t)
                  then (true, drop_leading_paren_group rest)
                  else (false, body)
              | [] => (false, body)
        fun unparse toks = String.concatWith " " (map Token.unparse toks)
        fun unparse_tac (tok1::tok2::R) =
              if Token.keyword_with (fn s => s = "[") tok2
                 andalso not (Token.keyword_with (K true) tok1)
              then "(" ^ unparse [tok1] ^ ")" ^ unparse (tok2::R)
              else unparse (tok1::tok2::R)
          | unparse_tac toks = unparse toks
        val rhs =
              if is_metis andalso replace_metis
              then unparse lead_open ^ "smt (cvc5) " ^ unparse body'
              else unparse_tac tac
     in (is_metis,
         (if null using then "" else "(insert " ^ unparse using ^ ")[1], ") ^ rhs)
    end
in
fun mk_proof_candidates s_prf =
  let val tokens = Input.string s_prf
                      |> Input.source_explode
                      |> Token.tokenize full_keywords {strict = true}
                      |> filter Token.is_proper
      val toks1 = case tokens of
                    [] => raise Fail "internal bug #e12asfwgy43"
                  | (tok::L) =>
                      if Token.is_command tok andalso Token.content_of tok = "using"
                      then L else tok::L
      val (is_metis, prf) = build_variant false toks1
      val smt_prf_opt =
            if is_metis then SOME (#2 (build_variant true toks1)) else NONE
   in {is_metis = is_metis, metis_prf = prf, smt_prf_opt = smt_prf_opt}
  end
end

fun debug_param {debug=debug, verbose=verbose, overlord=overlord, spy=spy, provers=provers,
                 abduce=abduce, falsify=falsify, type_enc=type_enc, strict=strict, lam_trans=lam_trans,
                 uncurried_aliases=uncurried_aliases, learn=learn, fact_filter=fact_filter,
                 induction_rules=induction_rules, max_facts=max_facts, fact_thresholds=fact_thresholds,
                 max_mono_iters=max_mono_iters, max_new_mono_instances=max_new_mono_instances,
                 max_proofs=max_proofs, isar_proofs=isar_proofs, compress=compress, try0=try0,
                 smt_proofs=smt_proofs, minimize=minimize, slices=slices, timeout=timeout,
                 preplay_timeout=preplay_timeout, expect=expect} =
      {debug=true, verbose=true, overlord=overlord, spy=spy, provers=provers,
       abduce=abduce, falsify=falsify, type_enc=type_enc, strict=strict, lam_trans=lam_trans,
       uncurried_aliases=uncurried_aliases, learn=learn, fact_filter=fact_filter,
       induction_rules=induction_rules, max_facts=max_facts, fact_thresholds=fact_thresholds,
       max_mono_iters=max_mono_iters, max_new_mono_instances=max_new_mono_instances,
       max_proofs=max_proofs, isar_proofs=isar_proofs, compress=compress, try0=try0,
       smt_proofs=smt_proofs, minimize=minimize, slices=slices, timeout=timeout,
       preplay_timeout=preplay_timeout, expect=expect}


fun raw_sledgehammer timeout_opt override hasty stat =
  let val N = #goal (Proof.goal stat) |> Thm.nprems_of
      val _ = if N = 0 then error "No subgoal!" else ()
      val shortcut = Single_Assignment.var "\<phi>sledgehammer.shortcut"
      val futures = Synchronized.var "\<phi>sledgehammer.futures" []
      val found_proof = Synchronized.var "\<phi>sledgehammer.found_proof" false
      val sledgehammer_params = get_sledgehammer_params (Proof.context_of stat)
      val ctxt = Proof.context_of stat
      val pptimeout = Config.get ctxt preplay_timeout
      val try_cvc5 = Config.get ctxt SMT_Config.oracle
      val group = Future.new_group (Future.worker_group ())
      val effective_timeout = case timeout_opt of
            SOME t => SOME t
          | NONE => (case AList.lookup (op =) sledgehammer_params "timeout" of
              SOME s => Option.mapPartial (fn secs =>
                  if secs <= 0 then NONE else SOME (Time.fromSeconds secs))
                (Int.fromString s)
            | NONE => let val secs = Options.default_int \<^system_option>\<open>sledgehammer_timeout\<close>
                       in if secs <= 0 then NONE else SOME (Time.fromSeconds secs) end)
      val deadline = Option.map (fn t => Time.scale 0.8 t) effective_timeout

      fun dirty_hack s =
        if String.isSubstring "found a falsification" s
        then Future.cancel_group group
        else if hasty
        then if String.isSubstring "found a proof" s
          then let
             val ret = Proof.refine (Method.Basic (fn ctxt =>
                          Method.METHOD (fn _ => Skip_Proof.cheat_tac ctxt 1))) stat
                    |> Seq.the_result "cheat fails?!"
          in (Single_Assignment.assign shortcut ("<cheat>", ret) handle Fail _ => ())
           ; Future.cancel_group group
         end
         else ()
        else
        let val _ = if String.isSubstring "found a proof" s
                    then Synchronized.change found_proof (K true) else ()
            fun tree_text (XML.Elem (_, ts)) = String.concat (map tree_text ts)
              | tree_text (XML.Text t) = t
            fun find_sendback (XML.Elem ((name, _), ts)) =
                  if name = Markup.sendbackN then SOME (String.concat (map tree_text ts))
                  else get_first find_sendback ts
              | find_sendback (XML.Text _) = NONE
         (* Isabelle2025-2: the proof command lives inside a `sendback` markup
            element (Active.sendback_markup_command); the old 2nd/3rd-ENQ slice
            now lands on an inserted `Markup.break " "` (a single space).
            Non-suggestion messages ("... found a proof ...", "Duplicate proof")
            carry no sendback element and are just logged. *)
         in case get_first find_sendback (YXML.parse_body s)
            of NONE => sh_log s
             | SOME s_prf => let
              (* preplay time suffix "(NN ms)"/"(NN s)": a "(" followed by a digit.
                 Proof-command parens ("(metis ...", "(smt ...") are followed by a
                 letter, so this reliably detects a successful preplay. *)
              val preplay_succeeded = is_some (CharVector.findi (fn (i, c) =>
                    c = #"(" andalso i + 1 < size s andalso Char.isDigit (String.sub (s, i + 1))) s)
              val {is_metis = _, metis_prf = prf, smt_prf_opt = raw_smt_opt} =
                    mk_proof_candidates s_prf
              val smt_prf_opt = if try_cvc5 then raw_smt_opt else NONE
              val _ = sh_log s
              fun eval_future () =
                let val candidates = prf :: (case smt_prf_opt of SOME s => [s] | NONE => [])
                    val new_futures = Future.forks {name="SH-preplay", group = SOME group, deps = [], pri=50, interrupts=true}
                      (map (fn p => fn () =>
                        case try (Future.interruptible_task (eval_prf_str_stat keywords pptimeout NONE p)) stat
                          of SOME ret => (
                               (Single_Assignment.assign shortcut ret handle Fail _ => ())
                             ; Future.cancel_group group)
                           | NONE => ()) candidates)
                 in Synchronized.change futures (fn L => new_futures @ L)
                end
              in if preplay_succeeded
               then case try (eval_prf_str_stat keywords 3 NONE prf) stat
                   of SOME ret => (
                          (Single_Assignment.assign shortcut ret handle Fail _ => ())
                        ; Future.cancel_group group)
                    | NONE => eval_future ()
               else eval_future ()
             end
        end

      val watchdog = Option.map (fn dl =>
            Event_Timer.request {physical = true} (Time.now () + dl) (fn () =>
              if not (Synchronized.value found_proof)
              then (sh_log "no proof found. give up in advance"; Future.cancel_group group)
              else ()))
          deadline

   in Future.forks {name="\<phi>SH", group = SOME group, deps = [], pri=10, interrupts=true} [(fn () =>
        ( Sledgehammer.run_sledgehammer
            (Sledgehammer_Commands.default_params (Proof.theory_of stat) sledgehammer_params)
                Sledgehammer_Prover.Normal
                (SOME dirty_hack) 1 override
                (silence_state stat)
        ; ()))]
    |> Future.join_results
     ; Future.join_results (Synchronized.value futures)
     ; (case watchdog of SOME req => ignore (Event_Timer.cancel req) | NONE => ())
     ; Future.cancel_group group
     ; Single_Assignment.peek shortcut
  end

(*** Proof search using Sledgehammer ***)

datatype goal_scope = Leading | Each_Goal | All_At_Once

local

(* The ONE guard, and it is a kernel constraint rather than a policy: the
   proposition promised to Goal.future_result must be free of schematic
   variables or the kernel refuses it outright.

   Term.maxidx_term, NEVER Thm.maxidx_of_cterm: Thm.cprem_of copies the WHOLE
   sequent's maxidx into each premise's cterm, and in this system the protected
   conclusion almost always carries schematics -- judging by the cterm's maxidx
   would misfire on every goal and switch asynchrony off permanently.

   Nothing object-logic-specific belongs here.  This combinator lives in the
   HOL-and-below layer and is used by callers that know nothing of each other. *)
fun is_schematic t = Term.maxidx_term t ~1 <> ~1

(* Fork the proof of `goal`, starting the solver from `goal_state`.  Returns the
   by-product future and the theorem of `goal` that the promise stands for.
   Only ONE fork happens: the ('a * thm) future is split with Future.map, which
   builds dependent tasks rather than running the proof a second time. *)
fun fork_state ctxt f (goal : cterm, goal_state : thm) =
  let
    val pos = Position.make (Thread_Position.get ())
    val hyps = Assumption.all_assms_of ctxt
    val promise = Drule.list_implies (hyps, goal)
    fun body () =
      let
        val (a, st) = f (ctxt, goal_state)
        (* Goal.conclude does NOT check that the state is finished; skipping this
           turns an unsolved subgoal into a `bad prop` at fulfilment time, far
           from the cause. *)
        val th = Goal.check_finished ctxt st
              |> fold_rev Thm.implies_intr hyps
              |> Goal.conclude
        val _ =
          if Thm.prop_of th aconv Thm.term_of promise then ()
          else raise THM ("async_prove: the solver returned a conclusion that is \
                          \not the one it was given", 0, [th])
      in (a, th) end
    val future = Execution.fork {name = "\<phi>System-async-proof", pos = pos, pri = ~1} (fn _ =>
      case Exn.capture_body body of
        Exn.Res r => r
        (* execution.ML hardcodes `if exec_id = 0 then ()`, so under batch builds
           and Isa-REPL a failing fork body prints NOTHING.  The third component
           must be NONE for the message to be printed unconditionally. *)
      | Exn.Exn exn =>
          (if Exn.is_interrupt exn then ()
           else Future.error_message pos ((serial (), Runtime.exn_message exn), NONE);
           Exn.reraise exn))
    val _ = Phi_Proof_Store.register_async_task (Future.task_of future)
              (Proof_Context.theory_of ctxt)
    val proved =
      Goal.future_result ctxt (Future.map snd future) (Thm.term_of promise)
        |> fold (fn a => fn th => Thm.implies_elim th (Thm.assume a)) hyps
  in (Future.map fst future, proved) end

(* What the solver was supposed to have consumed.  Leading can only assert "one
   fewer premise" -- it attacks the major premise by definition and several of
   its call sites run on states with more subgoals than that. *)
fun check_exit scope nprems (forked, futs, sequent') =
 (case scope of
    Leading =>
      if Thm.nprems_of sequent' = nprems - 1 then ()
      else raise THM ("async_prove/Leading: the solver did not consume exactly \
                      \one subgoal", 0, [sequent'])
  | _ =>
      if Thm.no_prems sequent' then ()
      else raise THM ("async_prove: subgoals were left unsolved", 0, [sequent']);
  (forked, futs, sequent'))

in

fun async_prove async scope f (ctxt, sequent) =
  (* Zero subgoals short-circuit, for all three scopes at once: Leading's exit
     assertion would demand -1 premises; All_At_Once's promise
     Conjunction.intr_balanced [] quietly degenerates to asm_rl while the inverse
     Conjunction.elim_balanced 0 raises List.Empty. *)
  if Thm.no_prems sequent then (false, [], sequent)
  else
  let
    val nprems = Thm.nprems_of sequent
    val cprems = map (Thm.cprem_of sequent) (1 upto nprems)
    val targets = case scope of Leading => [hd cprems] | _ => cprems
    val assms_ok = not (exists (is_schematic o Thm.term_of) (Assumption.all_assms_of ctxt))
    val bad = find_index (is_schematic o Thm.term_of) targets
    val forking = async andalso assms_ok andalso bad < 0
    val _ =
      if async andalso not forking
      then sh_log ("[async_prove] running synchronously instead: " ^
                   (if not assms_ok
                    then "a context assumption contains a schematic variable"
                    else "subgoal " ^ string_of_int (bad + 1) ^
                         " contains a schematic variable"))
      else ()
  in
    check_exit scope nprems (
    if not forking
    then
      (case scope of
         (* the loop that used to live in all_auto: one premise per call *)
         Each_Goal =>
           let fun loop sequent acc =
                 if Thm.no_prems sequent then (rev acc, sequent)
                 else let val (a, sequent') = f (ctxt, sequent)
                       in loop sequent' (a :: acc) end
               val (as_, sequent') = loop sequent []
            in (false, map Future.value as_, sequent') end
       | _ =>
           let val (a, sequent') = f (ctxt, sequent)
            in (false, [Future.value a], sequent') end)
    else
      (case scope of
         All_At_Once =>
           let
             (* Promise G_1 &&& ... &&& G_n and NEVER the conclusion: in this
                system the conclusion almost always carries schematics, which the
                kernel rejects when the promise is generalised.

                Both sides are beta-eta contracted, symmetrically.  Contracting
                only the extracted G_i would break Thm.implies_elim, whose match
                is alpha-only.  Doing eta as well as beta turns a property that
                otherwise depends on which rules happened to fire into a
                structural one. *)
             val norm = map (fn ct => Thm.cterm_of ctxt
                                        (Envir.beta_eta_contract (Thm.term_of ct))) cprems
             val conj = Conjunction.mk_conjunction_balanced norm
             (* G_1 ==> ... ==> G_n ==> #(G_1 &&& ... &&& G_n); same shape as
                Minilang's merge_goal_states, which runs this in production *)
             val goal_state =
                   Conjunction.intr_balanced (map Thm.assume norm)
                     |> Goal.protect 0
                     |> fold_rev Thm.implies_intr norm
             val (fut, proved) = fork_state ctxt f (conj, goal_state)
             val parts = Conjunction.elim_balanced nprems proved
             val sequent' =
                   fold2 (fn cprem => fn part => fn seq =>
                            Thm.implies_elim seq
                              (Thm.equal_elim
                                 (Thm.symmetric (Drule.beta_eta_conversion cprem)) part))
                         cprems parts sequent
            in (true, [fut], sequent') end
       | _ =>
           let val (futs, sequent') =
                 fold (fn cprem => fn (acc, seq) =>
                        let val (fut, th) = fork_state ctxt f (cprem, Goal.init cprem)
                         in (fut :: acc, Thm.implies_elim seq th) end)
                      targets ([], sequent)
            in (true, rev futs, sequent') end))
  end

end

fun find_local_may_false ctxt =
  let
    val local_facts = Proof_Context.facts_of ctxt
    val outer_facts = try Local_Theory.target_of ctxt
                   |> Option.map Proof_Context.facts_of
                   |> the_list
  in
    Facts.dest_static false outer_facts local_facts
    |> filter (fn ("local.this", _) => false | _ => true)
    |> get_first (fn (name0, ths) =>
         get_first (fn th =>
           let val th' = Thm.transfer' ctxt th
           in if may_entail_false (Thm.prop_of th')
              then SOME (Facts.extern ctxt local_facts name0, th')
              else NONE
           end) ths)
  end

(* Carries the search unit's (elapsed, proof text) pair through, prefixing the
   text where it had to insert a locally-false fact first. *)
fun wrapper f (ctxt,sequent) =
  if Thm.no_prems sequent
  (* "-" says "nothing to do, nothing to replay"; it is not a placeholder. *)
  then ((Time.zeroTime, "-"), sequent)
  else case Thm.major_prem_of sequent
    of Const (\<^const_name>\<open>Trueprop\<close>, _) $ \<^const>\<open>True\<close> =>
            ((Time.zeroTime, "rule TrueI"), @{thm TrueI} RS sequent)
     | _ => if getenv "DEBUG_DISABLE_SH" = "yes"
            then error "Proof fails and Sledgehammer is disable due to debugging"
            else
              let val (sequent', insert_prefix) =
                    case find_local_may_false ctxt of
                      SOME (name, th) =>
                        (case Seq.pull (Method.insert_tac ctxt [th] 1 sequent) of
                           SOME (s', _) =>
                             (s', "insert " ^ Phi_Help.quote_fact name ^ ", ")
                         | NONE => (sequent, ""))
                    | NONE => (sequent, "")
                  val ((time, prf), result) = f (ctxt, sequent')
              in ((time, insert_prefix ^ prf), result) end


fun funpow' (0: int) _ x = x
  | funpow' n f x = funpow' (n - 1) f (f n x)

fun trim_makrup msg =
  let fun auto _ [] = []
        | auto acc (#"\005" :: L) = auto (not acc) L
        | auto true (#"\127" :: L) = auto true L
        | auto true (x :: L) = x :: auto true L
        | auto false (_ :: L) = auto false L
   in String.implode (auto true (String.explode msg))
  end


fun restore_interval (Facts.FromTo (i,j)) = string_of_int i ^ "-" ^ string_of_int j
  | restore_interval (Facts.From i) = string_of_int i ^ "-"
  | restore_interval (Facts.Single i) = string_of_int i
fun restore_ref (Facts.Named ((name,_), NONE)) = Phi_Help.quote_fact name
  | restore_ref (Facts.Named ((name,_), SOME ivs)) =
      Phi_Help.quote_fact name ^ "(" ^ String.concatWith "," (map restore_interval ivs) ^ ")"
  | restore_ref (Facts.Fact expr) = "\<open>" ^ trim_makrup expr ^ "\<close>"
fun restore_ref' (rf, []) = restore_ref rf
  | restore_ref' (rf, attrs) =
      restore_ref rf ^ "[" ^
          space_implode "," (map (fn attr => space_implode " " (map Token.unparse attr)) attrs)
        ^ "]"

val iv_ord = int_ord o apply2 (fn Facts.FromTo (i,_) => i
                                | Facts.From i => i
                                | Facts.Single i => i)
local open Facts
fun collapse_iv' (From i :: _) = [From i]
  | collapse_iv' ((X as FromTo (i,j)) :: (LL as FromTo(k,l) :: L)) =
      if k <= j     then collapse_iv' (FromTo (i,l) :: L)
      else if j+1=k then collapse_iv' (FromTo (i,l) :: L)
                    else X :: collapse_iv' LL
  | collapse_iv' ((X as FromTo (i,j)) :: (LL as Single k :: L)) =
      if k <= j     then collapse_iv' (FromTo (i,j) :: L)
      else if j+1=k then collapse_iv' (FromTo (i,k) :: L)
                    else X :: collapse_iv' LL
  | collapse_iv' ((X as Single i) :: (LL as FromTo(k,l) :: L)) =
      if k <= i     then collapse_iv' (FromTo (k,l) :: L)
      else if i+1=k then collapse_iv' (FromTo (i,l) :: L)
                    else X :: collapse_iv' LL
  | collapse_iv' ((X as Single i) :: (LL as Single k :: L)) =
      if k = i      then collapse_iv' (Single k :: L)
      else if i+1=k then collapse_iv' (FromTo (i,k) :: L)
                    else X :: collapse_iv' LL
  | collapse_iv' L = L
fun collapse_iv L = collapse_iv' (sort iv_ord L)
fun merge_iv (SOME a) (SOME b) = SOME (a @ b)
  | merge_iv NONE (SOME x) = SOME x
  | merge_iv (SOME x) NONE = SOME x
  | merge_iv NONE NONE = NONE
fun merge_facts' ((x1 as (Named ((s1,p1),iv1), att1)) :: (L2 as (Named ((s2,p2),iv2), att2) :: L))
      = if s1 = s2 andalso pointer_eq (att1, att2)
        then merge_facts' ((Named ((s1,p1), merge_iv iv1 iv2), att1) :: L)
        else x1 :: merge_facts' L2
  | merge_facts' L = L
in
val collapse_iv = collapse_iv
fun fact_ord (Named ((s1,_),iv1), Named ((s2,_),iv2)) =
      prod_ord string_ord (option_ord (list_ord iv_ord)) ((s1,iv1), (s2,iv2))
  | fact_ord (Named _, Fact _) = GREATER
  | fact_ord (Fact _, Named _) = LESS
  | fact_ord (Fact s1, Fact s2) = string_ord (s1, s2)

fun merge_facts ctxt facts =
         facts
      |> sort (fact_ord o apply2 fst)
      |> merge_facts'
      |> map (apfst (fn Named (name, SOME iv) =>
                          let val iv' = collapse_iv iv
                                     |> (fn X as [FromTo (1,n)] =>
                                           (( if n = length (Proof_Context.get_thms ctxt (fst name))
                                              then NONE
                                              else SOME X )
                                              handle ERROR _ => SOME X )
                                          | X => SOME X)
                           in Named (name, iv')
                          end
                      | X => X))
end


(** MePo-guided fastforce **)

fun facts_as_mepo_lazy_facts local_only ctxt =
  let
    val transfer = Thm.transfer' ctxt
    val local_facts = Proof_Context.facts_of ctxt
    val outer_facts =
      if local_only
      then try Local_Theory.target_of ctxt
           |> Option.map Proof_Context.facts_of |> the_list
      else []
    val named_locals = Facts.dest_static false outer_facts local_facts
                    |> filter (fn ("local.this", _) => false | _ => true)
  in
    maps (fn (name0, ths) =>
      let val n = length ths
          val extern_name = Facts.extern ctxt local_facts name0
      in map_index (fn (j, th0) =>
        let
          val th = transfer th0
          val get_name = fn () =>
            if name0 = "" then Sledgehammer_Fact.cartouche_thm ctxt th
            else if n > 1 then extern_name ^ "(" ^ string_of_int (j + 1) ^ ")"
            else extern_name
          val stature = (ATP_Problem_Generate.Local, ATP_Problem_Generate.General)
        in ((get_name, stature), th) : Sledgehammer_Fact.lazy_fact
        end
      ) ths end
    ) named_locals
    |> filter_out (fn (_, th) => is_of_class_thm th)  (* drop OFCLASS lemmas *)
  end

local

val mepo_dummy_params = {
  debug = false, verbose = false, overlord = false, spy = false,
  provers = [], abduce = NONE, falsify = NONE, type_enc = NONE,
  strict = false, lam_trans = NONE, uncurried_aliases = NONE,
  learn = false, fact_filter = NONE, induction_rules = NONE,
  max_facts = NONE, fact_thresholds = (0.45, 0.85),
  max_mono_iters = NONE, max_new_mono_instances = NONE,
  max_proofs = 1, isar_proofs = NONE, compress = NONE,
  try0 = false, smt_proofs = false, instantiate = NONE, minimize = false,
  slices = 1, timeout = Time.fromSeconds 5,
  preplay_timeout = Time.fromSeconds 1, expect = "", cache_dir = NONE
} : Sledgehammer_Prover.params

(* Render the cached Isar method string from MePo's selection.
   to_insert / to_add are (name_string, thm) pairs. The name strings produced
   by `facts_as_mepo_lazy_facts`'s `get_name ()` are already valid Isar
   fact references in all three shapes it can produce:
     - "name"           — singleton bundle
     - "name(N)"        — j-th member of an N-member bundle (valid Isar selector)
     - "\<open>...\<close>" — cartouche-by-content for anonymous facts
   and the cartouche content is pre-stripped of YXML markup by
   `hackish_string_of_term` inside `Sledgehammer_Fact.cartouche_thm`. So we
   can splice the name strings directly into the generated method text. *)
fun render_fast_mepo_proof to_insert to_add del_pairs =
  let
    val ithm = if null to_insert then ""
               else "insert " ^ space_implode " " (map fst to_insert) ^ ", "
    fun clause label ty pairs =
          map_filter (fn (name, th) =>
            if infer_type_of_rule name th = ty then SOME name else NONE) pairs
       |> (fn [] => ""
            | L => " " ^ label ^ ": " ^ space_implode " " L)
    val simps  = clause "simp"  T_SIMP  to_add
    val unkns  = clause "simp"  T_UNKNOWN to_add
    val intros = clause "intro" T_INTRO to_add
    val elims  = clause "elim"  T_ELIM  to_add
    val dests  = clause "dest"  T_DEST  to_add
    val congs  = clause "cong"  T_CONG  to_add
    val splits = clause "split" T_SPLIT to_add
    val iffs   = clause "iff"   T_IFF   to_add
    val dsimps  = clause "simp del"  T_SIMP  del_pairs
    val dcongs  = clause "cong del"  T_CONG  del_pairs
    val dsplits = clause "split del" T_SPLIT del_pairs
    val diffs   = clause "iff del"   T_IFF   del_pairs
    val del_gen = map_filter (fn (name, th) =>
        let val ty = infer_type_of_rule name th
        in if ty = T_INTRO orelse ty = T_ELIM orelse ty = T_DEST orelse ty = T_UNKNOWN
           then SOME name else NONE end) del_pairs
      |> (fn [] => "" | L => " del: " ^ space_implode " " L)
  in
    String.concat ["(", ithm, "fastforce del: disjCI insertCI intro: disjCI insertCI",
                   simps, unkns, intros, elims, dests,
                   congs, splits, iffs, dsimps, dcongs, dsplits, diffs, del_gen, ")"]
  end

in

(* Run MePo + fastforce on the i-th subgoal. On success returns the proved
   sequent, the rendered Isar replay string, and the fastforce-only elapsed
   time (NOT including MePo selection time, since the cache replay only
   re-runs fastforce, not MePo). On failure raises Auto_Fail.
   lazy_facts: pool for MePo selection (empty = skip MePo).
   extra_pairs: user-provided (name, thm) pairs always included.
   del_pairs: user-provided del facts applied to base context. *)
fun run_mepo_and_render timeout max_facts lazy_facts extra_pairs del_pairs ctxt i st =
  let
    (* A MePo suggestion that cannot be turned into a rule is SKIPPED, not fatal:
       Thm.apply_attribute raises THM (e.g. Simpdata.mk_eq's RS Eq_TrueI on an
       OFCLASS conclusion) as readily as TERM, and one unusable fact must not
       take the whole fastforce branch down. *)
    val ctxt = fold (fn (name, th) => fn c =>
      (with_rule false name th (Context.Proof c) |> Context.proof_of)
      handle TERM _ => c | THM _ => c) del_pairs ctxt

    val mepo_pairs =
      if null lazy_facts then []
      else
        let
          val goal_term = Logic.get_goal (Thm.prop_of st) i
          val hyp_ts = Logic.strip_assums_hyp goal_term
          val concl_t = Logic.strip_assums_concl goal_term
          val selected = Sledgehammer_MePo.mepo_suggested_facts
                           ctxt mepo_dummy_params max_facts NONE hyp_ts concl_t lazy_facts
          val selected = if null selected
                         then map Sledgehammer_Fact.fact_of_lazy_fact lazy_facts
                         else selected
        in map (fn ((name, _), th) => (name, th)) selected end

    val all_pairs =
      let val extra_thms = map snd extra_pairs
          fun is_extra th = exists (fn e => Thm.eq_thm_prop (th, e)) extra_thms
      in filter (fn (_, th) => not (is_extra th)) mepo_pairs @ extra_pairs end

    val (safe_pairs, ctxt) =
      Looping_Simp.pass_looping_simps
        {only_check_local = false, ignore_cond = false, local_ignore_cond = false,
         schematize_local_frees = false}
        ctxt all_pairs
    val sbi = should_be_inserted ctxt
    val (to_insert, to_add) =
      fold_rev (fn (name, th) => fn (ins, add) =>
        if sbi (Thm.prop_of th)
        then ((name, th) :: ins, add)
        else (ins, (name, th) :: add)
      ) safe_pairs ([], [])

    val ctxt' = Context.Proof ctxt
      |> (fn gc => Thm.apply_attribute Classical.rule_del @{thm disjCI} gc |> snd)
      |> (fn gc => Thm.apply_attribute Classical.rule_del @{thm insertCI} gc |> snd)
      |> (fn gc => Thm.apply_attribute (Classical.unsafe_intro NONE) @{thm disjCI} gc |> snd)
      |> (fn gc => Thm.apply_attribute (Classical.unsafe_intro NONE) @{thm insertCI} gc |> snd)
      |> Context.proof_of

    val ctxt' = fold (fn (name, th) => fn c =>
      (with_rule true name th (Context.Proof c) |> Context.proof_of)
      handle TERM _ => c | THM _ => c
    ) to_add ctxt'

    val insert_thms = map snd to_insert

    fun fastforce_branch () =
      (Method.insert_tac ctxt insert_thms i THEN Clasimp.fast_force_tac ctxt' i) st

    val start = Time.now ()
  in
    case Timeout.apply timeout (fn () => Seq.pull (fastforce_branch ())) ()
              handle Timeout.TIMEOUT _ => NONE
                   | TERM _ => NONE of
      NONE => raise Auto_Fail Application_Fails
    | SOME (st', _) =>
        let val elapsed = Time.- (Time.now (), start)
            val prf_str = render_fast_mepo_proof to_insert to_add del_pairs
        in (st', prf_str, elapsed) end
  end

(* Replay a cached Isar method on the i-th subgoal of `st`. For i = 1 we just
   call eval_prf_str directly; for i > 1 we wrap with Goal.restrict / unrestrict
   so the cached "(insert ..., fastforce ...)" string (which acts on subgoal 1
   of whatever sequent it sees) lands on the right subgoal. *)
fun replay_mepo_proof kws timeout i prf (ctxt, st) =
  if i = 1 then
    let val (_, cs) = eval_prf_str kws 1 timeout prf (ctxt, st) in cs end
  else
    let
      val st_focused = Goal.restrict i 1 st
      val (_, (ctxt', st_focused')) =
            eval_prf_str kws 1 timeout prf (ctxt, st_focused)
    in
      (ctxt', Goal.unrestrict i st_focused')
    end

fun fast_mepo_tac timeout ctxt i st =
  if Thm.nprems_of st < i then Seq.empty
  else
    let val max_facts = Config.get ctxt fast_mepo_max_facts
        val lazy_facts = facts_as_mepo_lazy_facts true ctxt
        fun run () = run_mepo_and_render timeout max_facts lazy_facts [] [] ctxt i st
    in if not (Config.get ctxt Phi_Proof_Store.enable_proof_store) then
      ((case run () of (st', _, _) => Seq.single st')
       handle Auto_Fail _ => Seq.empty
            | Timeout.TIMEOUT _ => Seq.empty)
    else
      let
        val thy = Proof_Context.theory_of ctxt
        val kws = Keyword.no_major_keywords (Thy_Header.get_keywords thy)

        fun evaluator t prf cs =
              SOME (replay_mepo_proof kws t i prf cs)
              handle Auto_Fail _ => NONE
                   | Timeout.TIMEOUT _ => NONE

        fun fallback _ =
              let val (st', prf_str, elapsed) = run ()
               in ((elapsed, prf_str), (ctxt, st')) end
      in
        ((case Phi_Proof_Store.try_cached_proof_by_hash_at i evaluator fallback (ctxt, st) of
            (_, (_, st')) => Seq.single st')
         handle Auto_Fail _ => Seq.empty
              | Timeout.TIMEOUT _ => Seq.empty)
      end
    end

end


fun sledgehammer timeout_opt improved hasty kws override0 (ctxt,sequent) =
  let val (goal_term,_) = Logic.dest_implies (Thm.prop_of sequent)

      val failed_subgoal = Unsynchronized.ref (NONE : term option)

      val pass_thms  = filter (can (Attrib.eval_thms ctxt) o single)
      val pass_thms' = map_filter (fn th => try (rpair th o Attrib.eval_thms ctxt) [th])
      (* silently discard user-supplied OFCLASS lemmas at this entry point *)
      val drop_of_class =
        filter_out (fn (ths, _) => not (null ths) andalso List.all is_of_class_thm ths)
      val origin_add = drop_of_class (pass_thms' (#add override0))
      val origin_del = drop_of_class (pass_thms' (#del override0))

      val sbi = should_be_inserted ctxt
      val (ithms, sthms, OA) = fold_rev (fn (th', th) => fn (I,S,OA) =>
            if exists (sbi o Thm.prop_of) th'
            then (restore_ref' th :: I, S, OA)
            else (I, restore_ref' th :: S, (th', th) :: OA)
          ) origin_add ([],[],[])
      val ithm = if null ithms then "" else "insert " ^ space_implode " " ithms ^ ", "
      (* The user-declared \<phi>sledgehammer_simps join the simp set of the
         parallel classical branches.  Naming the bundle rather than splicing its
         members keeps the reference late-bound and costs nothing when empty. *)
      val sthm = " \<phi>sledgehammer_simps" ^
                 (if null sthms then "" else " " ^ space_implode " " sthms)
      val dthm = if null origin_del then ""
                 else " simp del: " ^ space_implode " " (map (restore_ref' o snd) origin_del)
      val athms = space_implode " " (map (restore_ref' o snd) origin_add)

      val override = {add=map snd OA, del = map snd origin_del, only = #only override0}
      val raw_override = {add = map snd origin_add, del = map snd origin_del, only = #only override0}

      val need_standard = need_standard_tac ctxt sequent

      val stat = Proof.theorem NONE (K I) [[(goal_term, [])]] ctxt
                 |> Proof.refine_primitive Pre_Simproc.pre_simproc_on_concl

      fun eval_prf_strs_stat [] _ = raise Auto_Fail Application_Fails
        | eval_prf_strs_stat [prf] stat = eval_prf_str_stat kws 30 NONE prf stat
        | eval_prf_strs_stat prfs stat =
            case Par_List.get_some (fn prf =>
                    SOME (eval_prf_str_stat kws 30 NONE prf stat)
                    handle Auto_Fail _ => NONE
                 ) prfs
              of SOME ret => ret
               | NONE => raise Auto_Fail Application_Fails

      fun hammer override (prf0,stat0) =
        let
          val N = Thm.nprems_of (#goal (Proof.raw_goal stat0))
          val Ns = string_of_int N

          val _ = if N > 30 then (sh_log ("The prompt generates too many subgoals (" ^
                                    string_of_int N ^ "). give up...");
                                  raise Auto_Fail Too_Many_Subgoals)
                            else ()

          val iter_timeout = Option.map (fn t => t + Time.fromSeconds 120) timeout_opt

          val (prfs, final_state) =
            funpow' N (fn j => fn (ps,s) =>
                        let val _ = sh_log ("Sledgehammering on the " ^ string_of_int (N+1-j) ^
                                             "th goal (total " ^ Ns ^ ")")
                            fun do_iter () =
                            case raw_sledgehammer timeout_opt override hasty s
                                            of NONE =>
                                  let val subgoal_raw = hd (Thm.prems_of (#goal (Proof.raw_goal s)))
                                      val params = Logic.strip_params subgoal_raw
                                      val hyps = Logic.strip_assums_hyp subgoal_raw
                                      val concl = Logic.strip_assums_concl subgoal_raw
                                      val concl0 = Logic.strip_assums_concl goal_term
                                      val _ = if not (concl aconv concl0)
                                        then (let
                                               val (hyps', concl') =
                                                 case (concl, hyps)
                                                   of (Const(\<^const_name>\<open>Trueprop\<close>, _)
                                                         $ Const(\<^const_name>\<open>False\<close>, _),
                                                       _ :: _) =>
                                                        (case List.last hyps
                                                           of Const(\<^const_name>\<open>Trueprop\<close>, _) $ A =>
                                                                (List.take (hyps, length hyps - 1),
                                                                 HOLogic.mk_Trueprop
                                                                   (HOLogic.mk_not A))
                                                            | _ => (hyps, concl))
                                                    | _ => (hyps, concl)
                                               fun close body =
                                                 fold_rev (fn (n, T) => fn b =>
                                                     Logic.all_const T $ Abs (n, T, b))
                                                   params body
                                               val whole =
                                                 Object_Logic.atomize_term ctxt
                                                   (close (Logic.list_implies (hyps', concl')))
                                               val concl_only =
                                                 Object_Logic.atomize_term ctxt (close concl')
                                          in case List.find (fn t => smart_size_of_term t <= 50)
                                                               [whole, concl_only]
                                               of SOME t => failed_subgoal := SOME t
                                                | NONE => ()
                                         end
                                        (* Object_Logic.atomize_term raises TERM on
                                           shapes it cannot atomize; that only costs
                                           us the nicer diagnostic, and the verdict
                                           below is the same either way. *)
                                        handle TERM _ => ())
                                        else ()
                                   in raise Auto_Fail Application_Fails
                                  end
                               | SOME prf => prf
                            (* this TIMEOUT used to escape bare, straight past every
                               caller that only knows the engine's own vocabulary *)
                            val (p',s') = (case iter_timeout
                                  of SOME t => Timeout.apply t do_iter ()
                                   | NONE => do_iter ())
                                  handle Timeout.TIMEOUT _ => raise Auto_Fail Timeout
                         in (p'::ps, s') end)
                     ((if prf0 = "" then [] else [prf0]),stat0)
    
          val prf = "(" ^ String.concatWith ",\n" (rev prfs) ^ ")"
        in (prf, #goal (Proof.goal final_state))
       end

      fun hammer' () =
        let val src1 = if need_standard
                       then "standard, " ^ ithm ^ "auto_split simp: "^ sthm ^ dthm
                       else ithm ^ "auto_split simp: "^ sthm ^ dthm
            val src2 = if need_standard
                       then "standard, " ^ ithm ^ "clarsimp_split simp: "^ sthm ^ dthm
                       else ithm ^ "clarsimp_split simp: "^ sthm ^ dthm
            fun auto () = SOME (eval_prf_str_stat kws 5 NONE src1 stat)
                          handle Auto_Fail _ => NONE
            fun clar () = SOME (eval_prf_str_stat kws 4 NONE src2 stat)
                          handle Auto_Fail _ => NONE
            val [r1, r2] = Par_List.map (fn f => f()) [auto, clar]
         in case r1
              of SOME r => hammer override r
               | NONE => (case r2
                   of SOME r => hammer override r
                    | NONE => raise Auto_Fail Application_Fails)
        end

      fun bare_hammer () =
          hammer raw_override ("-", stat)

      fun expand_fact_refs origin =
        let
          fun nth_iv' i (Facts.FromTo (j,k) :: L) =
                if i < k-j+1 then SOME [Facts.Single (j+i)]
                else nth_iv' (i - (k-j+1)) L
            | nth_iv' i [Facts.From j] = SOME [Facts.Single (j+i)]
            | nth_iv' i (Facts.Single j :: L) = nth_iv' i (Facts.FromTo (j,j) :: L)
            | nth_iv' _ _ = NONE
          fun nth_iv N i iv =
            if i + 1 = N then NONE
            else case iv
              of NONE => SOME [Facts.Single (i+1)]
               | SOME ivs => ivs |> sort iv_ord |> nth_iv' i
        in
          maps (fn (ths, (Facts.Named ((name, pos), iv), atts)) =>
              let val N = length ths
              in map_index (fn (i, th) =>
                  (restore_ref' (Facts.Named ((name, pos), nth_iv N i iv), atts), th)
                ) ths
              end
            | ([th], (fact_ref, atts)) => [(restore_ref' (fact_ref, atts), th)]
            | _ => []) origin
        end

      fun fastforce () =
        let
          val ctxt = Proof.context_of stat
          val st = #goal (Proof.goal stat)

          val user_add = expand_fact_refs origin_add
          val user_del = expand_fact_refs origin_del

          val local_lazy = facts_as_mepo_lazy_facts true ctxt
          val all_lazy = Lazy.lazy (fn () => facts_as_mepo_lazy_facts false ctxt)

          fun try_stage timeout max_mf lazy_facts =
            let val (st', prf_str, _) =
                  run_mepo_and_render (Time.fromSeconds timeout)
                    max_mf lazy_facts user_add user_del ctxt 1 st
            in SOME (prf_str, st') end
            handle Auto_Fail _ => NONE | Timeout.TIMEOUT _ => NONE
        in
          case try_stage 6  0  []
           of SOME r => r | NONE =>
          case try_stage 10 12 local_lazy
           of SOME r => r | NONE =>
          case try_stage 15 24 (Lazy.force all_lazy)
           of SOME r => r | NONE =>
          case try_stage 15 50 (Lazy.force all_lazy)
           of SOME r => r | NONE =>
          raise Auto_Fail Application_Fails
        end

      fun smt () =
        let val src = "(smt " ^ athms ^ ")"
         in eval_prf_str_stat kws 5 NONE src stat
         |> apsnd (#goal o Proof.goal)
        end

      (* Ground-evaluation backend: if the goal is variable-free, try to close
         it by code evaluation (the same oracle AoA's Compute uses).  The
         oracle itself rejects non-ground / non-executable goals, so this fails
         fast and cheaply otherwise. *)
      fun ground () =
        let val src = "ground_eval"
         in eval_prf_str_stat kws 5 NONE src stat
         |> apsnd (#goal o Proof.goal)
        end

      fun simp () =
        let val src = "(insert " ^ athms ^ ", simp)"
            val n0 = Thm.nprems_of (#goal (Proof.goal stat))
            val (ret, s') = eval_prf_str_stat kws 5 NONE src stat
         in if Thm.nprems_of (#goal (Proof.goal s')) + 1 = n0
          then (ret, #goal (Proof.goal s'))
          else raise Auto_Fail Application_Fails
        end

      (* The ONLY place the normaliser is installed: the exits of the search
         branches.  Anything that escapes a branch becomes engine vocabulary
         here, so a stray TIMEOUT / THM / TERM makes us try the next branch
         instead of blowing past every caller.  An Internal_Failure is a bug and
         goes straight up with its payload -- swallowing it would leave the user
         staring at "could not prove the goal" for, say, a typo in
         auto_sledgehammer_params. *)
      fun run_branch F =
        case Exn.capture_body F of
          Exn.Res r => SOME r
        | Exn.Exn exn =>
            (case Exn.capture_body (fn () => normalise exn) of
               Exn.Res _ => NONE                       (*unreachable: normalise always raises*)
             | Exn.Exn (Auto_Fail (Internal_Failure msg)) =>
                 raise Auto_Fail (Internal_Failure msg)
             | Exn.Exn (Auto_Fail _) => NONE
             | Exn.Exn e => Exn.reraise e)

      val prf = if improved
        then Par_List.get_some run_branch [
            ground,
            hammer',
            bare_hammer,
            fastforce,
            simp,
            smt
          ]
        else run_branch bare_hammer

   in case prf
   of SOME (prf, sequent') =>
        if hasty
        then ((Time.zeroTime, "<cheat>"), (ctxt, sequent'))
        else let val composed = "Auto_Sledgehammer.pre_simproc_on_concl, " ^ prf
                 val _ = sh_log ("[sledgehammer] verifying composed proof: " ^ quote composed)
              in eval_prf_str kws 1 (Time.fromSeconds 180) composed (ctxt,sequent)
             end
    | NONE => (case !failed_subgoal
                 of SOME t => raise Auto_Fail (Subgoal_Fail t)
                  | NONE => raise Auto_Fail Application_Fails)
  end


(* The PRIVATE pure-search unit.  It has no notion of a proof store at all: no
   key, no lookup, no write-back, no switches.  All of that sits one layer up in
   auto / all_auto, where a call computes its key exactly once.

   Its shape is fixed by async_prove, which drives it:
     Proof.context * thm -> (Time.time * string) * thm.
   The elapsed time HAS to come out -- the caching layer records it, and the old
   code simply threw it away. *)
fun auto'i {improved, fact_override, timeout} (ctxt, sequent) =
  let
    val hasty = Config.get ctxt hasty_mode
    val kws = Keyword.no_major_keywords (
                      Thy_Header.get_keywords (Proof_Context.theory_of ctxt))
   (* val classical_timeout = Config.get ctxt classical_prover_timeout *)
    val found =
     ((* case Timeout.apply (Time.fromSeconds classical_timeout) (Timing.timing Seq.pull)
                            (auto_obligation_solver (ctxt, sequent))
        of ({elapsed=time,...}, SOME (sequent', _)) =>
            ((time,""), (ctxt, sequent'))
         | _ => (
            tracing "Proof search by default tactic fails. Invoking sledgehammer..."; *)
            sledgehammer timeout improved hasty kws fact_override (ctxt, sequent) )
      handle Timeout.TIMEOUT _ => (
        sh_log "Proof search by default tactic times out. Invoking sledgehammer...";
        sledgehammer timeout improved hasty kws fact_override (ctxt, sequent) )
  in
    apsnd snd found   (*async_prove's `f` yields 'a * thm; drop the context*)
  end
(* val proof = raw_sledgehammer stat *)

type options = {improved      : bool,
                async         : bool,
                fact_override : Sledgehammer.fact_override,
                proof_id      : Phi_Proof_Store.proof_id option,
                timeout       : Time.time option,
                read_store    : bool option,
                write_store   : bool option,
                raise_Error_instead_of_Auto_Fail : bool}

local

(*NONE = follow the enable_proof_store config, i.e. behave exactly as this
  module did before the switch existed.*)
fun store_flag ctxt NONE = Config.get ctxt Phi_Proof_Store.enable_proof_store
  | store_flag _ (SOME b) = b

(*A timeout override reaches Sledgehammer through its own parameter string.*)
fun with_timeout NONE ctxt = ctxt
  | with_timeout (SOME t) ctxt =
      Config.map sledgehammer_params
        (fn s => "timeout = " ^ string_of_int (Time.toSeconds t)
                 ^ (if s = "" then "" else ", " ^ s)) ctxt

(*true converts Auto_Fail into a fatal ERROR, for the Isar methods.
  Internal_Failure gets its own arm: its payload is the entire reason the
  constructor exists, and the generic "Fail to prove the goal" would eat it.
  The hand-rolled Par_Exn.dest paragraph that used to live here is gone -- the
  branch exits now normalise everything into Auto_Fail.*)
fun guard_errors false _ _ body = body ()
  | guard_errors true ctxt sequent body =
      body ()
      handle Auto_Fail (Internal_Failure msg) => error msg
           | Auto_Fail _ => error (error_message ctxt sequent)

(*Run `g` once the by-products are in.  Already fulfilled (the synchronous case)
  means running it NOW, before we return, so a synchronous call still records
  before it hands control back; otherwise it becomes a dependent task.  Either
  way the caller gets one future of the same shape, and the recording code is
  written once.  This is the one dependent task that is allowed to join.*)
fun after futs g =
  if forall Future.is_finished futs
  then Future.value (g (Future.joins futs))
  else singleton (Future.forks {name = "\<phi>SH.record_proof", group = NONE,
                                deps = map Future.task_of futs, pri = 0,
                                interrupts = false})
         (fn () => g (Future.joins futs))

(*Proof texts are stored with their own scope.  `[n]` is the real Isar combinator
  Select_Goals, so the record says for itself which goals it speaks for instead
  of depending on the reader to arrange the state.  It only attaches to a bare
  method name or a PARENTHESISED group -- `auto [1]` parses as an argument to
  auto -- hence the parentheses.*)
fun scoped prf = "(" ^ prf ^ ")[1]"

in

fun auto (opts : options) ctxt0 sequent =
  (* Zero subgoals returns before anything else happens: no key (goal_at 1 would
     raise), no lookup, no record, no fork.  "-" means "nothing to do, nothing to
     replay". *)
  if Thm.no_prems sequent then (Future.value "-", sequent)
  else
  let
    val ctxt = with_timeout (#timeout opts) ctxt0
    val thy = Proof_Context.theory_of ctxt
    val kws = Keyword.no_major_keywords (Thy_Header.get_keywords thy)
    val hasty = Config.get ctxt hasty_mode
    val nprem = Thm.nprems_of sequent
    (* single-goal entry => key on the LEADING subgoal alone.  Hashing the whole
       proposition would move the key when the conclusion is replaced by a
       promise, so one obligation would key differently sync vs async. *)
    val hash = Hasher.goal_at 1 (ctxt, sequent)
    val id = case #proof_id opts of SOME s => s | NONE => hash
    val do_read = store_flag ctxt (#read_store opts)
    val do_write = store_flag ctxt (#write_store opts)

    (*The log line is deliberately NOT gated on write_store: it reports what the
      search found, which is worth knowing whether or not we keep it.*)
    fun record (time, prf) =
      (sh_log ("Find proof (" ^ id ^ ", time: " ^ Time.toString time ^ "): \n" ^ prf);
       if do_write andalso not hasty
       then let val t = Phi_Proof_Store.standard_time time in
              Phi_Proof_Store.update_hash_cache hash (t, prf);
              Phi_Proof_Store.update_cached_proof thy (id, (t, prf))
            end
       else ())

    fun search () =
      let val (_, futs, sequent') =
            async_prove (#async opts) Leading
              (wrapper (auto'i {improved = #improved opts,
                                fact_override = #fact_override opts,
                                timeout = #timeout opts}))
              (ctxt, sequent)
          val out = after futs (fn [(time, prf)] =>
                                   let val text = scoped prf
                                    in record (time, text); text end
                                 | _ => raise Fail "auto: async_prove Leading \
                                                   \yielded the wrong shape")
          val _ = if Future.is_finished out then ()
                  else Phi_Proof_Store.register_async_task (Future.task_of out) thy
       in (out, sequent') end
  in
    guard_errors (#raise_Error_instead_of_Auto_Fail opts) ctxt sequent (fn () =>
    let
      (*Level 1 -- the on-disk store, keyed by proof id.  A hit that still
        replays is handed back as it stands; nothing is written.*)
      val (stale, hit) =
        if not do_read then (false, NONE)
        else case Phi_Proof_Store.get_cached_proof thy id of
          NONE => (sh_log ("[auto] store MISS for id " ^ quote id); (false, NONE))
        | SOME (time, prf) =>
           (sh_log ("[auto] store HIT for id " ^ quote id ^ ", replaying: " ^ quote prf);
            (case eval_prf_str kws 1 (Phi_Proof_Store.tolerant_time time) prf (ctxt, sequent) of
               (_, (_, sequent')) =>
                 if Thm.nprems_of sequent' < nprem
                 then (sh_log "[auto] store replay OK"; (false, SOME (prf, sequent')))
                 else raise Auto_Fail Subgoal_unsolved)
            handle Auto_Fail _ =>
              (sh_log "[auto] store replay FAILED, re-searching"; (true, NONE)))

      (*Level 2 -- the in-process table, keyed by the goal hash and never written
        to disk on its own.  A hit here IS recorded, which promotes it into the
        store under THIS call's proof id.  Finding an entry marks the situation
        stale either way: a stored id entry that we are about to supersede.*)
      val (stale, replayed) =
        if is_some hit orelse not do_read then (stale, NONE)
        else case Phi_Proof_Store.access_hash_cache hash of
          NONE => (stale, NONE)
        | SOME (t, prf) =>
            (true,
             SOME (eval_prf_str kws 1 (Phi_Proof_Store.tolerant_time t) prf (ctxt, sequent))
             handle Auto_Fail _ => NONE)
    in
      case hit of
        SOME (prf, sequent') => (Future.value prf, sequent')
      | NONE =>
      case replayed of
        SOME ((time, prf), (_, sequent')) => (record (time, prf); (Future.value prf, sequent'))
      | NONE =>
         (if stale
          then (warning "A cached proof fails. Re-searching proofs...";
                (*store self-maintenance: deliberately outside read_store /
                  write_store, and unreachable unless read_store let us hit*)
                Phi_Proof_Store.invalidate_proof_cache true id thy)
          else sh_log ("Proof store miss, " ^ id);
          search ())
    end)
  end

fun all_auto (opts : options) ctxt0 sequent =
  if Thm.no_prems sequent then (Future.value (Time.zeroTime, "-"), sequent)
  else
  let
    val ctxt = with_timeout (#timeout opts) ctxt0
    val thy = Proof_Context.theory_of ctxt
    val kws = Keyword.no_major_keywords (Thy_Header.get_keywords thy)
    val hasty = Config.get ctxt hasty_mode
    val nprem = Thm.nprems_of sequent
    (* multi-goal entry => key on EVERY subgoal at once.  One call, one key, one
       record: the old code reused the caller's single id for all n subgoals, so
       each write overwrote the previous one. *)
    val hash = Hasher.all_goals (ctxt, sequent)
    val id = case #proof_id opts of SOME s => s | NONE => hash
    val do_read = store_flag ctxt (#read_store opts)
    val do_write = store_flag ctxt (#write_store opts)

    fun record (time, prf) =
      (sh_log ("Find proof (" ^ id ^ ", time: " ^ Time.toString time ^ "): \n" ^ prf);
       if do_write andalso not hasty
       then let val t = Phi_Proof_Store.standard_time time in
              Phi_Proof_Store.update_hash_cache hash (t, prf);
              Phi_Proof_Store.update_cached_proof thy (id, (t, prf))
            end
       else ())

    fun search () =
      let val (_, futs, sequent') =
            async_prove (#async opts) Each_Goal
              (wrapper (auto'i {improved = #improved opts,
                                fact_override = #fact_override opts,
                                timeout = #timeout opts}))
              (ctxt, sequent)
          (*n subgoal proofs composed in order; each carries its own scope, so
            replaying the composition does not let the first method run away with
            all the goals.  Empty list cannot occur -- the entry short-circuits on
            zero subgoals -- so no "()" can ever be stored.*)
          val out = after futs (fn tps =>
                       let val time = fold (curry (op +) o fst) tps Time.zeroTime
                           val text = "(" ^ String.concatWith ", "
                                              (map (scoped o snd) tps) ^ ")"
                        in record (time, text); (time, text) end)
          val _ = if Future.is_finished out then ()
                  else Phi_Proof_Store.register_async_task (Future.task_of out) thy
       in (out, sequent') end
  in
    guard_errors (#raise_Error_instead_of_Auto_Fail opts) ctxt sequent (fn () =>
    let
      val (stale, hit) =
        if not do_read then (false, NONE)
        else case Phi_Proof_Store.get_cached_proof thy id of
          NONE => (sh_log ("[all_auto] store MISS for id " ^ quote id); (false, NONE))
        | SOME (time, prf) =>
           (sh_log ("[all_auto] store HIT for id " ^ quote id ^ ", replaying: " ^ quote prf);
            (*protect n, n = the number of goals this text speaks for*)
            (case eval_prf_str kws nprem (Phi_Proof_Store.tolerant_time time) prf (ctxt, sequent) of
               (_, (_, sequent')) =>
                 if Thm.no_prems sequent'
                 then (sh_log "[all_auto] store replay OK"; (false, SOME ((time, prf), sequent')))
                 else raise Auto_Fail Subgoal_unsolved)
            handle Auto_Fail _ =>
              (sh_log "[all_auto] store replay FAILED, re-searching"; (true, NONE)))

      val (stale, replayed) =
        if is_some hit orelse not do_read then (stale, NONE)
        else case Phi_Proof_Store.access_hash_cache hash of
          NONE => (stale, NONE)
        | SOME (t, prf) =>
            (true,
             SOME (eval_prf_str kws nprem (Phi_Proof_Store.tolerant_time t) prf (ctxt, sequent))
             handle Auto_Fail _ => NONE)
    in
      case hit of
        SOME (tp, sequent') => (Future.value tp, sequent')
      | NONE =>
      case replayed of
        SOME (tp, (_, sequent')) => (record tp; (Future.value tp, sequent'))
      | NONE =>
         (if stale
          then (warning "A cached proof fails. Re-searching proofs...";
                Phi_Proof_Store.invalidate_proof_cache true id thy)
          else sh_log ("Proof store miss, " ^ id);
          search ())
    end)
  end

end

fun insert_tac _ [] _ = all_tac
  | insert_tac ctxt facts i =
      EVERY (map (fn r => resolve_tac ctxt [Thm.forall_intr_vars r COMP_INCR revcut_rl] i) facts);

fun not_del parser (toks as (tok1 :: tok2 :: _)) =
      if Token.is_kind Token.Keyword tok2 andalso
         Token.is_kind Token.Ident tok1 andalso
         Token.content_of tok1 = "del" andalso
         Token.content_of tok2 = ":"
      then Scan.fail toks
      else parser toks
  | not_del parser toks = parser toks
  

fun override_parser toks = (
        Scan.repeat (   (Args.add |-- \<^keyword>\<open>:\<close> |-- Scan.repeat (not_del Parse.thm) >> rpair [])
                     || (Args.del |-- \<^keyword>\<open>:\<close> |-- Scan.repeat Parse.thm >>  pair []) )
     >> (fn LL => fold_rev (fn (A,D) => fn (A',D') => (A @ A', D @ D') ) LL ([],[])
               |> (fn (A,D) => {add = A, del = D, only = false})) ) toks

(* The four methods differ only in which entry point they drive and whether the
   improved multi-strategy search is used.  All four take async = false (a method
   has to fail observably, which forking rules out) and
   raise_Error_instead_of_Auto_Fail = true.  The id is computed BEFORE
   insert_tac, exactly as it always was, so `using foo by auto_sledgehammer` does
   not key on foo -- a pre-existing asymmetry, left alone deliberately. *)
fun sledgehammer_method key run improved = Scan.lift (
  override_parser >> (fn override => fn _ =>
  Method.CONTEXT_METHOD (fn uses => fn (ctxt,sequent) => Seq.make (fn () =>
    (* Isar does hand a method a state with no subgoals left, and the key must
       not be computed there: Hasher.goal_at 1 goes through Logic.get_goal, which
       raises outright when the index is out of range.  Nothing to prove, so
       return the state untouched -- which is what the entry point would have
       done anyway, only without raising on the way in. *)
    if Thm.no_prems sequent then SOME (Seq.Result (ctxt, sequent), Seq.empty)
    else
    let val id = key (ctxt, sequent)
        fun err () = error_message ctxt sequent
        val sequent' =
              case Seq.pull (Method.insert_tac ctxt uses 1 sequent)
                of SOME (ret, _) => ret
                 | NONE => error "Why the insert_tac can fail?"
     in SOME (
         (Seq.Result (ctxt, snd (run {improved = improved,
                                      async = false,
                                      fact_override = override,
                                      proof_id = SOME id,
                                      timeout = NONE,
                                      read_store = NONE,
                                      write_store = NONE,
                                      raise_Error_instead_of_Auto_Fail = true}
                                     ctxt sequent'))
          handle Auto_Fail _ => Seq.Error err),
         Seq.empty)
    end))))

val _ = Theory.setup (
Method.setup \<^binding>\<open>auto_sledgehammer\<close>
  (sledgehammer_method (Hasher.goal_at 1) auto true)
  "Apply sledgehammer transparently and record the outcome."
#>
Method.setup \<^binding>\<open>auto_sledgehammers\<close>
  (sledgehammer_method Hasher.all_goals all_auto true)
  "Apply sledgehammer repeatedly to all goals and record the outcome."
#>
Method.setup \<^binding>\<open>raw_sledgehammer\<close>
  (sledgehammer_method (Hasher.goal_at 1) auto false)
  "Apply sledgehammer transparently and record the outcome."
#>
Method.setup \<^binding>\<open>raw_sledgehammers\<close>
  (sledgehammer_method Hasher.all_goals all_auto false)
  "Apply sledgehammer repeated to every goals and record the outcome."
#>
Method.setup \<^binding>\<open>fast_mepo\<close>
  (Scan.lift (Scan.option Parse.nat) -- Method.sections Clasimp.clasimp_modifiers >>
    (fn (timeout_opt, _) =>
      let val timeout = Time.fromSeconds (case timeout_opt of SOME n => n | NONE => 10)
      in SIMPLE_METHOD' o fast_mepo_tac timeout end))
  "fastforce + smt with MePo-guided fact selection from local context"
)

end

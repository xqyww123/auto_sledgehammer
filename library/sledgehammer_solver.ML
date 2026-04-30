signature PHI_SLEDGEHAMMER_SOLVER = sig

val orverride_parser : Sledgehammer.fact_override parser
val auto : bool (*true for using the improved version,  false for the raw sledgehammer*)
        -> Sledgehammer.fact_override
        -> Phi_Cache_DB.proof_id option
        -> Time.time option (*optional timeout override*)
        -> Proof.context -> thm -> string (*proof*) * thm
(*attacks all goals*)
val all_auto : bool (*true for using the improved version,  false for the raw sledgehammer*)
        -> Sledgehammer.fact_override
        -> Phi_Cache_DB.proof_id option
        -> Proof.context -> thm -> string (*proof*) * thm

val assync_proof : bool Config.T

val sledgehammer_params : string Config.T
val classical_prover_timeout : int Config.T
val try_parallel_smt_cvc5 : bool Config.T

(* Exposed for testing: given a raw Sledgehammer proof string (e.g. "by (metis foo bar)"),
   tokenize, strip any leading `using` keyword, detect whether the tactic head is `metis`,
   and produce both the canonical proof string (as used today) and a `smt (cvc5) …`
   variant when applicable. Does NOT consult the `try_parallel_smt_cvc5` config — the
   smt variant is always returned when `is_metis` holds; call sites gate on the config. *)
val mk_proof_candidates :
      string -> {is_metis : bool, metis_prf : string, smt_prf_opt : string option}

datatype fail_reason = Too_Many_Subgoals | Timeout | Application_Fails | Subgoal_unsolved | Unknown
                     | Prelude_Timeout | Subgoal_Fail of term
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

(* Like `auto`, but propagates Auto_Fail instead of converting it to ERROR.
   The caller is responsible for handling Auto_Fail (including Subgoal_Fail).
   WARNING: Par_Exn from parallel thread failures may also propagate —
   callers should handle or convert them. *)
val auto_raw : bool -> Sledgehammer.fact_override -> Phi_Cache_DB.proof_id option
            -> Time.time option -> Proof.context -> thm -> string * thm

val fast_mepo_max_facts : int Config.T
val fast_mepo_tac : Time.time -> Proof.context -> int -> tactic

end

structure Phi_Sledgehammer_Solver : PHI_SLEDGEHAMMER_SOLVER = struct

(*** Preliminaries ***)

(** Options **)

val classical_prover_timeout =
        Attrib.setup_config_int \<^binding>\<open>classical_prover_timeout\<close> (K 3)

val fast_mepo_max_facts =
  Attrib.setup_config_int \<^binding>\<open>fast_mepo_max_facts\<close> (K 32)

val sledgehammer_params_fixed = [("isar_proofs", "false")]

val sledgehammer_params = Attrib.setup_config_string \<^binding>\<open>auto_sledgehammer_params\<close> (K "")
val preplay_timeout = Attrib.setup_config_int \<^binding>\<open>auto_sledgehammer_preplay_timeout\<close> (K 10)
val try_parallel_smt_cvc5 =
  Attrib.setup_config_bool \<^binding>\<open>auto_sledgehammer_try_parallel_smt_cvc5\<close> (K false)

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
  | dest_eq _ = NONE

val chk_simp = is_some o dest_eq
fun chk_split thm =
  (case Thm.concl_of (Simpdata.mk_eq thm) of
    \<^Const_>\<open>Pure.eq _ for \<open>Var _ $ t\<close> c\<close> =>
      (case strip_comb t of
        (Const p, _) => true
      | _ => false)
  | _ => false);

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
  let fun chk _ []  = NONE
        | chk N [#"I"] = if N >= 2 then SOME T_INTRO else NONE
        | chk N [#"E"] = if N >= 2 then SOME T_ELIM  else NONE
        | chk N [#"D"] = if N >= 2 then SOME T_DEST  else NONE
        | chk N (c::cs) = if Char.isUpper c then chk 0 cs else chk (N+1) cs
   in chk 0 (String.explode name)
  end

in

fun infer_type_of_rule name th =
  if String.isSuffix "_intro" name orelse
     String.isSuffix ".intro" name
     then T_INTRO
  else if String.isSuffix "_elim" name orelse
          String.isSuffix ".elim" name
       then T_ELIM
  else if String.isSuffix "_simp"  name orelse
          String.isSuffix ".simp"  name orelse
          String.isSuffix "_simps" name orelse
          String.isSuffix ".simps" name orelse
          String.isSuffix "_iff"   name
       then T_SIMP
  else if String.isSuffix "_def" name then T_IFF
  else if String.isSuffix ".splits" name then T_SPLIT
  else if String.isSuffix "_dest" name orelse
          String.isSuffix ".dest" name
       then T_DEST
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
        Metis_Method (NONE, NONE) => "metis"
      | Metis_Method (type_enc_opt, lam_trans_opt) =>
        "metis (" ^ commas (map_filter I [type_enc_opt, lam_trans_opt]) ^ ")"
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
      Proof.map_contexts (Try0.silence_methods false #> Config.put SMT_Config.verbose false)

val debug_state =
      Proof.map_contexts (Try0.silence_methods false #> Config.put SMT_Config.verbose true
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

datatype fail_reason = Too_Many_Subgoals | Timeout | Application_Fails | Subgoal_unsolved | Unknown
                     | Prelude_Timeout | Subgoal_Fail of term
exception Auto_Fail of fail_reason

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

fun eval_prf_str _ timeout "" (ctxt,sequent) =
      \<^try>\<open>Timeout.apply timeout (Timing.timing (
            Position.setmp_thread_data Position.none auto_obligation_solver1)
         ) (ctxt,sequent) |> apfst (fn {elapsed=time,...} => (time,""))
         catch Timeout.TIMEOUT _               => raise Auto_Fail Timeout
                  |  err => (tracing ("Unexpected error, maybe a bug: " ^ Runtime.exn_message err);
                             raise Auto_Fail Unknown)\<close>
  | eval_prf_str kws timeout prf (ctxt,sequent) = \<^try>\<open>
      let val protected = Goal.protect 1 sequent
          val seq =
            Method.evaluate (
              Parse.read_embedded ctxt kws Method.parse (Input.string prf)
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
              | err => (tracing ("Unexpected error, maybe a bug: " ^ Runtime.exn_message err);
                         raise Auto_Fail Unknown) \<close>


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
          tracing "The proof fails due to timeout. Re-searching proofs...";
          raise Auto_Fail Timeout)
            | Auto_Fail reason => raise Auto_Fail reason
            | err => (
          tracing ("Unexpected error, maybe a bug: " ^ Runtime.exn_message err);
          raise Auto_Fail Unknown) \<close>
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
            fun find c s = CharVector.foldri (fn (i, c', ret) => if c' = c then i :: ret else ret) [] s
            val inds = find #"\^E" s
         in if length inds < 4
            then tracing s
            else let
              val i2 = List.nth (inds, 1)
              val i3 = List.nth (inds, 2)
              val i4 = List.nth (inds, 3)
              val s_prf = String.substring (s, i2+1, i3 - 1 -i2)
              val preplay_succeeded = is_some (CharVector.findi (fn (i,c) => i > i4 andalso c = #"(") s)
              val {is_metis = _, metis_prf = prf, smt_prf_opt = raw_smt_opt} =
                    mk_proof_candidates s_prf
              val smt_prf_opt =
                    if Config.get (Proof.context_of stat) try_parallel_smt_cvc5
                    then raw_smt_opt else NONE
              val _ = tracing s
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
              then (tracing "no proof found. give up in advance"; Future.cancel_group group)
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

val assync_proof = Attrib.setup_config_bool \<^binding>\<open>\<phi>assync_proof\<close> (K false)

fun assync_prove f (ctxt,sequent) =
  let val (goal_term,_) = Thm.cprop_of sequent |> Thm.dest_implies
   in if Term.maxidx_term (Thm.term_of goal_term) ~1 <> ~1 orelse
         not (Config.get ctxt assync_proof)
      then f (ctxt,sequent)
      else let val pos' = Thread_Position.get ()
               val pos = Position.make pos'
               val hyps = Assumption.all_assms_of ctxt
               val goal_term' = Drule.list_implies (hyps,goal_term)
               val goal_stat = Goal.init goal_term
               val future = Execution.fork {name="\<phi>System-async-proof", pos=pos, pri = ~1} (fn _ =>
                        f (ctxt, goal_stat)
                    (*|> Thm.solve_constraints
                    |> Thm.strip_shyps *)
                    |> fold_rev Thm.implies_intr hyps
                    |> Goal.conclude (*
                    |> (fn th => (if Thm.prop_of th aconv Thm.term_of goal_term' then () else
                                  error "XXXXXXXXXXXXX!"; th)) *)
                  handle
                     Auto_Fail _ => (
                       Future.error_message pos
                          ((serial (), error_message ctxt sequent), NONE);
                       raise Fail (error_message ctxt sequent)))
               val _ = Phi_Cache_DB.register_async_task (Future.task_of future) (Proof_Context.theory_of ctxt)
            in Thm.implies_elim sequent (
                  Goal.future_result ctxt future (Thm.term_of goal_term') (*TODO: optimize this!*)
                    |> fold (fn a => fn th => Thm.implies_elim th (Thm.assume a)) hyps)
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

fun wrapper f (ctxt,sequent) =
  if Thm.no_prems sequent
  then ("", sequent)
  else case Thm.major_prem_of sequent
    of Const (\<^const_name>\<open>Trueprop\<close>, _) $ \<^const>\<open>True\<close> =>
            ("rule TrueI", @{thm TrueI} RS sequent)
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
                  val (prf, result) = f (ctxt, sequent')
              in (insert_prefix ^ prf, result) end


val time_delt = Time.fromMilliseconds 1000
fun folerant_time t = Time.scale 1.3 t + time_delt

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

local

val mepo_dummy_params = {
  debug = false, verbose = false, overlord = false, spy = false,
  provers = [], abduce = NONE, falsify = NONE, type_enc = NONE,
  strict = false, lam_trans = NONE, uncurried_aliases = NONE,
  learn = false, fact_filter = NONE, induction_rules = NONE,
  max_facts = NONE, fact_thresholds = (0.45, 0.85),
  max_mono_iters = NONE, max_new_mono_instances = NONE,
  max_proofs = 1, isar_proofs = NONE, compress = NONE,
  try0 = false, smt_proofs = false, minimize = false,
  slices = 1, timeout = Time.fromSeconds 5,
  preplay_timeout = Time.fromSeconds 1, expect = ""
} : Sledgehammer_Prover.params

fun local_facts_as_mepo_lazy_facts ctxt =
  let
    val transfer = Thm.transfer' ctxt
    val local_facts = Proof_Context.facts_of ctxt
    val outer_facts = try Local_Theory.target_of ctxt
                   |> Option.map Proof_Context.facts_of
                   |> the_list
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
  end

(* Render the cached Isar method string from MePo's selection.
   to_insert / to_add are (name_string, thm) pairs. The name strings produced
   by `local_facts_as_mepo_lazy_facts`'s `get_name ()` are already valid Isar
   fact references in all three shapes it can produce:
     - "name"           — singleton bundle
     - "name(N)"        — j-th member of an N-member bundle (valid Isar selector)
     - "\<open>...\<close>" — cartouche-by-content for anonymous facts
   and the cartouche content is pre-stripped of YXML markup by
   `hackish_string_of_term` inside `Sledgehammer_Fact.cartouche_thm`. So we
   can splice the name strings directly into the generated method text. *)
fun render_fast_mepo_proof to_insert to_add =
  let
    val ithm = if null to_insert then ""
               else "insert " ^ space_implode " " (map fst to_insert) ^ ", "
    fun clause label ty =
          map_filter (fn (name, th) =>
            if infer_type_of_rule name th = ty then SOME name else NONE) to_add
       |> (fn [] => ""
            | L => " " ^ label ^ ": " ^ space_implode " " L)
    val simps  = clause "simp"  T_SIMP
    val unkns  = clause "simp"  T_UNKNOWN  (* modifier_of true T_UNKNOWN = simp_add *)
    val intros = clause "intro" T_INTRO
    val elims  = clause "elim"  T_ELIM
    val dests  = clause "dest"  T_DEST
    val congs  = clause "cong"  T_CONG
    val splits = clause "split" T_SPLIT
    val iffs   = clause "iff"   T_IFF
  in
    String.concat ["(", ithm, "fastforce", simps, unkns, intros, elims, dests,
                   congs, splits, iffs, ")"]
  end

in

(* Run MePo + fastforce on the i-th subgoal. On success returns the proved
   sequent, the rendered Isar replay string, and the fastforce-only elapsed
   time (NOT including MePo selection time, since the cache replay only
   re-runs fastforce, not MePo). On failure raises Auto_Fail. *)
fun run_mepo_and_render timeout ctxt i st =
  let
    val max_facts = Config.get ctxt fast_mepo_max_facts
    val lazy_facts = local_facts_as_mepo_lazy_facts ctxt

    val goal_term = Logic.get_goal (Thm.prop_of st) i
    val hyp_ts = Logic.strip_assums_hyp goal_term
    val concl_t = Logic.strip_assums_concl goal_term

    val selected = Sledgehammer_MePo.mepo_suggested_facts
                     ctxt mepo_dummy_params max_facts NONE hyp_ts concl_t lazy_facts
    (* MePo treats False/True as invisible connectives, so goals composed entirely
       of them yield zero features and an empty selection.  Fall back to all local facts. *)
    val selected = if null selected then map Sledgehammer_Fact.fact_of_lazy_fact lazy_facts
                   else selected

    val sbi = should_be_inserted ctxt
    val (to_insert, to_add) =
      fold_rev (fn ((name, _), th) => fn (ins, add) =>
        if sbi (Thm.prop_of th)
        then ((name, th) :: ins, add)
        else (ins, (name, th) :: add)
      ) selected ([], [])

    val ctxt' = fold (fn (name, th) => fn c =>
      with_rule true name th (Context.Proof c) |> Context.proof_of
    ) to_add ctxt

    val insert_thms = map snd to_insert

    fun fastforce_branch () =
      (Method.insert_tac ctxt insert_thms i THEN Clasimp.fast_force_tac ctxt' i) st

    val start = Time.now ()
  in
    case Timeout.apply timeout (fn () => Seq.pull (fastforce_branch ())) ()
              handle Timeout.TIMEOUT _ => NONE of
      NONE => raise Auto_Fail Application_Fails
    | SOME (st', _) =>
        let val elapsed = Time.- (Time.now (), start)
            val prf_str = render_fast_mepo_proof to_insert to_add
        in (st', prf_str, elapsed) end
  end

(* Replay a cached Isar method on the i-th subgoal of `st`. For i = 1 we just
   call eval_prf_str directly; for i > 1 we wrap with Goal.restrict / unrestrict
   so the cached "(insert ..., fastforce ...)" string (which acts on subgoal 1
   of whatever sequent it sees) lands on the right subgoal. *)
fun replay_mepo_proof kws timeout i prf (ctxt, st) =
  if i = 1 then
    let val (_, cs) = eval_prf_str kws timeout prf (ctxt, st) in cs end
  else
    let
      val st_focused = Goal.restrict i 1 st
      val (_, (ctxt', st_focused')) =
            eval_prf_str kws timeout prf (ctxt, st_focused)
    in
      (ctxt', Goal.unrestrict i st_focused')
    end

fun fast_mepo_tac timeout ctxt i st =
  if Thm.nprems_of st < i then Seq.empty
  else if not (Config.get ctxt Phi_Cache_DB.enable_proof_cache) then
    ((case run_mepo_and_render timeout ctxt i st of
        (st', _, _) => Seq.single st')
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
            let val (st', prf_str, elapsed) = run_mepo_and_render timeout ctxt i st
             in ((elapsed, prf_str), (ctxt, st')) end
    in
      ((case Phi_Cache_DB.try_cached_proof_by_hash_at i evaluator fallback (ctxt, st) of
          (_, (_, st')) => Seq.single st')
       handle Auto_Fail _ => Seq.empty
            | Timeout.TIMEOUT _ => Seq.empty)
    end

end


fun sledgehammer timeout_opt improved hasty kws override0 (ctxt,sequent) =
  let val (goal_term,_) = Logic.dest_implies (Thm.prop_of sequent)

      val failed_subgoal = Unsynchronized.ref (NONE : term option)

      val pass_thms  = filter (can (Attrib.eval_thms ctxt) o single)
      val pass_thms' = map_filter (fn th => try (rpair th o Attrib.eval_thms ctxt) [th])
      val origin_add = pass_thms' (#add override0)
      val origin_del = pass_thms' (#del override0)

      val sbi = should_be_inserted ctxt
      val (ithms, sthms, OA) = fold_rev (fn (th', th) => fn (I,S,OA) =>
            if exists (sbi o Thm.prop_of) th'
            then (restore_ref' th :: I, S, OA)
            else (I, restore_ref' th :: S, (th', th) :: OA)
          ) origin_add ([],[],[])
      val ithm = if null ithms then "" else "insert " ^ space_implode " " ithms ^ ", "
      val sthm = if null sthms then "" else " " ^ space_implode " " sthms
      val dthm = if null origin_del then ""
                 else " simp del: " ^ space_implode " " (map (restore_ref' o snd) origin_del)
      val athms = space_implode " " (map (restore_ref' o snd) origin_add)

      val override = {add=map snd OA, del = map snd origin_del, only = #only override0}
      val raw_override = {add = map snd origin_add, del = map snd origin_del, only = #only override0}

      val need_standard = need_standard_tac ctxt sequent

      val stat = Proof.theorem NONE (K I) [[(goal_term, [])]] ctxt

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
          val N = Thm.nprems_of (@{print} (#goal (Proof.raw_goal stat0)))
          val Ns = string_of_int N

          val _ = if N > 30 then (tracing ("The prompt generates too many subgoals (" ^
                                    string_of_int N ^ "). give up...");
                                  raise Auto_Fail Too_Many_Subgoals)
                            else ()

          val (prfs, final_state) =
            funpow' N (fn j => fn (ps,s) =>
                        let val _ = tracing ("Sledgehammering on the " ^ string_of_int (N+1-j) ^
                                             "th goal (total " ^ Ns ^ ")")
                            val (p',s') = case raw_sledgehammer timeout_opt override hasty s
                                            of NONE =>
                                  let val subgoal_raw = hd (Thm.prems_of (#goal (Proof.raw_goal s)))
                                      val params = Logic.strip_params subgoal_raw
                                      val hyps = Logic.strip_assums_hyp subgoal_raw
                                      val concl = Logic.strip_assums_concl subgoal_raw
                                      val concl0 = Logic.strip_assums_concl goal_term
                                      val _ = if not (concl aconv concl0)
                                        then let
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
                                        else ()
                                   in raise Auto_Fail Application_Fails
                                  end
                               | SOME prf => prf
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

      fun fastforce () =
        let val ctxt = Proof.context_of stat
            fun nth_iv' i (Facts.FromTo (j,k) :: L) =
                  if i < k-j+1
                  then SOME [Facts.Single (j+i)]
                  else nth_iv' (i - (k-j+1)) L
              | nth_iv' i [Facts.From j] = SOME [Facts.Single (j+i)]
              | nth_iv' i (Facts.Single j :: L) = nth_iv' i (Facts.FromTo (j,j) :: L)
              | nth_iv' _ _ = error "BUG SH fastforce() nth_iv"
            
            fun nth_iv N i iv =
                  if i + 1 = N then NONE
                  else case iv
                    of NONE => SOME [Facts.Single (i+1)]
                     | SOME ivs => ivs
                                |> sort iv_ord
                                |> nth_iv' i
            val type_of_thms = maps (
                  fn (ths, (Facts.Named ((name, pos), iv), atts)) =>
                      let val N = length ths
                       in map_index (fn (i,th) =>
                            (infer_type_of_rule name th,
                             (Facts.Named ((name, pos), nth_iv N i iv), atts))
                          ) ths
                      end
                   | ([th], fact as (Facts.Fact _, _)) =>
                        [(infer_type_of_rule "" th, fact)]
                   | _ => error "BUG SH fastforce() 2"
                    )
            val thms = type_of_thms OA
            val dthms= type_of_thms origin_del
            val simps  = map_filter (fn (ty, x) => if ty = T_SIMP then SOME x else NONE) thms
                      |> merge_facts ctxt
                      |> (fn [] => "" | L =>  " simp: " ^ space_implode " " (map restore_ref' L))
            val intros = map_filter (fn (ty, x) => if ty = T_INTRO then SOME x else NONE) thms
                      |> merge_facts ctxt
                      |> (fn [] => "" | L => " intro: " ^ space_implode " " (map restore_ref' L))
            val elims  = map_filter (fn (ty, x) => if ty = T_ELIM then SOME x else NONE) thms
                      |> merge_facts ctxt
                      |> (fn [] => "" | L =>  " elim: " ^ space_implode " " (map restore_ref' L))
            val dests  = map_filter (fn (ty, x) => if ty = T_DEST then SOME x else NONE) thms
                      |> merge_facts ctxt
                      |> (fn [] => "" | L =>  " dest: " ^ space_implode " " (map restore_ref' L))
            val congs  = map_filter (fn (ty, x) => if ty = T_CONG then SOME x else NONE) thms
                      |> merge_facts ctxt
                      |> (fn [] => "" | L =>  " cong: " ^ space_implode " " (map restore_ref' L))
            val splits = map_filter (fn (ty, x) => if ty = T_SPLIT then SOME x else NONE) thms
                      |> merge_facts ctxt
                      |> (fn [] => "" | L => " split: " ^ space_implode " " (map restore_ref' L))
            val iffs   = map_filter (fn (ty, x) => if ty = T_IFF then SOME x else NONE) thms
                      |> merge_facts ctxt
                      |> (fn [] => "" | L =>   " iff: " ^ space_implode " " (map restore_ref' L))

            val dsimps= map_filter (fn (ty, x) => if ty = T_SIMP then SOME x else NONE) dthms
                      |> merge_facts ctxt
                      |> (fn [] => "" | L =>  " simp del: " ^ space_implode " " (map restore_ref' L))
            val dcongs= map_filter (fn (ty, x) => if ty = T_CONG then SOME x else NONE) dthms
                      |> merge_facts ctxt
                      |> (fn [] => "" | L =>  " cong del: " ^ space_implode " " (map restore_ref' L))
            val dsplits= map_filter (fn (ty, x) => if ty = T_SPLIT then SOME x else NONE) dthms
                      |> merge_facts ctxt
                      |> (fn [] => "" | L =>  " split del: " ^ space_implode " " (map restore_ref' L))
            val diff   = map_filter (fn (ty, x) => if ty = T_IFF then SOME x else NONE) dthms
                      |> merge_facts ctxt
                      |> (fn [] => "" | L =>  " iff del: " ^ space_implode " " (map restore_ref' L))
            val del    = map snd dthms
                      |> merge_facts ctxt
                      |> (fn [] => "" | L =>  " del: " ^ space_implode " " (map restore_ref' L))


            val src = String.concat ["(",
                        ithm, "fastforce", simps, intros, elims, dests, congs, splits, iffs,
                        dsimps, dcongs, dsplits, diff, del,
                      ")"]
         in (* tracing src
          ; *) eval_prf_str_stat kws 5 NONE src (
                Proof.map_context (Context_Position.set_visible false) stat)
         |> apsnd (#goal o Proof.goal)
        end

      fun smt () =
        let val src = "(smt " ^ athms ^ ")"
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

      val prf = if improved
        then Par_List.get_some (fn F => SOME (F ()) handle Auto_Fail _ => NONE) [
            hammer',
            bare_hammer,
            fastforce,
            simp,
            smt
          ]
        else (SOME (bare_hammer ()) handle Auto_Fail _ => NONE)

   in case prf
   of SOME (prf, sequent') =>
        if hasty
        then ((Time.zeroTime, "<cheat>"), (ctxt, sequent'))
        else eval_prf_str kws Time.zeroTime prf (ctxt,sequent)
    | NONE => (case !failed_subgoal
                 of SOME t => raise Auto_Fail (Subgoal_Fail t)
                  | NONE => raise Auto_Fail Application_Fails)
  end


fun auto'i timeout_opt improved override id (ctxt,sequent) =
  let
    val id = case id of SOME some => some
                      | _ => Hasher.goal (ctxt,sequent)
    val hasty = Config.get ctxt hasty_mode

    val thy = Proof_Context.theory_of ctxt
    val kws = Keyword.no_major_keywords (
                      Thy_Header.get_keywords (Proof_Context.theory_of ctxt))

    fun try_cached_proof fallback =
     (case Phi_Cache_DB.get_cached_proof thy id
        of NONE => fallback true
         | SOME (time,prf) =>
            let val nprem = Thm.nprems_of sequent
                val ctxt' = ctxt (*if prf = "" then ctxt else Phi_Envir.freeze_dynamic_lemmas ctxt*)
             in (case eval_prf_str kws (Time.scale 1.5 time + time_delt) prf (ctxt', sequent)
                   of (_, (_, sequent')) =>
                      if Thm.nprems_of sequent' < nprem
                      then (prf, sequent')
                      else raise Auto_Fail Subgoal_unsolved )
                handle Auto_Fail _ => fallback false
            end )

    fun update_cache hash (prf', (ctxt, sequent')) = (
           tracing (
              "Find proof (" ^ id ^ ", time: " ^ Value.print_time (fst prf') ^ "): " ^
               (if snd prf' = "" then "classical automation" else "\n" ^ snd prf')
           ) ;
           Phi_Cache_DB.update_hash_cache hash prf';
           Phi_Cache_DB.update_cached_proof thy (id, prf') ;
           (snd prf', sequent'))



    val classical_timeout = Config.get ctxt classical_prover_timeout
    fun find_proof () =
     ((* case Timeout.apply (Time.fromSeconds classical_timeout) (Timing.timing Seq.pull)
                            (auto_obligation_solver (ctxt, sequent))
        of ({elapsed=time,...}, SOME (sequent', _)) =>
            ((time,""), (ctxt, sequent'))
         | _ => (
            tracing "Proof search by default tactic fails. Invoking sledgehammer..."; *)
            sledgehammer timeout_opt improved hasty kws override (ctxt, sequent) )
      handle Timeout.TIMEOUT _ => (
        tracing "Proof search by default tactic times out. Invoking sledgehammer...";
        sledgehammer timeout_opt improved hasty kws override (ctxt, sequent) )

    in try_cached_proof (fn no_cache' => (let
          val hash = Hasher.goal (ctxt,sequent)
          val (no_cache, prf_result') =
                case Phi_Cache_DB.access_hash_cache hash
                  of SOME (t, prf) =>
                      let val ctxt' = ctxt (*if prf = "" then ctxt else Phi_Envir.freeze_dynamic_lemmas ctxt*)
                       in ((false, SOME (
                                  eval_prf_str kws (folerant_time t) prf (ctxt',sequent)))
                           handle Auto_Fail _ => (false, NONE))
                      end
                   | NONE => (no_cache', NONE)

          val prf_result =
                case prf_result' of SOME ret => ret
                   | NONE => (if no_cache
                              then (tracing ("Proof cache miss, " ^ id))
                              else (warning "A cached proof fails. Re-searching proofs...";
                                    Phi_Cache_DB.invalidate_proof_cache (not no_cache) id thy) ;
                              find_proof ())
           in if hasty
           then let val ((_,prf'), (_, sequent')) =  prf_result
                 in (prf', sequent')
                end
           else update_cache hash prf_result
          end ))
   end
(* val proof = raw_sledgehammer stat *)

fun auto improved override id timeout_opt ctxt sequent =
  let val ctxt' = case timeout_opt of
          NONE => ctxt
        | SOME t => Config.map sledgehammer_params
                      (fn s => "timeout = " ^ string_of_int (Time.toSeconds t)
                               ^ (if s = "" then "" else ", " ^ s)) ctxt
  in \<^try>\<open>
       wrapper (auto'i timeout_opt improved override id) (ctxt', sequent)
       catch Auto_Fail _ => error (error_message ctxt sequent)
           | exn => (case Par_Exn.dest exn of
               SOME exns =>
                 let val msgs = map_filter (fn ERROR msg => SOME msg | _ => NONE) exns
                 in if null exns orelse length msgs <> length exns
                    then Exn.reraise exn
                    else error (String.concatWith "\n" msgs)
                 end
             | NONE => Exn.reraise exn)
     \<close>
  end

fun auto_raw improved override id timeout_opt ctxt sequent =
  let val ctxt' = case timeout_opt of
          NONE => ctxt
        | SOME t => Config.map sledgehammer_params
                      (fn s => "timeout = " ^ string_of_int (Time.toSeconds t)
                               ^ (if s = "" then "" else ", " ^ s)) ctxt
  in wrapper (auto'i timeout_opt improved override id) (ctxt', sequent)
  end

fun all_auto improved override id ctxt sequent =
  let fun loop sequent =
        if Thm.no_prems sequent
        then ([], sequent)
        else let val (prf, sequent') = wrapper (auto'i NONE improved override id) (ctxt,sequent)
          in loop sequent'
          |> apfst (fn L => prf :: L)
         end
      val (prfs, sequent') = loop sequent
   in ("(" ^ String.concatWith ", " prfs ^ ")", sequent')
  end
  handle Auto_Fail _ => error (error_message ctxt sequent)

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
  

fun orverride_parser toks = (
        Scan.repeat (   (Args.add |-- \<^keyword>\<open>:\<close> |-- Scan.repeat (not_del Parse.thm) >> rpair [])
                     || (Args.del |-- \<^keyword>\<open>:\<close> |-- Scan.repeat Parse.thm >>  pair []) )
     >> (fn LL => fold_rev (fn (A,D) => fn (A',D') => (A @ A', D @ D') ) LL ([],[])
               |> (fn (A,D) => {add = A, del = D, only = false})) ) toks

val _ = Theory.setup (
Method.setup \<^binding>\<open>auto_sledgehammer\<close> (Scan.lift (
  orverride_parser >> (fn override => fn _ =>
  Method.CONTEXT_METHOD (fn uses => fn (ctxt0,sequent) => Seq.make (fn () =>
    let val ctxt = Config.put assync_proof false ctxt0
        val id = Hasher.goal (ctxt,sequent)
        fun err () = error_message ctxt sequent
        val sequent' =
              case Seq.pull (Method.insert_tac ctxt uses 1 sequent)
                of SOME (ret, _) => ret
                 | NONE => error "Why the insert_tac can fail?"
     in SOME (
         (Seq.Result (ctxt, snd (auto true override (SOME id) NONE ctxt sequent'))
          handle Auto_Fail _ => Seq.Error err),
         Seq.empty)
    end))
)))
  "Apply sledgehammer transparently and record the outcome."
#>
Method.setup \<^binding>\<open>auto_sledgehammers\<close> (Scan.lift (
  orverride_parser >> (fn override => fn _ =>
  Method.CONTEXT_METHOD (fn uses => fn (ctxt0,sequent) => Seq.make (fn () =>
    let val ctxt = Config.put assync_proof false ctxt0
        val id = Hasher.goal (ctxt,sequent)
        fun err () = error_message ctxt sequent
        val sequent' =
              case Seq.pull (Method.insert_tac ctxt uses 1 sequent)
                of SOME (ret, _) => ret
                 | NONE => error "Why the insert_tac can fail?"
     in SOME (
         (Seq.Result (ctxt, snd (all_auto true override (SOME id) ctxt sequent'))
          handle Auto_Fail _ => Seq.Error err),
         Seq.empty)
    end))
)))
  "Apply sledgehammer repeatedly to all goals and record the outcome."
#>
Method.setup \<^binding>\<open>raw_sledgehammer\<close> (Scan.lift (
  orverride_parser >> (fn override => fn _ =>
  Method.CONTEXT_METHOD (fn uses => fn (ctxt0,sequent) => Seq.make (fn () =>
    let val ctxt = Config.put assync_proof false ctxt0
        val id = Hasher.goal (ctxt,sequent)
        fun err () = error_message ctxt sequent
        val sequent' =
              case Seq.pull (Method.insert_tac ctxt uses 1 sequent)
                of SOME (ret, _) => ret
                 | NONE => error "Why the insert_tac can fail?"
     in SOME (
         (Seq.Result (ctxt, snd (auto false override (SOME id) NONE ctxt sequent'))
          handle Auto_Fail _ => Seq.Error err),
         Seq.empty)
    end))
)))
  "Apply sledgehammer transparently and record the outcome."
#>
Method.setup \<^binding>\<open>raw_sledgehammers\<close> (Scan.lift (
  orverride_parser >> (fn override => fn _ =>
  Method.CONTEXT_METHOD (fn uses => fn (ctxt0,sequent) => Seq.make (fn () =>
    let val ctxt = Config.put assync_proof false ctxt0
        val id = Hasher.goal (ctxt,sequent)
        fun err () = error_message ctxt sequent
        val sequent' =
              case Seq.pull (Method.insert_tac ctxt uses 1 sequent)
                of SOME (ret, _) => ret
                 | NONE => error "Why the insert_tac can fail?"
     in SOME (
         (Seq.Result (ctxt, snd (all_auto false override (SOME id) ctxt sequent'))
          handle Auto_Fail _ => Seq.Error err),
         Seq.empty)
    end))
)))
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
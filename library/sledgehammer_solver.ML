signature PHI_SLEDGEHAMMER_SOLVER = sig

val orverride_parser : Sledgehammer.fact_override parser
val auto : Sledgehammer.fact_override
        -> Phi_Cache_DB.proof_id option
        -> Proof.context -> thm -> string (*proof*) * thm

val assync_proof : bool Config.T

val sledgehammer_params : string Config.T
val classical_prover_timeout : int Config.T

datatype fail_reason = Too_Many_Subgoals | Timeout | Application_Fails | Subgoal_unsolved | Unknown
                     | Prelude_Timeout
exception Auto_Fail of fail_reason

datatype type_of_rule = T_SIMP | T_INTRO | T_ELIM | T_DEST | T_CONG | T_SPLIT | T_IFF | T_UNKNOWN
val infer_type_of_rule : string -> thm -> type_of_rule
val with_rule : bool -> string -> thm -> Context.generic -> Context.generic
val should_be_inserted : Proof.context -> term -> bool

val need_standard_tac : Proof.context -> thm -> bool

end

structure Phi_Sledgehammer_Solver : PHI_SLEDGEHAMMER_SOLVER = struct

(*** Preliminaries ***)

(** Options **)

val classical_prover_timeout =
        Attrib.setup_config_int \<^binding>\<open>classical_prover_timeout\<close> (K 3)

val sledgehammer_params_fixed = [("isar_proofs", "false"), ("try0", "false")]

val sledgehammer_params = Attrib.setup_config_string \<^binding>\<open>auto_sledgehammer_params\<close> (K "")
val preplay_timeout = Attrib.setup_config_int \<^binding>\<open>auto_sledgehammer_preplay_timeout\<close> (K 10)

fun get_sledgehammer_params ctxt =
  Config.get ctxt sledgehammer_params
    |> String.tokens (fn #"," => true | _ => false)
    |> map (fn s => case String.tokens (fn #"=" => true | _ => false) s
                      of [k,v] => (Symbol.trim_blanks k, Symbol.trim_blanks v)
                       | _ => error ("Invalid auto_sledgehammer_params : " ^ s))

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

fun should_be_inserted ctxt  =
  let val outter = try Local_Theory.target_of ctxt
      fun is_new name = case outter of NONE => true
                                     | SOME ctxt' => Variable.is_newly_fixed ctxt ctxt' name
   in fn rule =>
      Term.add_free_names rule []
   |> filter is_new
   |> null
   |> not
  end

end

(** Does it need the standard tac? **)

fun need_standard_tac ctxt st =
  let val thy = Proof_Context.theory_of ctxt
      val [\<^Const>\<open>Trueprop\<close> $ goal] = Thm.prems_of st
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
                     | Prelude_Timeout
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
      let val seq =
            Method.evaluate (
              Parse.read_embedded ctxt kws Method.parse (Input.string prf)
                |> fst
                |> Method.check_text ctxt
              ) ctxt [] (ctxt, sequent)
        in case Timeout.apply timeout (Timing.timing (
                    Position.setmp_thread_data Position.none Seq.pull)) seq
             of ({elapsed=time,...}, SOME (Seq.Result ret, _)) => ((time,prf), ret)
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

val full_keywords = Thy_Header.get_keywords \<^theory>
val keywords = Keyword.no_major_keywords full_keywords

fun dirty_hack futures group pptimeout shortcut stat s =
  let fun find c s = CharVector.foldri (fn (i, c', ret) => if c' = c then i :: ret else ret) [] s
      val inds = find #"\^E" s
   in if length inds < 4
      then tracing s
      else let
        val i2 = List.nth (inds, 1)
        val i3 = List.nth (inds, 2)
        val i4 = List.nth (inds, 3)
        val s_prf = String.substring (s, i2+1, i3 - 1 -i2)
        val preplay_succeeded = is_some (CharVector.findi (fn (i,c) => i > i4 andalso c = #"(") s)
        fun trans toks =
          let val toks1 = case toks of [] => raise Fail "internal bug #e12asfwgy43"
                                     | (tok::L) =>
                                 if Token.is_command tok andalso Token.content_of tok = "using"
                                 then L else tok::L
              val sep = find_index (fn tok => Token.is_command tok andalso
                                              (Token.content_of tok = "apply" orelse
                                               Token.content_of tok = "by")) toks1
              val (using, tac) = if sep = ~1 then raise Fail "internal bug #e12asfwgy44"
                                 else (take sep toks1, drop (sep+1) toks1)
              fun unparse toks = String.concatWith " " (map Token.unparse toks)
              fun unparse_tac (tok1::tok2::R) =
                    if Token.keyword_with (fn s => s = "[") tok2
                       andalso not (Token.keyword_with (K true) tok1)
                    then "(" ^ unparse [tok1] ^ ")" ^ unparse (tok2::R)
                    else unparse (tok1::tok2::R)
                | unparse_tac toks = unparse toks

            in (if null using then "" else "(insert " ^ unparse using ^ ")[1], ") ^ unparse_tac tac
           end
        val prf = trans (Input.string s_prf
                      |> Input.source_explode
                      |> Token.tokenize full_keywords {strict = true}
                      |> filter Token.is_proper)
        val _ = tracing s
        fun eval_future () =
          Synchronized.change futures (
            fn NONE => NONE
             | SOME fs => SOME (
              Future.forks {name="SH-preplay", group = SOME group, deps = [], pri=20, interrupts=true}
              [fn () =>
                case try (Future.interruptible_task (eval_prf_str_stat keywords pptimeout NONE prf)) stat
                  of SOME ret => (
                       Synchronized.change shortcut (fn NONE => SOME ret
                                                      | some => some)
                     ; Future.cancel_group group)
                   | NONE => ()] @ fs))
        in if preplay_succeeded
         then case try (eval_prf_str_stat keywords 3 NONE prf) stat
             of SOME ret => (
                    Synchronized.change shortcut (fn NONE => SOME ret
                                                   | some => some)
                  ; Future.cancel_group group)
              | NONE => ()
         else eval_future ()
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


fun raw_sledgehammer override stat =
  let val N = #goal (Proof.goal stat) |> Thm.nprems_of
      val _ = if N = 0 then error "No subgoal!" else ()
      (* val ret : string list Synchronized.var = Synchronized.var "raw_sledgehammer" [] *)
      val futures = Synchronized.var "\<phi>sledgehammer.futures" (SOME [])
      val shortcut = Synchronized.var "\<phi>sledgehammer.shortcut" NONE
      val sledgehammer_params = sledgehammer_params_fixed @ get_sledgehammer_params (Proof.context_of stat)
      val ctxt = Proof.context_of stat
      val pptimeout = Config.get ctxt preplay_timeout
      val group = Future.new_group (Future.worker_group ())
   in Future.forks {name="\<phi>SH", group = SOME group, deps = [], pri=10, interrupts=true} [(fn () =>
        ( Sledgehammer.run_sledgehammer
            (Sledgehammer_Commands.default_params (Proof.theory_of stat) sledgehammer_params)
                Sledgehammer_Prover.Normal
                (SOME (dirty_hack futures group pptimeout shortcut stat)) 1 override
                (silence_state stat)
        ; ()))]
    |> Future.join_results
     ; Synchronized.change futures (K NONE)
     ; Future.cancel_group group
     ; ( case Synchronized.value shortcut
           of SOME ret => SOME ret
            | NONE => NONE )
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

fun wrapper f (ctxt,sequent) =
  if Thm.no_prems sequent
  then ("", sequent)
  else case Thm.major_prem_of sequent
    of Const (\<^const_name>\<open>Trueprop\<close>, _) $ \<^const>\<open>True\<close> =>
            ("", @{thm TrueI} RS sequent)
     | _ => f (ctxt,sequent)

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
fun fact_ord (Named ((s1,_),iv1), Named ((s2,_),iv2)) =
      prod_ord string_ord (option_ord (list_ord iv_ord)) ((s1,iv1), (s2,iv2))
  | fact_ord (Named _, Fact _) = GREATER
  | fact_ord (Fact _, Named _) = LESS
  | fact_ord (Fact s1, Fact s2) = string_ord (s1, s2)

val merge_facts = merge_facts' o sort (fact_ord o apply2 fst)
end


fun sledgehammer kws override0 (ctxt,sequent) =
  let val (goal_term,_) = Logic.dest_implies (Thm.prop_of sequent)

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

          val (prfs,_) =
            funpow' N (fn j => fn (ps,s) =>
                        let val _ = tracing ("Sledgehammering on the " ^ string_of_int (N+1-j) ^
                                             "th goal (total " ^ Ns ^ ")")
                            val (p',s') = case raw_sledgehammer override s
                                            of NONE => raise Auto_Fail Application_Fails
                                             | SOME prf => prf
                         in (p'::ps, s') end)
                     ((if prf0 = "" then [] else [prf0]),stat0)
    
          val prf = "(" ^ String.concatWith ",\n" (rev prfs) ^ ")"
        in prf end

      fun hammer' () =
        let val src1 = if need_standard
                       then "standard, " ^ ithm ^ "auto simp: "^ sthm ^ dthm
                       else ithm ^ "auto simp: "^ sthm ^ dthm
            val src2 = if need_standard
                       then "standard, " ^ ithm ^ "clarsimp simp: "^ sthm ^ dthm
                       else ithm ^ "clarsimp simp: "^ sthm ^ dthm
            val auto = SOME (eval_prf_str_stat kws 5 NONE src1 stat)
                       handle Auto_Fail E => NONE
            val clar = SOME (eval_prf_str_stat kws 4 NONE src2 stat)
                       handle Auto_Fail E => NONE
            val thy = Proof.theory_of stat
            val plan = case (auto, clar)
                         of (SOME (prf1, s1), SOME (prf2, s2)) =>
                            if Thm.equiv_thm thy (#goal (Proof.raw_goal s1),
                                                  #goal (Proof.raw_goal s2))
                            then [(prf2, s2)]
                            else [(prf1, s1), (prf2, s2)]
                          | (SOME ret, _) => [ret]
                          | (_, SOME ret) => [ret]
                          | _ => []
            fun get_some _ [] = NONE
              | get_some F [x] = F x
              | get_some F L = Par_List.get_some F L
         in if null plan
          then raise Auto_Fail Application_Fails
          else case get_some (SOME o hammer override) plan
            of SOME ret => ret
             | _ => raise Auto_Fail Application_Fails
        end

      fun bare_hammer () =
          hammer raw_override ("-", stat)

      fun fastforce () =
        let fun nth_iv' i (Facts.FromTo (j,k) :: L) =
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
                      |> merge_facts
                      |> (fn [] => "" | L =>  " simp: " ^ space_implode " " (map restore_ref' L))
            val intros = map_filter (fn (ty, x) => if ty = T_INTRO then SOME x else NONE) thms
                      |> merge_facts
                      |> (fn [] => "" | L => " intro: " ^ space_implode " " (map restore_ref' L))
            val elims  = map_filter (fn (ty, x) => if ty = T_ELIM then SOME x else NONE) thms
                      |> merge_facts
                      |> (fn [] => "" | L =>  " elim: " ^ space_implode " " (map restore_ref' L))
            val dests  = map_filter (fn (ty, x) => if ty = T_DEST then SOME x else NONE) thms
                      |> merge_facts
                      |> (fn [] => "" | L =>  " dest: " ^ space_implode " " (map restore_ref' L))
            val congs  = map_filter (fn (ty, x) => if ty = T_CONG then SOME x else NONE) thms
                      |> merge_facts
                      |> (fn [] => "" | L =>  " cong: " ^ space_implode " " (map restore_ref' L))
            val splits = map_filter (fn (ty, x) => if ty = T_SPLIT then SOME x else NONE) thms
                      |> merge_facts
                      |> (fn [] => "" | L => " split: " ^ space_implode " " (map restore_ref' L))
            val iffs   = map_filter (fn (ty, x) => if ty = T_IFF then SOME x else NONE) thms
                      |> merge_facts
                      |> (fn [] => "" | L =>   " iff: " ^ space_implode " " (map restore_ref' L))

            val dsimps= map_filter (fn (ty, x) => if ty = T_SIMP then SOME x else NONE) dthms
                      |> merge_facts
                      |> (fn [] => "" | L =>  " simp del: " ^ space_implode " " (map restore_ref' L))
            val dcongs= map_filter (fn (ty, x) => if ty = T_CONG then SOME x else NONE) dthms
                      |> merge_facts
                      |> (fn [] => "" | L =>  " cong del: " ^ space_implode " " (map restore_ref' L))
            val dsplits= map_filter (fn (ty, x) => if ty = T_SPLIT then SOME x else NONE) dthms
                      |> merge_facts
                      |> (fn [] => "" | L =>  " split del: " ^ space_implode " " (map restore_ref' L))
            val diff   = map_filter (fn (ty, x) => if ty = T_IFF then SOME x else NONE) dthms
                      |> merge_facts
                      |> (fn [] => "" | L =>  " iff del: " ^ space_implode " " (map restore_ref' L))
            val del    = map snd dthms
                      |> merge_facts
                      |> (fn [] => "" | L =>  " del: " ^ space_implode " " (map restore_ref' L))


            val src = String.concat ["(",
                        ithm, "fastforce", simps, intros, elims, dests, congs, splits, iffs,
                        dsimps, dcongs, dsplits, diff, del,
                      ")"]
         in (* tracing src
          ; *) eval_prf_str_stat kws 5 NONE src (
                Proof.map_context (Context_Position.set_visible false) stat)
         |> fst
        end

      fun smt () =
        let val src = "(smt " ^ athms ^ ")"
         in eval_prf_str_stat kws 5 NONE src stat
         |> fst
        end

      fun simp () =
        let val src = "(insert " ^ athms ^ ", simp)"
            val n0 = Thm.nprems_of (#goal (Proof.goal stat))
            val (ret, s') = eval_prf_str_stat kws 5 NONE src stat
         in if Thm.nprems_of (#goal (Proof.goal s')) + 1 = n0
          then ret
          else raise Auto_Fail Application_Fails
        end

      val prf = Par_List.get_some (fn F => SOME (F ()) handle Auto_Fail _ => NONE) [
            hammer',
            bare_hammer,
            fastforce,
            simp,
            smt

(*          (fn () => (tracing "Fails... Try instead a stronger or maybe weaker prompt..." ;
                     search_prf (ithm ^ "clarsimp simp: "^ sthm ^ dthm ^", ((rule conjI)+)?"))),
          (fn () => (if need_standard
                     then search_prf ("standard, " ^ ithm ^ "-")
                     else raise Auto_Fail Application_Fails )),
          (fn () => (tracing "Fails... Try instead the weakest prompt..." ;
                     search_prf (ithm ^ "-"))) *)
        ]

   in case prf
   of SOME prf => eval_prf_str kws Time.zeroTime prf (ctxt,sequent)
    | NONE => raise Auto_Fail Application_Fails
  end


fun auto'i override id (ctxt,sequent) =
  let
    val id = case id of SOME some => some
                      | _ => Hasher.goal (ctxt,sequent)

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
            sledgehammer kws override (ctxt, sequent) )
      handle Timeout.TIMEOUT _ => (
        tracing "Proof search by default tactic times out. Invoking sledgehammer...";
        sledgehammer kws override (ctxt, sequent) )

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
           in update_cache hash prf_result
          end ))
   end
(* val proof = raw_sledgehammer stat *)

fun auto override id ctxt sequent =
  wrapper  (auto'i override id) (ctxt,sequent)
  handle Auto_Fail _ => error (error_message ctxt sequent)

fun insert_tac _ [] _ = all_tac
  | insert_tac ctxt facts i =
      EVERY (map (fn r => resolve_tac ctxt [Thm.forall_intr_vars r COMP_INCR revcut_rl] i) facts);

val orverride_parser =
        Scan.repeat (   (Args.add |-- Scan.repeat Parse.thm >> rpair [])
                     || (Args.del |-- Scan.repeat Parse.thm >>  pair []) )
     >> (fn LL => fold_rev (fn (A,D) => fn (A',D') => (A @ A', D @ D') ) LL ([],[])
               |> (fn (A,D) => {add = A, del = D, only = false}))

val _ = Theory.setup (Method.setup \<^binding>\<open>auto_sledgehammer\<close> (Scan.lift (
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
         (Seq.Result (ctxt, snd (auto override (SOME id) ctxt sequent'))
          handle Auto_Fail _ => Seq.Error err),
         Seq.empty)
    end))
)))
  "Apply sledgehammer transparently and record the outcome."
)

end
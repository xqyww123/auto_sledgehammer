signature LOOPING_SIMP = sig
  type config = {only_check_local: bool, ignore_cond: bool, local_ignore_cond: bool}
  val simp_rule_may_loop : config -> Proof.context -> term -> bool
  val thms_to_once_simprocs : Proof.context -> thm list -> simproc list

  (* Pre-process a list of (name, thm) facts: remove looping simp rules and
     install them as once-firing simprocs in the returned context.
     Non-equation facts and non-looping equations pass through unchanged. *)
  val pass_looping_simps : config -> Proof.context -> (string * thm) list
                         -> (string * thm) list * Proof.context
end

structure Looping_Simp : LOOPING_SIMP = struct

type config = {only_check_local: bool, ignore_cond: bool, local_ignore_cond: bool}

local
  fun vperm (Var _, Var _) = true
    | vperm (Abs (_, _, s), Abs (_, _, t)) = vperm (s, t)
    | vperm (t1 $ t2, u1 $ u2) = vperm (t1, u1) andalso vperm (t2, u2)
    | vperm (t, u) = (t = u)

  val vars_set = Vars.build o Vars.add_vars
in
  fun var_perm (t, u) = vperm (t, u) andalso Vars.eq_set (apply2 vars_set (t, u))
end

fun matches_subterm_of thy pat (t as (f $ x)) =
      ((Pattern.match thy (pat, t) (Vartab.empty, Vartab.empty); true)
       handle Pattern.MATCH =>
         matches_subterm_of thy pat f orelse matches_subterm_of thy pat x)
  | matches_subterm_of thy pat (Abs (_, _, body)) =
      ((Pattern.match thy (pat, body) (Vartab.empty, Vartab.empty); true)
       handle Pattern.MATCH => matches_subterm_of thy pat body)
  | matches_subterm_of thy pat t =
      (Pattern.match thy (pat, t) (Vartab.empty, Vartab.empty); true)
      handle Pattern.MATCH => false

fun dest_simp_eq prop =
  let
    fun go prems (\<^Const>\<open>Pure.imp\<close> $ P $ Q) = go (P :: prems) Q
      | go prems (\<^Const>\<open>Pure.all _\<close> $ Abs (_, _, body)) = go prems body
      | go prems (\<^Const>\<open>Trueprop\<close> $ X) = go_obj prems X
      | go prems (\<^Const>\<open>Pure.eq _\<close> $ lhs $ rhs) = SOME (rev prems, lhs, rhs)
      | go _ _ = NONE
    and go_obj prems (\<^Const>\<open>HOL.implies\<close> $ P $ Q) = go_obj (P :: prems) Q
      | go_obj prems (\<^Const>\<open>HOL.All _\<close> $ Abs (_, _, body)) = go_obj prems body
      | go_obj prems (\<^Const>\<open>HOL.eq _\<close> $ lhs $ rhs) = SOME (rev prems, lhs, rhs)
      | go_obj _ _ = NONE
  in go [] prop end

fun has_local_free_vars ctxt t =
  if Local_Theory.level ctxt = 0
  then Term.exists_subterm is_Free t
  else not (null (Variable.add_newly_fixed ctxt (Local_Theory.target_of ctxt) t []))

fun simp_rule_may_loop (cfg: config) ctxt prop =
  case dest_simp_eq prop of
    NONE => false
  | SOME (prems, lhs, rhs) =>
      let val thy = Proof_Context.theory_of ctxt
          val has_local = has_local_free_vars ctxt lhs orelse has_local_free_vars ctxt rhs
      in matches_subterm_of thy lhs rhs
         andalso not (var_perm (lhs, rhs))
         andalso (null prems orelse #ignore_cond cfg
                  orelse (not (#local_ignore_cond cfg) orelse has_local))
         andalso (not (#only_check_local cfg) orelse has_local)
      end

fun thms_to_once_simprocs ctxt (thms: thm list) : simproc list =
  let
    val meta_rules = maps (Raw_Simplifier.mksimps ctxt) thms
    fun mk_once (i, rule) =
      let
        val fired = Unsynchronized.ref false
        val (lhs, _) = Logic.dest_equals
              (Logic.strip_imp_concl (Thm.prop_of rule))
        fun proc _ _ =
          if !fired then NONE
          else (fired := true; SOME rule)
      in
        SOME (Simplifier.make_simproc ctxt
          { name = "once_simproc_" ^ string_of_int i,
            lhss = [lhs],
            proc = K proc,
            identifier = [] })
      end handle TERM _ => NONE
  in map_filter I (map_index mk_once meta_rules) end

fun pass_looping_simps cfg ctxt facts =
  let
    val (looping, safe) = List.partition (fn (_, th) =>
        simp_rule_may_loop cfg ctxt (Thm.prop_of th)) facts
    val simprocs = thms_to_once_simprocs ctxt (map snd looping)
    val ctxt' = ctxt addsimprocs simprocs
  in (safe, ctxt') end

end

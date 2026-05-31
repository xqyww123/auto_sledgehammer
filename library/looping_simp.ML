signature LOOPING_SIMP = sig
  type config = {only_check_local: bool, ignore_cond: bool, local_ignore_cond: bool,
                 schematize_local_frees: bool}
  val simp_rule_may_loop : config -> Proof.context -> term -> bool
  val thms_to_once_simprocs : Proof.context -> thm list -> simproc list

  (* Pre-process a list of (name, thm) facts: remove looping simp rules and
     install them as once-firing simprocs in the returned context.
     Non-equation facts and non-looping equations pass through unchanged. *)
  val pass_looping_simps : config -> Proof.context -> (string * thm) list
                         -> (string * thm) list * Proof.context
end

structure Looping_Simp : LOOPING_SIMP = struct

type config = {only_check_local: bool, ignore_cond: bool, local_ignore_cond: bool,
               schematize_local_frees: bool}

local
  fun vperm (Var _, Var _) = true
    | vperm (Abs (_, _, s), Abs (_, _, t)) = vperm (s, t)
    | vperm (t1 $ t2, u1 $ u2) = vperm (t1, u1) andalso vperm (t2, u2)
    | vperm (t, u) = (t = u)

  val vars_set = Vars.build o Vars.add_vars
in
  fun var_perm (t, u) = vperm (t, u) andalso Vars.eq_set (apply2 vars_set (t, u))
end

fun dest_simp_eq prop =
  let
    fun go bvs prems (\<^Const>\<open>Pure.imp\<close> $ P $ Q) = go bvs (P :: prems) Q
      | go bvs prems (\<^Const>\<open>Pure.all _\<close> $ Abs (name, T, body)) =
          go ((name, T) :: bvs) prems body
      | go bvs prems (\<^Const>\<open>Trueprop\<close> $ X) = go_obj bvs prems X
      | go bvs prems (\<^Const>\<open>Pure.eq _\<close> $ lhs $ rhs) = SOME (bvs, rev prems, lhs, rhs)
      | go _ _ _ = NONE
    and go_obj bvs prems (\<^Const>\<open>HOL.implies\<close> $ P $ Q) = go_obj bvs (P :: prems) Q
      | go_obj bvs prems (\<^Const>\<open>HOL.All _\<close> $ Abs (name, T, body)) =
          go_obj ((name, T) :: bvs) prems body
      | go_obj bvs prems (\<^Const>\<open>HOL.eq _\<close> $ lhs $ rhs) = SOME (bvs, rev prems, lhs, rhs)
      | go_obj _ _ _ = NONE
  in go [] [] prop end

fun has_local_free_vars ctxt t =
  if Local_Theory.level ctxt = 0
  then Term.exists_subterm is_Free t
  else not (null (Variable.add_newly_fixed ctxt (Local_Theory.target_of ctxt) t []))

fun schematize_local_frees ctxt pat0 =
  let
    val is_keep =
      if Local_Theory.level ctxt > 0
      then Variable.is_fixed (Local_Theory.target_of ctxt)
      else K false
    val frees = Term.add_frees pat0 []
    val idx = maxidx_of_term pat0 + 1
    val (_, subst) = fold (fn (n, T) => fn (i, acc) =>
      if is_keep n then (i, acc)
      else (i + 1, (Free (n, T), Var ((n, i), T)) :: acc))
      frees (idx, [])
  in Term.subst_free subst pat0 end

fun simp_rule_may_loop (cfg: config) ctxt prop =
  case dest_simp_eq prop of
    NONE => false
  | SOME (bvs, prems, lhs, rhs) =>
      let val thy = Proof_Context.theory_of ctxt
          val has_local = has_local_free_vars ctxt lhs orelse has_local_free_vars ctxt rhs
          val idx = maxidx_of_term lhs + 1
          val closed_lhs = Term.subst_bounds
                (map_index (fn (i, (n, T)) => Var ((n, idx + i), T)) bvs, lhs)
          val pat = if #schematize_local_frees cfg
                    then schematize_local_frees ctxt closed_lhs
                    else closed_lhs
      in PLPR_Pattern.matches_subterm_of thy bvs pat rhs
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
            kind = Simproc,
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

signature LOOPING_SIMP = sig
  type config = {only_check_local: bool, ignore_cond: bool, local_ignore_cond: bool}
  val simp_rule_may_loop : config -> Proof.context -> term -> bool
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

end

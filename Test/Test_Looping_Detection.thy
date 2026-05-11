theory Test_Looping_Detection
  imports Auto_Sledgehammer.Auto_Sledgehammer
begin

ML \<open>
let
  val ctxt = \<^context>
  val default_cfg : Looping_Simp.config =
    {only_check_local = false, ignore_cond = false, local_ignore_cond = false}
  val check = Looping_Simp.simp_rule_may_loop default_cfg ctxt

  fun test_thm name expected =
    let val props = map Thm.prop_of (Proof_Context.get_thms ctxt name)
        val any_loops = exists check props
        val ok = any_loops = expected
        val _ = writeln (name ^ ": loops=" ^ Bool.toString any_loops ^
                         " (expected=" ^ Bool.toString expected ^ ")" ^
                         (if ok then " OK" else " FAIL"))
        val _ = if ok then () else error ("Test failed: " ^ name)
    in () end

  (* Permutative rules — should NOT be flagged *)
  val _ = test_thm "add.commute" false
  val _ = test_thm "add.left_commute" false
  val _ = test_thm "mult.commute" false
  val _ = test_thm "conj_commute" false
  val _ = test_thm "disj_commute" false

  (* Non-looping rules *)
  val _ = test_thm "add_0_right" false
  val _ = test_thm "add_0" false

  (* Unconditional looping rule *)
  val loop_prop = Syntax.read_prop ctxt "f x = g (f x)"
  val _ = let val r = check loop_prop
              val _ = writeln ("f x = g (f x): loops=" ^ Bool.toString r ^
                               " (expected=true)" ^ (if r then " OK" else " FAIL"))
          in if r then () else error "Test failed: unconditional loop" end

  (* Conditional looping rule — default config has local_ignore_cond=false,
     so the (false -> has_local) disjunct is vacuously true and this IS flagged *)
  val cond_prop = Syntax.read_prop ctxt "P x \<Longrightarrow> f x = g (f x)"
  val _ = let val r = check cond_prop
              val _ = writeln ("cond loop [default]: loops=" ^ Bool.toString r ^
                               " (expected=true)" ^ (if r then " OK" else " FAIL"))
          in if r then () else error "Test failed: cond loop with default cfg" end

  (* With local_ignore_cond=true: tested below in locale context where
     we can distinguish local vs non-local variables *)

  (* With ignore_cond=true: conditional rule IS flagged regardless *)
  val ic_cfg : Looping_Simp.config =
    {only_check_local = false, ignore_cond = true, local_ignore_cond = false}
  val _ = let val r = Looping_Simp.simp_rule_may_loop ic_cfg ctxt cond_prop
              val _ = writeln ("cond loop [ignore_cond=true]: loops=" ^
                               Bool.toString r ^ " (expected=true)" ^
                               (if r then " OK" else " FAIL"))
          in if r then () else error "Test failed: ignore_cond should flag" end

in () end
\<close>

text \<open>Locale parameter is NOT proof-local.\<close>

locale test_locale =
  fixes f :: "nat \<Rightarrow> nat" and g :: "nat \<Rightarrow> nat" and P :: "nat \<Rightarrow> bool"
begin

ML \<open>
let
  val ctxt = \<^context>
  val lic_cfg : Looping_Simp.config =
    {only_check_local = false, ignore_cond = false, local_ignore_cond = true}

  (* Conditional rule using only locale params (not proof-local) => not flagged *)
  val prop = Syntax.read_prop ctxt "P x \<Longrightarrow> f x = g (f x)"
  val r = Looping_Simp.simp_rule_may_loop lic_cfg ctxt prop
  val _ = writeln ("locale params [lic=true]: loops=" ^
                   Bool.toString r ^ " (expected=false)" ^
                   (if not r then " OK" else " FAIL"))
  val _ = if not r then () else error "Test failed: locale params should not be local"
in () end
\<close>

ML \<open>
let
  val ctxt0 = \<^context>
  val ([y], ctxt) = Variable.add_fixes ["y"] ctxt0
  val lic_cfg : Looping_Simp.config =
    {only_check_local = false, ignore_cond = false, local_ignore_cond = true}

  (* Conditional rule with a proof-local var => flagged *)
  val prop = Syntax.read_prop ctxt "P y \<Longrightarrow> f y = g (f y)"
  val r = Looping_Simp.simp_rule_may_loop lic_cfg ctxt prop
  val _ = writeln ("proof-local in locale [lic=true]: loops=" ^
                   Bool.toString r ^ " (expected=true)" ^
                   (if r then " OK" else " FAIL"))
  val _ = if r then () else error "Test failed: proof-local in locale should be flagged"
in () end
\<close>

end

text \<open>Proof-local variable with local_ignore_cond=true.\<close>

ML \<open>
let
  val ctxt0 = \<^context>
  val ([y], ctxt) = Variable.add_fixes ["y"] ctxt0

  val lic_cfg : Looping_Simp.config =
    {only_check_local = false, ignore_cond = false, local_ignore_cond = true}
  val prop = Syntax.read_prop ctxt "P y \<Longrightarrow> f y = g (f y)"
  val r = Looping_Simp.simp_rule_may_loop lic_cfg ctxt prop
  val _ = writeln ("proof-local var [lic=true]: loops=" ^
                   Bool.toString r ^ " (expected=true)" ^
                   (if r then " OK" else " FAIL"))
  val _ = if r then () else error "Test failed: proof-local var should be flagged"
in () end
\<close>

text \<open>only_check_local tests — need locale context to distinguish local vs non-local.\<close>

locale test_locale2 =
  fixes f :: "nat \<Rightarrow> nat" and g :: "nat \<Rightarrow> nat"
begin

ML \<open>
let
  val ctxt = \<^context>
  val ocl_cfg : Looping_Simp.config =
    {only_check_local = true, ignore_cond = false, local_ignore_cond = false}

  (* Only locale params, no local vars => not flagged *)
  val prop = Syntax.read_prop ctxt "f x = g (f x)"
  val r = Looping_Simp.simp_rule_may_loop ocl_cfg ctxt prop
  val _ = writeln ("only_check_local [no local]: loops=" ^
                   Bool.toString r ^ " (expected=false)" ^
                   (if not r then " OK" else " FAIL"))
  val _ = if not r then () else error "Test failed: only_check_local without local vars"
in () end
\<close>

ML \<open>
let
  val ctxt0 = \<^context>
  val ([y], ctxt) = Variable.add_fixes ["y"] ctxt0
  val ocl_cfg : Looping_Simp.config =
    {only_check_local = true, ignore_cond = false, local_ignore_cond = false}

  (* Has proof-local var y => flagged *)
  val prop = Syntax.read_prop ctxt "f y = g (f y)"
  val r = Looping_Simp.simp_rule_may_loop ocl_cfg ctxt prop
  val _ = writeln ("only_check_local [with local]: loops=" ^
                   Bool.toString r ^ " (expected=true)" ^
                   (if r then " OK" else " FAIL"))
  val _ = if r then () else error "Test failed: only_check_local with local var"
in () end
\<close>

end

end

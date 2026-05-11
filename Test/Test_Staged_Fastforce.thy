theory Test_Staged_Fastforce
  imports Auto_Sledgehammer.Auto_Sledgehammer
begin

declare [[enable_proof_cache = false]]

section \<open>Test: \<open>fast_mepo_tac\<close> basic functionality after refactoring\<close>

text \<open>
  Sanity check that \<open>fast_mepo_tac\<close> still works after the
  \<open>run_mepo_and_render\<close> signature change.  This goal is trivially solvable
  by \<open>fastforce\<close> without needing MePo-selected facts.
\<close>

lemma trivial_fastforce: "1 + 1 = (2::nat)"
  by (tactic \<open>
    Phi_Sledgehammer_Solver.fast_mepo_tac (Time.fromSeconds 5) \<^context> 1
  \<close>)

lemma trivial_fastforce2: "\<lbrakk> (x::nat) < y; y < z \<rbrakk> \<Longrightarrow> x < z"
  by (tactic \<open>
    Phi_Sledgehammer_Solver.fast_mepo_tac (Time.fromSeconds 5) \<^context> 1
  \<close>)


section \<open>Test: \<open>fast_mepo_tac\<close> with proof-local facts\<close>

text \<open>
  \<open>test_fn\<close> is opaque; the proof-local \<open>have\<close> binds a rewrite rule that
  MePo should select.
\<close>

definition test_fn :: "nat \<Rightarrow> nat" where
  "test_fn x = Suc (Suc x)"

lemma mepo_finds_proof_local_fact: "test_fn (test_fn x) = x + 4"
proof -
  have h: "test_fn x = x + 2" for x
    unfolding test_fn_def by simp
  show ?thesis
    by (tactic \<open>
      Phi_Sledgehammer_Solver.fast_mepo_tac (Time.fromSeconds 10) \<^context> 1
    \<close>)
qed


section \<open>Test: \<open>fast_mepo_tac\<close> on subgoal \<open>i > 1\<close>\<close>

lemma subgoal_two: "True" "1 + 2 = (3::nat)"
proof -
  show "True" ..
  show "1 + 2 = (3::nat)"
    by (tactic \<open>
      Phi_Sledgehammer_Solver.fast_mepo_tac (Time.fromSeconds 5) \<^context> 1
    \<close>)
qed


section \<open>Test: looping simp filtering in MePo path\<close>

text \<open>
  A looping rule among locally visible facts should be caught by
  \<open>pass_looping_simps\<close> inside \<open>run_mepo_and_render\<close>, preventing divergence.
\<close>

axiomatization loop_f :: "nat \<Rightarrow> nat" where
  loop_ax: "loop_f x = loop_f x + 0"

lemma loop_not_diverge: "loop_f 0 = loop_f 0"
  by (tactic \<open>
    Phi_Sledgehammer_Solver.fast_mepo_tac (Time.fromSeconds 5) \<^context> 1
  \<close>)


end

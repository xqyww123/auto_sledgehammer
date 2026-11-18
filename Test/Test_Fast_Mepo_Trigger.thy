theory Test_Fast_Mepo_Trigger
  imports Auto_Sledgehammer.Auto_Sledgehammer
begin

text \<open>
  Needs Isabelle with the Sledgehammer fact trigger patch (\<open>Sledgehammer_MePo.add_trigger\<close>).
  \<open>fast_mepo\<close> calls MePo even when the proof has no local facts, so a fact trigger can offer a fact.
\<close>

declare [[enable_proof_store = false]]

consts g :: "nat \<Rightarrow> nat"
axiomatization where g_eq: "g x = x + 1"

setup \<open>
  Context.theory_map (Sledgehammer_MePo.add_trigger "test" (fn _ =>
    [{name = "g_eq", prop = Thm.prop_of @{thm g_eq},
      stature = (ATP_Problem_Generate.Global, ATP_Problem_Generate.General)}]))
\<close>

text \<open>\<open>g_eq\<close> is no simp rule, so \<open>fastforce\<close> has it only from the trigger.\<close>

lemma "g 2 = 3"
  by (tactic \<open>Phi_Sledgehammer_Solver.fast_mepo_tac (Time.fromSeconds 5) \<^context> 1\<close>)

end

theory Test_Ground_Eval
  imports Auto_Sledgehammer.Auto_Sledgehammer
begin

declare [[enable_proof_cache = false]]

section \<open>The standalone \<open>ground_eval\<close> method\<close>

text \<open>
  \<open>ground_eval\<close> discharges a variable-free (ground) goal by code evaluation,
  reusing the same oracle as AoA's \<open>Compute\<close> operation
  (\<open>Ground_Eval.eval_ground\<close>).  It closes the goal iff its conclusion
  evaluates to \<open>True\<close>; on a false, non-ground or non-executable goal it simply
  fails so other backends can take over.
\<close>

lemma "(3::nat) * 7 = 21" by ground_eval
lemma "(2::nat) + 2 = 4" by ground_eval
lemma "(2::nat) < 3 \<and> (5::nat) = 5" by ground_eval
lemma "(2::nat) ^ 10 = 1024" by ground_eval

text \<open>A false (or non-ground) goal must NOT be closed by \<open>ground_eval\<close>: the
      tactic yields an empty sequence.\<close>

ML \<open>
  fun refuses goal =
    let val st = Goal.init (Thm.cterm_of \<^context> (Syntax.read_prop \<^context> goal))
    in case Seq.pull (Ground_Eval.eval_ground_tac 10 \<^context> 1 st)
         of NONE => () | SOME _ => error ("ground_eval wrongly closed: " ^ goal) end
  val _ = refuses "(2::nat) + 2 = 5"   (* false ground goal *)
  val _ = refuses "(x::nat) + 0 = x"   (* non-ground goal    *)
\<close>


section \<open>Integration into \<open>auto_sledgehammer\<close>\<close>

text \<open>
  The ground-eval backend is the first candidate in the parallel solver, so
  large ground goals are dispatched by evaluation instead of sledgehammer.
\<close>

lemma "(123::nat) * 456 = 56088" by auto_sledgehammer
lemma "fact (6::nat) = 720" by auto_sledgehammer
lemma "(2::nat) ^ 10 = 1024" by auto_sledgehammer

text \<open>Non-ground goals still flow through the ordinary backends.\<close>

lemma "(x::nat) + 0 = x" by auto_sledgehammer

end

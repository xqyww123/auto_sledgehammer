theory Auto_Sledgehammer
  imports HOL.Sledgehammer Performant_Isabelle_ML.Performant_Isabelle_ML
begin
(*declare [[ML_debugger, ML_print_depth = 1000, ML_exception_debugger]]*)
named_theorems \<phi>sledgehammer_simps \<open>Simplification rules used before applying slegehammer automation\<close>

text \<open>\<open>NO_SIMP\<close> stops the simplifier from descending into the term it wraps. One constant
  serves both levels: an occurrence under \<open>Trueprop\<close> is object-level, one at the top of a
  \<^typ>\<open>prop\<close> is meta-level. They are told apart by position, never by name.\<close>

definition NO_SIMP where \<open>NO_SIMP (X::'a::{}) \<equiv> X\<close>

lemma NO_SIMP_cong[cong]: \<open>NO_SIMP (X::'a::{}) \<equiv> NO_SIMP X\<close> .
  \<comment> \<open>The sort annotation is load-bearing. Without it \<open>X\<close> takes HOL's default sort, this rule
      stops matching meta-level instances, and nothing reports it -- the tag just quietly
      stops protecting them.\<close>

lemma NO_SIMP_I : \<open>P \<Longrightarrow> NO_SIMP P\<close> unfolding NO_SIMP_def .
lemma NO_SIMP_I': \<open>PROP P \<Longrightarrow> PROP NO_SIMP P\<close> unfolding NO_SIMP_def .

ML_file \<open>library/helpers0.ML\<close>
ML_file \<open>library/Hasher.ML\<close>
ML_file \<open>library/cache_file.ML\<close>
ML_file \<open>library/split.ML\<close>
ML_file \<open>library/looping_simp.ML\<close>
ML_file \<open>library/pre_simproc.ML\<close>

lemma strip_Trueprop_eq: \<open>(Trueprop P \<equiv> Trueprop Q) \<Longrightarrow> P \<equiv> Q\<close>
unfolding atomize_eq
proof rule
  assume A: \<open>Trueprop P \<equiv> Trueprop Q\<close>
     and B: P
  from B[unfolded A]
  show "Q" .
next
  assume A: \<open>Trueprop P \<equiv> Trueprop Q\<close>
     and B: Q
  show "P"
    unfolding A
    using B .
qed

ML_file \<open>library/ground_eval.ML\<close>

ML_file \<open>library/sledgehammer_solver.ML\<close>


(*
lemma \<open>False\<close>
   apply auto_sledg ehammer
 
ML \<open>Proof_Context.facts_of\<close>
ML \<open>Facts.dest_static\<close>
ML \<open>Options.default_int \<^system_option>\<open>sledgehammer_timeout\<close>\<close>

declare [[fast_mepo_max_facts = 10]]
lemma \<open>x + y = z\<close> if "x = (1::nat)" and "y = 2" and "z = 3" and "True" and "x = y"
  by fast_mepo
 
              
lemma \<open>a + b = c\<close> if "a = (2::int)" and "b = 3" and "c = 5"
  by (fast_mepo 1)
*)


end

theory Auto_Sledgehammer
  imports HOL.Sledgehammer Performant_Isabelle_HOL.SSymb
begin
(*declare [[ML_debugger, ML_print_depth = 1000, ML_exception_debugger]]*)
named_theorems φsledgehammer_simps ‹Simplification rules used before applying slegehammer automation›

text ‹‹NO_SIMP› stops the simplifier from descending into the term it wraps. One constant
  serves both levels: an occurrence under ‹Trueprop› is object-level, one at the top of a
  \<^typ>‹prop› is meta-level. They are told apart by position, never by name.›

definition NO_SIMP where ‹NO_SIMP (X::'a::{}) ≡ X›

lemma NO_SIMP_cong[cong]: ‹NO_SIMP (X::'a::{}) ≡ NO_SIMP X› .
  ― ‹The sort annotation is load-bearing. Without it ‹X› takes HOL's default sort, this rule
      stops matching meta-level instances, and nothing reports it -- the tag just quietly
      stops protecting them.›

lemma NO_SIMP_I : ‹P ⟹ NO_SIMP P› unfolding NO_SIMP_def .
lemma NO_SIMP_I': ‹PROP P ⟹ PROP NO_SIMP P› unfolding NO_SIMP_def .

ML_file ‹library/helpers0.ML›
ML_file ‹library/Hasher.ML›
ML_file ‹library/cache_file.ML›
ML_file ‹library/split.ML›
ML_file ‹library/looping_simp.ML›
ML_file ‹library/pre_simproc.ML›

lemma strip_Trueprop_eq: ‹(Trueprop P ≡ Trueprop Q) ⟹ P ≡ Q›
unfolding atomize_eq
proof rule
  assume A: ‹Trueprop P ≡ Trueprop Q›
     and B: P
  from B[unfolded A]
  show "Q" .
next
  assume A: ‹Trueprop P ≡ Trueprop Q›
     and B: Q
  show "P"
    unfolding A
    using B .
qed

ML_file ‹library/ground_eval.ML›

ML_file ‹library/sledgehammer_solver.ML›


(*
lemma ‹False›
   apply auto_sledg ehammer
 
ML ‹Proof_Context.facts_of›
ML ‹Facts.dest_static›
ML ‹Options.default_int \<^system_option>‹sledgehammer_timeout››

declare [[fast_mepo_max_facts = 10]]
lemma ‹x + y = z› if "x = (1::nat)" and "y = 2" and "z = 3" and "True" and "x = y"
  by fast_mepo
 
              
lemma ‹a + b = c› if "a = (2::int)" and "b = 3" and "c = 5"
  by (fast_mepo 1)
*)


end

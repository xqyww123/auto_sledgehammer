theory Auto_Sledgehammer
  imports HOL.Sledgehammer Performant_Isabelle_ML.Performant_Isabelle_ML
begin
declare [[ML_debugger, ML_print_depth = 1000, ML_exception_debugger]]
(* named_theorems φsledgehammer_simps \<open>Simplification rules used before applying slegehammer automation\<close> *)

ML_file \<open>library/helpers0.ML\<close>
ML_file \<open>library/Hasher.ML\<close>
ML_file \<open>library/cache_file.ML\<close>
ML_file \<open>library/split.ML\<close>
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

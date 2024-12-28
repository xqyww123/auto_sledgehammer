theory Auto_Sledgehammer
  imports HOL.Sledgehammer
begin

named_theorems \<phi>sledgehammer_simps \<open>Simplification rules used before applying slegehammer automation\<close>

ML_file \<open>library/helpers0.ML\<close>
ML_file \<open>library/Hasher.ML\<close>
ML_file \<open>library/cache_file.ML\<close>
ML_file \<open>library/sledgehammer_solver.ML\<close>

end
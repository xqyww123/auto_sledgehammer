theory Auto_Sledgehammer
  imports HOL.Sledgehammer
begin

named_theorems \<phi>sledgehammer_simps \<open>Simplification rules used before applying slegehammer automation\<close>

declare [[ML_debugger]]

ML_file \<open>library/helpers0.ML\<close>
ML_file \<open>library/Hasher.ML\<close>
ML_file \<open>library/cache_file.ML\<close>
ML_file \<open>library/sledgehammer_solver.ML\<close>
 
ML \<open> (*TEST*)
let open Phi_Sledgehammer_Solver
    fun assert A B = if A = B then () else error "ASSERTION"
 in assert T_ELIM  (infer_type_of_rule "conjE" @{thm conjE})
  ; assert T_INTRO (infer_type_of_rule "conjI" @{thm conjI})
  ; assert T_SPLIT (infer_type_of_rule "if_split_asm" @{thm if_split_asm})
end \<close>

end
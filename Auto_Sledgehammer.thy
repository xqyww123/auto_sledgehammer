theory Auto_Sledgehammer
  imports HOL.Sledgehammer
begin

(*
named_theorems φsledgehammer_simps ‹Simplification rules used before applying slegehammer automation›
*)

ML_file ‹library/helpers0.ML›
ML_file ‹library/Hasher.ML›
ML_file ‹library/cache_file.ML›
ML_file ‹library/sledgehammer_solver.ML›

end

signature PHI_HELP = sig

val strip_meta_hhf : term -> (string * typ) list (*quantified variables*)
                            * term list (*premises of the antecedent*)
                            * term (*conclusion containing loose bound*)

val leading_antecedent : term -> (string * typ) list (*quantified variables*)
                               * term list (*premises of the antecedent*)
                               * term (*conclusion containing loose bound*)

val leading_antecedent' : thm -> term

end


structure Phi_Help : PHI_HELP = struct

fun strip_meta_hhf term =
  let
    fun strip (V,P) (Const("Pure.imp", _) $ H $ B) = strip (V,H::P) B
      | strip (V,P) (Const("Pure.all", _) $ Abs (a, T, B)) = strip ((a,T)::V,P) B
      | strip (V,P) (\<^Const>\<open>Pure.all ty\<close> $ X) =
          strip (V,P) (\<^Const>\<open>Pure.all ty\<close> $ Abs ("_", ty, Term.incr_boundvars 1 X $ Bound 0))
      | strip (V,P) X = (rev V, rev P, X)
  in strip ([],[]) term end

fun leading_antecedent (Const("Pure.imp", _) $ H $ _) = strip_meta_hhf H
  | leading_antecedent X = raise TERM ("has no antecedent", [X])

fun leading_antecedent' thm = fst (Logic.dest_implies (Thm.prop_of thm))

end

signature PHI_HELP = sig

val strip_meta_hhf : term -> (string * typ) list (*quantified variables*)
                            * term list (*premises of the antecedent*)
                            * term (*conclusion containing loose bound*)

val leading_antecedent : term -> (string * typ) list (*quantified variables*)
                               * term list (*premises of the antecedent*)
                               * term (*conclusion containing loose bound*)

val leading_antecedent' : thm -> term

val quote_space : string -> string
val quote_fact  : string -> string

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

fun has_delimiter s =
  let val N = size s
      val i = Unsynchronized.ref 0
      val ret = Unsynchronized.ref false
   in while !i < N andalso not (!ret) do
        let val c = String.sub (s, !i)
         in if Char.isAlphaNum c orelse
               (case c of #"_" => true | #"'" => true | _ => false)
          then i := !i + 1
          else ret := true
        end
    ; !ret
  end

fun quote_space s = if has_delimiter s then quote s else s
fun quote_fact s =
      if s <> "" andalso
        (has_delimiter s orelse
         not (Char.isAlpha (String.sub (s,0))) )
      then quote s
      else s

end

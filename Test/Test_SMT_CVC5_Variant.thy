theory Test_SMT_CVC5_Variant
  imports Auto_Sledgehammer.Auto_Sledgehammer
begin

section \<open>Unit tests for `mk_proof_candidates`\<close>

text \<open>
  Tests the pure transformation behind the `auto_sledgehammer_try_parallel_smt_cvc5`
  option. `mk_proof_candidates` takes a raw Sledgehammer proof string (as extracted
  from the `dirty_hack` callback) and returns

    \<^item> \<open>is_metis\<close>   — whether the tactic head is `metis`
    \<^item> \<open>metis_prf\<close>  — the canonical proof string preplayed today (same as the
                    pre-refactor `trans` output)
    \<^item> \<open>smt_prf_opt\<close> — the parallel `smt (cvc5) \<dots>` variant (always present
                     when \<open>is_metis\<close> holds; the call site gates on the config)
\<close>

ML \<open>
structure Test_SMT_Variant = struct

fun expect_eq msg expected actual =
  if expected = actual then ()
  else error (msg ^ "\n  expected: [" ^ expected ^ "]\n  actual:   [" ^ actual ^ "]")

fun run_case desc raw_prf
             {is_metis = exp_is_metis, metis_prf = exp_metis, smt_prf_opt = exp_smt} =
  let val {is_metis, metis_prf, smt_prf_opt} =
            Phi_Sledgehammer_Solver.mk_proof_candidates raw_prf
      val _ = if is_metis = exp_is_metis then ()
              else error (desc ^ ": is_metis mismatch \<mdash> expected " ^
                          Bool.toString exp_is_metis ^ ", got " ^ Bool.toString is_metis)
      val _ = expect_eq (desc ^ " / metis_prf") exp_metis metis_prf
      val _ = case (exp_smt, smt_prf_opt) of
                (NONE, NONE) => ()
              | (SOME s, NONE) =>
                  error (desc ^ " / smt_prf_opt: expected SOME [" ^ s ^ "], got NONE")
              | (NONE, SOME s) =>
                  error (desc ^ " / smt_prf_opt: expected NONE, got SOME [" ^ s ^ "]")
              | (SOME e, SOME a) => expect_eq (desc ^ " / smt_prf_opt") e a
   in writeln ("\<checkmark> " ^ desc) end

end
\<close>

subsection \<open>Bare `metis` without facts\<close>

ML \<open>
Test_SMT_Variant.run_case
  "bare metis" "by metis"
  {is_metis = true, metis_prf = "metis", smt_prf_opt = SOME "smt (cvc5) "}
\<close>

subsection \<open>Parenthesized `metis` with facts\<close>

ML \<open>
Test_SMT_Variant.run_case
  "metis foo bar" "by (metis foo bar)"
  {is_metis = true,
   metis_prf     = "( metis foo bar )",
   smt_prf_opt   = SOME "(smt (cvc5) foo bar )"}
\<close>

subsection \<open>`metis` with method options (stripped in smt variant)\<close>

ML \<open>
Test_SMT_Variant.run_case
  "metis (no_types) foo bar" "by (metis (no_types) foo bar)"
  {is_metis = true,
   metis_prf   = "( metis ( no_types ) foo bar )",
   smt_prf_opt = SOME "(smt (cvc5) foo bar )"};

Test_SMT_Variant.run_case
  "metis (no_types, lifting) foo" "by (metis (no_types, lifting) foo)"
  {is_metis = true,
   metis_prf   = "( metis ( no_types , lifting ) foo )",
   smt_prf_opt = SOME "(smt (cvc5) foo )"}
\<close>

subsection \<open>`using \<dots> by metis` produces the `(insert \<dots>)[1], ` prefix\<close>

ML \<open>
Test_SMT_Variant.run_case
  "using x by (metis foo)" "using x by (metis foo)"
  {is_metis = true,
   metis_prf   = "(insert x)[1], ( metis foo )",
   smt_prf_opt = SOME "(insert x)[1], (smt (cvc5) foo )"};

Test_SMT_Variant.run_case
  "using x y by metis" "using x y by metis"
  {is_metis = true,
   metis_prf   = "(insert x y)[1], metis",
   smt_prf_opt = SOME "(insert x y)[1], smt (cvc5) "}
\<close>

subsection \<open>Non-metis tactics never spawn an smt variant\<close>

ML \<open>
Test_SMT_Variant.run_case
  "by simp" "by simp"
  {is_metis = false, metis_prf = "simp", smt_prf_opt = NONE};

Test_SMT_Variant.run_case
  "by blast" "by blast"
  {is_metis = false, metis_prf = "blast", smt_prf_opt = NONE};

Test_SMT_Variant.run_case
  "by auto" "by auto"
  {is_metis = false, metis_prf = "auto", smt_prf_opt = NONE};

Test_SMT_Variant.run_case
  "by (smt (z3) foo)" "by (smt (z3) foo)"
  {is_metis = false,
   metis_prf   = "( smt ( z3 ) foo )",
   smt_prf_opt = NONE}
\<close>

subsection \<open>`apply` is handled the same way as `by`\<close>

ML \<open>
Test_SMT_Variant.run_case
  "apply metis" "apply metis"
  {is_metis = true, metis_prf = "metis", smt_prf_opt = SOME "smt (cvc5) "};

Test_SMT_Variant.run_case
  "apply (metis foo)" "apply (metis foo)"
  {is_metis = true,
   metis_prf   = "( metis foo )",
   smt_prf_opt = SOME "(smt (cvc5) foo )"}
\<close>

ML \<open>writeln "\n=== All mk_proof_candidates tests passed ===\n"\<close>

end

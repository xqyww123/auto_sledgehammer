theory Test_Leading_Subgoal
  imports Auto_Sledgehammer.Auto_Sledgehammer
begin

text \<open>
  \<open>sledgehammer_leading_subgoal\<close> proves the leading subgoal only, and contexts without a local
  theory target count the facts and fixed variables of the background theory as outside the proof.
\<close>

consts P :: "nat \<Rightarrow> bool"

ML \<open>
fun check name b = if b then () else error ("Failed check: " ^ name)
fun subgoals st = Thm.prems_of (#goal (Proof.goal st))
fun show_subgoals st = commas (map (Syntax.string_of_term (Proof.context_of st)) (subgoals st))
\<close>


section \<open>Only the leading subgoal\<close>

text \<open>
  The goal needs no fact, so Sledgehammer's \<open>auto\<close> proves the leading subgoal on any Isabelle2026.
  \<open>P z\<close> is a subgoal that \<open>auto\<close> cannot prove: without the protection, Sledgehammer sees three
  subgoals and Try0 writes \<open>apply auto [2]\<close>, which does not replay inside \<open>[1]\<close>.
\<close>

ML \<open>
local
  val lthy =
    Named_Target.theory_init \<^theory>
    |> Config.put Phi_Sledgehammer_Solver.sledgehammer_params "provers = auto, learn = false"
  val kws = Thy_Header.get_keywords' lthy
  val st3 =
    Proof.theorem NONE (K I) [[(\<^prop>\<open>rev (rev xs) = xs \<and> rev (rev ys) = ys \<and> P z\<close>, [])]] lthy
    |> Phi_Sledgehammer_Solver.eval_prf_str_stat kws 30 NONE "intro conjI" |> snd
  (*rev (rev ys) = ys and P z, as they stand in the state*)
  val rest = tl (subgoals st3)
  fun leaves st = eq_list (op aconv) (subgoals st, rest)
  fun leading hasty =
    Phi_Sledgehammer_Solver.sledgehammer_leading_subgoal NONE Sledgehammer_Fact.no_fact_override
      hasty st3
in
  val _ = check ("three subgoals: " ^ show_subgoals st3) (length (subgoals st3) = 3)

  val _ =
    (case leading false of
      NONE => check "a proof of the leading subgoal" false
    | SOME (text, st') =>
       (check ("the subgoals left: " ^ show_subgoals st') (leaves st');
        check ("the text is scoped: " ^ text) (String.isSuffix ")[1]" text);
        check ("the text replayed on the three subgoals: " ^ text)
          (leaves (snd (Phi_Sledgehammer_Solver.eval_prf_str_stat kws 30 NONE text st3)))))

  val _ =
    (case leading true of
      NONE => check "hasty: a result" false
    | SOME (text, st') =>
       (check ("hasty: the text " ^ text) (text = "<cheat>");
        check ("hasty: the subgoals left: " ^ show_subgoals st') (leaves st')))
end
\<close>


section \<open>Contexts without a local theory target\<close>

ML \<open>
local
  val bare = \<^context>
  val lthy = Named_Target.theory_init \<^theory>
  fun local_names ctxt =
    map (fn ((name, _), _) => name ()) (Phi_Sledgehammer_Solver.facts_as_mepo_lazy_facts true ctxt)
  fun with_H ctxt =
    snd (Proof_Context.note_thms "" ((Binding.name "H", []), [(@{thms TrueI}, [])]) ctxt)
  fun with_y ctxt = snd (Variable.add_fixes ["y"] ctxt)
  val inserted = Phi_Sledgehammer_Solver.should_be_inserted
  fun checks label ctxt =
    (check (label ^ ": no local facts: " ^ commas (take 3 (local_names ctxt)))
      (null (local_names ctxt));
     check (label ^ ": exactly the local fact H: " ^ commas (take 3 (local_names (with_H ctxt))))
      (local_names (with_H ctxt) = ["H"]);
     check (label ^ ": an unfixed variable is not new") (not (inserted ctxt \<^prop>\<open>P y\<close>));
     check (label ^ ": a fixed variable is new") (inserted (with_y ctxt) \<^prop>\<open>P y\<close>))
in
  val _ = check "the theory's context has no target" (Local_Theory.level bare = 0)
  val _ = checks "no target" bare
  val _ = checks "local theory" lthy
end
\<close>

end

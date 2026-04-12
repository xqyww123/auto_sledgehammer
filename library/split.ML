(*  Title:      Auto_Sledgehammer/library/split.ML
    Author:     Qiyuan Xu (with AI assistance)

Smart case-splitting looper that auto-discovers split rules from Ctr_Sugar
metadata and applies them conservatively, avoiding goal explosion.
*)

signature SMART_SPLIT =
sig
  val smart_split_tac: Proof.context -> int -> tactic
  val add_smart_split: Proof.context -> Proof.context
end

structure Smart_Split : SMART_SPLIT =
struct

(* Scan a term for case constants, look up split rules via Ctr_Sugar.
   Returns (split_thm, branch_count) pairs, deduplicated. *)
fun discover_splits ctxt t =
  let
    fun scan (Abs (_, _, body)) acc = scan body acc
      | scan (f $ x) acc = scan x (scan f acc)
      | scan (Const (c, _)) acc =
          (case Ctr_Sugar.ctr_sugar_of_case ctxt c of
            SOME {split, ctrs, ...} =>
              if exists (fn (th, _) => Thm.eq_thm_prop (th, split)) acc then acc
              else (split, length ctrs) :: acc
          | NONE => acc)
      | scan _ acc = acc
  in scan t [] end

val max_total_branches = 16

fun smart_split_tac ctxt = SUBGOAL (fn (goal, i) =>
  let
    val concl = Logic.strip_assums_concl goal
    val candidates = discover_splits ctxt concl
    val total = fold (fn (_, n) => fn acc => acc * n) candidates 1
  in
    if null candidates then no_tac
    else
      let val thms =
            if total <= max_total_branches then map fst candidates
            else [fst (hd (sort (int_ord o apply2 snd) candidates))]
      in CHANGED (Splitter.split_tac ctxt thms i) end
  end)

fun add_smart_split ctxt =
  ctxt addloop ("smart_split", smart_split_tac)

val _ = Theory.setup
  (Method.setup \<^binding>\<open>auto_split\<close>
    (Scan.lift (Scan.option (Parse.nat -- Parse.nat)) --|
      Method.sections Clasimp.clasimp_modifiers >>
     (fn NONE => SIMPLE_METHOD o CHANGED_PROP o Clasimp.auto_tac o add_smart_split
       | SOME (m, n) => fn ctxt =>
           SIMPLE_METHOD (CHANGED_PROP (Clasimp.mk_auto_tac (add_smart_split ctxt) m n))))
    "auto with smart case splitting" #>
  Method.setup \<^binding>\<open>clarsimp_split\<close>
    (Method.sections Clasimp.clasimp_modifiers >>
      K (SIMPLE_METHOD' o (CHANGED_PROP oo Clasimp.clarsimp_tac) o add_smart_split))
    "clarsimp with smart case splitting")

end

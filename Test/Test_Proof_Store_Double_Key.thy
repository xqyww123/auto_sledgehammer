theory Test_Proof_Store_Double_Key
  imports Auto_Sledgehammer.Auto_Sledgehammer
begin

text \<open>
  The proof store's two keys: the proof id and the goal hash.  Numbered as in
  ai-artifacts/PROOF_STORE_DOUBLE_KEY_PLAN.md section 4.  Every assertion that
  scans the store file is deliberate: the write funnel skips silently on an
  unwritable directory, and a test that only asks memory would pass vacuously.
\<close>

declare [[enable_proof_store = true]]

ML \<open>
structure F = Proof_Store_Format
structure S = Phi_Proof_Store

val thy = \<^theory>
val ctxt = \<^context>
val path = S.store_path thy

fun frames () = if File.is_file path then F.scan (Bytes.content (Bytes.read path)) else []
fun puts_of id =
  map_filter (fn F.PUT (r as {id = id', ...}) => if id' = id then SOME r else NONE | _ => NONE)
             (frames ())
fun tombs_of id = length (filter (fn F.TOMB i => i = id | _ => false) (frames ()))
fun assert b msg = if b then () else error ("FAIL: " ^ msg)

val t1 = Time.fromMilliseconds 100
val t2 = Time.fromMilliseconds 200
fun digest s = Hasher.string s

(*the pre-hash frame layout, as an old binary wrote it*)
fun tag1_payload (id, time_ms, proof) =
  let val outs = BytesIO.mkOutstream ()
   in MessagePackBytesIO.Pack.packPair
        (MessagePackBytesIO.Pack.packInt,
         MessagePackBytesIO.Pack.packTuple3
           (MessagePackBytesIO.Pack.packString, MessagePackBytesIO.Pack.packInt,
            MessagePackBytesIO.Pack.packString))
        (1, (id, time_ms, proof)) outs;
      BytesIO.toString outs
  end
\<close>

section \<open>Format layer: tests 1-3\<close>

ML \<open>
(*1: tag 3 round trip at both ends of the digest range, and without a hash*)
val _ = List.app (fn r =>
          (assert (F.decode_record (F.encode_record r) = r) "test1 round trip";
           assert (String.sub (F.encode_record r, 1) = Char.chr 3) "test1 tag byte"))
        [F.PUT {id = "a", hash = SOME 0w0, time_ms = 5, proof = "p"},
         F.PUT {id = "a", hash = SOME (Word64.notb 0w0), time_ms = 5, proof = "p"},
         F.PUT {id = "a", hash = NONE, time_ms = 5, proof = "p"}]

(*2: a tag 1 payload decodes to a record without a hash*)
val _ = assert (F.decode_record (tag1_payload ("x", 7, "q"))
                = F.PUT {id = "x", hash = NONE, time_ms = 7, proof = "q"}) "test2 tag 1"

(*3: a mixed buffer scans in file order*)
val r3 = F.PUT {id = "y", hash = SOME (digest "y"), time_ms = 9, proof = "r"}
val _ = assert (F.scan (F.frame (tag1_payload ("x", 7, "q"))
                        ^ F.frame (F.encode_record r3)
                        ^ F.encode_tombstone "x")
                = [F.PUT {id = "x", hash = NONE, time_ms = 7, proof = "q"}, r3, F.TOMB "x"]) "test3 scan"
\<close>

section \<open>Store layer: tests 4-15\<close>

ML \<open>
val _ = S.invalidate_store thy
val hA = digest "goal A"

(*4: the frame on disk carries the hash*)
val _ = S.update_cached_proof thy {id = "k1", hash = SOME hA} (t1, "pA")
val _ = assert (map #hash (puts_of "k1") = [SOME hA]) "test4 disk"

(*5: both keys hit the same record*)
val _ = assert (S.get_cached_proof thy "k1" = SOME (t1, "pA")) "test5 id"
val _ = assert (S.get_cached_proof_by_hash thy hA = SOME (t1, "pA")) "test5 hash"

(*6: a tombstone retires the id only*)
val _ = S.invalidate_proof_cache false "k1" thy
val _ = assert (S.get_cached_proof thy "k1" = NONE) "test6 id"
val _ = assert (S.get_cached_proof_by_hash thy hA = SOME (t1, "pA")) "test6 hash"

(*7: the hash entry survives a reload while the PUT frame is in the file, and
     goes with compaction*)
val _ = S.force_reload thy
val _ = assert (S.get_cached_proof_by_hash thy hA = SOME (t1, "pA")) "test7 reload"
val _ = S.compact_and_store thy
val _ = assert (null (puts_of "k1") andalso tombs_of "k1" = 0) "test7 compacted"
val _ = S.force_reload thy
val _ = assert (S.get_cached_proof_by_hash thy hA = NONE) "test7 after compaction"

(*8: compaction keeps the hash field; 9: a record without one is reachable by id*)
val hB = digest "goal B"
val _ = S.update_cached_proof thy {id = "k2", hash = SOME hB} (t1, "pB")
val _ = S.update_cached_proof thy {id = "k3", hash = NONE} (t1, "pC")
val _ = S.compact_and_store thy
val _ = assert (map #hash (puts_of "k2") = [SOME hB] andalso map #hash (puts_of "k3") = [NONE]) "test8 disk"
val _ = S.force_reload thy
val _ = assert (S.get_cached_proof_by_hash thy hB = SOME (t1, "pB")) "test8 reload"
val _ = assert (S.get_cached_proof thy "k3" = SOME (t1, "pC")) "test9 id"

(*10: one hash, two ids: the later write wins*)
val hC = digest "goal C"
val _ = S.update_cached_proof thy {id = "kA", hash = SOME hC} (t1, "pA1")
val _ = S.update_cached_proof thy {id = "kB", hash = SOME hC} (t1, "pB1")
val _ = assert (S.get_cached_proof_by_hash thy hC = SOME (t1, "pB1")) "test10"

(*11: one id, one text, two hashes and two times: both hash entries stay*)
val hD = digest "goal D"
val hD' = digest "goal D'"
val n11 = length (frames ())
val _ = S.update_cached_proof thy {id = "kD", hash = SOME hD} (t1, "pD")
val _ = S.update_cached_proof thy {id = "kD", hash = SOME hD'} (t2, "pD")
val _ = assert (S.get_cached_proof_by_hash thy hD' = SOME (t2, "pD")) "test11 h'"
val _ = assert (S.get_cached_proof_by_hash thy hD = SOME (t1, "pD")) "test11 h"
val _ = assert (length (frames ()) = n11 + 2) "test11 two frames"

(*12: the identical write is short-circuited*)
val _ = S.update_cached_proof thy {id = "kD", hash = SOME hD'} (t2, "pD")
val _ = assert (length (frames ()) = n11 + 2) "test12 no frame"

(*13: 10 and 11 hold after a reload*)
val _ = S.force_reload thy
val _ = assert (S.get_cached_proof_by_hash thy hC = SOME (t1, "pB1")) "test13 a"
val _ = assert (S.get_cached_proof_by_hash thy hD' = SOME (t2, "pD")
                andalso S.get_cached_proof_by_hash thy hD = SOME (t1, "pD")) "test13 b"
\<close>

ML \<open>
(*14: a hand-built file with a tag 1 frame, end to end*)
val _ = S.invalidate_store thy
val hE = digest "goal E"
val _ = File.write path
          (F.frame (tag1_payload ("x", 100, "px"))
           ^ F.encode_put {id = "a", hash = SOME hE, time_ms = 100, proof = "pa"}
           ^ F.encode_tombstone "a")
val _ = S.force_reload thy
val _ = assert (S.get_cached_proof thy "x" = SOME (t1, "px")) "test14 x by id"
val _ = assert (S.get_cached_proof thy "a" = NONE) "test14 a tombstoned"
val _ = assert (S.get_cached_proof_by_hash thy hE = SOME (t1, "pa")) "test14 h"
val _ = S.compact_and_store thy
val _ = assert (map #hash (puts_of "x") = [NONE] andalso null (puts_of "a") andalso tombs_of "a" = 0)
               "test14 compacted"
val _ = S.force_reload thy
val _ = assert (S.get_cached_proof thy "x" = SOME (t1, "px")
                andalso S.get_cached_proof_by_hash thy hE = NONE) "test14 reload"

(*15: forgetting a hash touches neither the id nor the file*)
val hF = digest "goal F"
val _ = S.update_cached_proof thy {id = "kF", hash = SOME hF} (t1, "pF")
val n15 = length (frames ())
val _ = S.invalidate_proof_cache_by_hash hF thy
val _ = assert (S.get_cached_proof_by_hash thy hF = NONE) "test15 hash gone"
val _ = assert (S.get_cached_proof thy "kF" = SOME (t1, "pF")) "test15 id stays"
val _ = assert (length (frames ()) = n15) "test15 no frame"
\<close>

section \<open>Through \<open>auto\<close> and \<open>all_auto\<close>: tests 16-19b\<close>

text \<open>Each block below empties the store first, so that it holds under a
  partial re-evaluation as much as under a fresh one.\<close>

ML \<open>
structure Solver = Phi_Sledgehammer_Solver

fun goal_of s = Goal.init (Thm.cterm_of ctxt (Syntax.read_prop ctxt s))
fun opts pid w =
  {improved = true, async_mode = Solver.Sync,
   fact_override = Sledgehammer_Fact.no_fact_override, proof_id = pid,
   timeout = NONE, read_store = SOME true, write_store = SOME w} : Solver.options
fun run_auto pid w st =
  let val (fut, st') = Solver.auto (opts pid w) ctxt st in (Future.join fut, st') end
\<close>

ML \<open>
val _ = S.invalidate_store thy
(*16: a hash hit that fails to replay writes no tombstone; the search result
     then overwrites the forgotten hash entry*)
val g16 = goal_of "(x::nat) + 0 = x"
val h16 = Hasher.goal_at 1 (ctxt, g16)
val _ = S.update_cached_proof thy {id = "other16", hash = SOME h16} (t1, "(fail)[1]")
val (txt16, st16) = run_auto (SOME "K16") true g16
val _ = assert (Thm.no_prems st16) "test16 solved"
val _ = assert (tombs_of "K16" = 0 andalso tombs_of "other16" = 0) "test16 no tombstone"
val _ = assert (length (puts_of "other16") = 1) "test16 record kept"
val _ = assert (Option.map snd (S.get_cached_proof_by_hash thy h16) = SOME txt16) "test16 overwritten"
\<close>

ML \<open>
val _ = S.invalidate_store thy
(*17: the id fails (tombstone), the same record is not replayed again under
     the hash and is forgotten; write_store off, so no PUT follows*)
val g17 = goal_of "(y::nat) * 1 = y"
val h17 = Hasher.goal_at 1 (ctxt, g17)
val _ = S.update_cached_proof thy {id = "K17", hash = SOME h17} (t1, "(fail)[1]")
val (_, st17) = run_auto (SOME "K17") false g17
val _ = assert (Thm.no_prems st17) "test17 solved"
val _ = assert (tombs_of "K17" = 1 andalso length (puts_of "K17") = 1) "test17 tombstone, no PUT"
val _ = assert (S.get_cached_proof thy "K17" = NONE) "test17 id gone"
val _ = assert (S.get_cached_proof_by_hash thy h17 = NONE) "test17 hash gone"
\<close>

ML \<open>
val _ = S.invalidate_store thy
(*18: the cascade.  K18a holds G1's proof; G0 arrives under K18a, fails, is
     tombstoned; then G1 arrives under K18b and gets its proof back by hash.*)
val g18a = goal_of "(z::nat) + 0 = z"
val g18b = goal_of "rev (rev (xs::nat list)) = xs"
val p18 = "(rule rev_rev_ident)[1]"
val h18b = Hasher.goal_at 1 (ctxt, g18b)
val _ = S.update_cached_proof thy {id = "K18a", hash = SOME h18b} (t1, p18)
val (_, st18a) = run_auto (SOME "K18a") true g18a
val _ = assert (Thm.no_prems st18a andalso tombs_of "K18a" = 1) "test18 first call"
val (txt18, st18b) = run_auto (SOME "K18b") true g18b
val _ = assert (txt18 = p18 andalso Thm.no_prems st18b) "test18 verbatim"
val _ = assert (map #hash (puts_of "K18b") = [SOME h18b] andalso tombs_of "K18b" = 0) "test18 promoted"
\<close>

ML \<open>
val _ = S.invalidate_store thy
(*19: the skip rule must not fire on a DIFFERENT record*)
val g19 = goal_of "rev (rev (ys::nat list)) = ys"
val h19 = Hasher.goal_at 1 (ctxt, g19)
val p19 = "(rule rev_rev_ident)[1]"
val _ = S.update_cached_proof thy {id = "K19", hash = NONE} (t1, "(fail)[1]")
val _ = S.update_cached_proof thy {id = "other19", hash = SOME h19} (t1, p19)
(*the promotion rewrites K19 with another text: the collision guard warns, as it should*)
val (txt19, st19) = run_auto (SOME "K19") true g19
val _ = assert (txt19 = p19 andalso Thm.no_prems st19) "test19 verbatim"
val _ = assert (tombs_of "K19" = 1 andalso map #hash (puts_of "K19") = [NONE, SOME h19]) "test19 frames"
val _ = S.force_reload thy
val _ = assert (Option.map snd (S.get_cached_proof thy "K19") = SOME p19) "test19 reload"
\<close>

ML \<open>
val _ = S.invalidate_store thy
(*19b: all_auto replays under k = nprem: a two-subgoal state, a two-part text.
     The context is taken afresh: the state is built from a theorem of THIS
     theory stage, and the earlier context belongs to an earlier one.*)
val ctxt = \<^context>
val g19b =
  Goal.init (Thm.cterm_of ctxt (Syntax.read_prop ctxt "(u::nat) + 0 = u & rev (rev (vs::nat list)) = vs"))
  |> resolve_tac ctxt @{thms conjI} 1 |> Seq.hd
val _ = assert (Thm.nprems_of g19b = 2) "test19b two subgoals"
val h19b = Hasher.all_goals (ctxt, g19b)
val p19b = "((rule add_0_right)[1], (rule rev_rev_ident)[1])"
val _ = S.update_cached_proof thy {id = "other19b", hash = SOME h19b} (t1, p19b)
val n19b = length (frames ())
val (fut19b, st19b) = Solver.all_auto (opts (SOME "K19b") false) ctxt g19b
val (_, txt19b) = Future.join fut19b
val _ = assert (txt19b = p19b) "test19b verbatim"
val _ = assert (Thm.no_prems st19b) "test19b closed"
val _ = assert (length (frames ()) = n19b) "test19b no frame"
\<close>

end

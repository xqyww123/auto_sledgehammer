(* Building the Proof Store *)

(* ===========================================================================
   Proof store on-disk format: a crash-robust, multi-process-safe append log.

   The file is a sequence of self-delimited frames:

     [ magic : u32 BE = 0x6ABCDEF6 ][ len : u32 BE ][ crc32 : u32 BE ][ payload : len bytes ]

   crc32 is the standard IEEE 802.3 CRC-32 over (be32 len ++ payload).
   payload is a MessagePack-encoded record, tagged by its first element:

     PUT {id, hash, time_ms, proof}  <->  (3, (id, hash | nil, time_ms, proof))
     TOMB id                         <->  (2, id)
     (1, (id, time_ms, proof))         --  the pre-hash PUT.  Decoded forever,
                                           never written: proofstore-merge.sh
                                           splices frames from old branches in.

   hash is the goal digest (Hasher.digest, a 64-bit word) or nil for a record
   that was stored without one.  Decoding is what migrates: a tag-1 frame and a
   tag-3 frame with a nil hash decode to the same record.

   Reading scans for the magic, validates the crc and that len fits, and yields
   the records in file order; folding them into tables is the store's business
   (its `replay`).
   A torn/half-written trailing frame, or a magic byte-sequence that happens
   to occur inside a payload, fails the crc check and the scanner resynchronises
   at the next magic occurrence -- so a crash never corrupts earlier records and
   never causes a wrong record to be accepted (beyond the 2^-32 crc collision).

   MessagePack comes from the Performant_Isabelle_ML base session (mlmsgpack).
   This structure is deliberately exposed (no signature ascription) so the
   format can be unit-tested directly.
   =========================================================================== *)
structure Proof_Store_Format = struct

val magic_word = 0wx6ABCDEF6 : Word32.word

(* big-endian u32 as a 4-byte string *)
fun be32 (w : Word32.word) : string =
  let fun byte k = Char.chr (Word32.toInt (Word32.andb (Word32.>> (w, Word.fromInt (8 * k)), 0wxFF)))
   in String.implode [byte 3, byte 2, byte 1, byte 0] end

(* read big-endian u32 from string s at offset i *)
fun rd_be32 (s, i) =
  let fun b k = Word32.fromInt (Char.ord (String.sub (s, i + k)))
   in Word32.orb (Word32.<< (b 0, 0w24),
       Word32.orb (Word32.<< (b 1, 0w16),
        Word32.orb (Word32.<< (b 2, 0w8), b 3))) end

val MAGIC = be32 magic_word
val magic0 = String.sub (MAGIC, 0)

local
  val crc_table : Word32.word Vector.vector =
    Vector.tabulate (256, fn n =>
      let fun loop (c, 0) = c
            | loop (c, k) =
                loop (if Word32.andb (c, 0w1) = 0w1
                      then Word32.xorb (0wxEDB88320, Word32.>> (c, 0w1))
                      else Word32.>> (c, 0w1), k - 1)
       in loop (Word32.fromInt n, 8) end)
in
fun crc32 (s : string) : Word32.word =
  Word32.xorb (
    Word8Vector.foldl (fn (b, c) =>
        Word32.xorb (Word32.>> (c, 0w8),
          Vector.sub (crc_table,
            Word32.toInt (Word32.andb (Word32.xorb (c, Word32.fromInt (Word8.toInt b)), 0wxFF)))))
      0wxFFFFFFFF (Byte.stringToBytes s),
    0wxFFFFFFFF)
end

datatype record =
    PUT of {id: string, hash: Hasher.digest option, time_ms: int, proof: string}
  | TOMB of string

local
  structure P = MessagePackBytesIO.Pack
  structure U = MessagePackBytesIO.Unpack
  val put_packer =
    P.packPair (P.packInt, P.packTuple4 (P.packString, P.packOption P.packWord64, P.packInt, P.packString))
  val tomb_packer = P.packPair (P.packInt, P.packString)
  fun put (id, hash, time_ms, proof) = PUT {id = id, hash = hash, time_ms = time_ms, proof = proof}
  val rec_unpacker =
    U.unpackPair_dep' U.unpackInt (fn tag =>
      if tag = 3 then U.>> (U.unpackTuple4 (U.unpackString, U.unpackOption U.unpackWord64,
                                            U.unpackInt, U.unpackString), put)
      else if tag = 2 then U.>> (U.unpackString, TOMB)
      else if tag = 1 then U.>> (U.unpackTuple3 (U.unpackString, U.unpackInt, U.unpackString),
                                 fn (id, time_ms, proof) => put (id, NONE, time_ms, proof))
      else raise U.Unpack)
in
fun encode_record r =
  let val outs = BytesIO.mkOutstream ()
   in (case r of PUT {id, hash, time_ms, proof} => put_packer (3, (id, hash, time_ms, proof)) outs
               | TOMB id => tomb_packer (2, id) outs);
      BytesIO.toString outs
  end
fun decode_record payload = #1 (U.doUnpack rec_unpacker (BytesIO.fromString payload))
end

fun frame payload =
  let val len_bytes = be32 (Word32.fromInt (size payload))
   in MAGIC ^ len_bytes ^ be32 (crc32 (len_bytes ^ payload)) ^ payload end

fun encode_put r = frame (encode_record (PUT r))
fun encode_tombstone id = frame (encode_record (TOMB id))

fun is_new_format raw = size raw >= 4 andalso String.substring (raw, 0, 4) = MAGIC

(* first index >= i at which the 4-byte magic occurs; NONE if none *)
fun find_magic (s, i) =
  let val n = size s
      fun go j =
        if j + 4 > n then NONE
        else if String.sub (s, j) = magic0 andalso String.substring (s, j, 4) = MAGIC
        then SOME j else go (j + 1)
   in go i end

(* scan a whole buffer into the list of records, in file order *)
fun scan s =
  let val n = size s
      fun loop i acc =
        case find_magic (s, i) of
          NONE => rev acc
        | SOME m =>
            if m + 12 > n then rev acc                          (* truncated header at EOF *)
            else
              let val len = Word32.toInt (rd_be32 (s, m + 4))
                  val crc = rd_be32 (s, m + 8)
               in if m + 12 + len > n then loop (m + 1) acc      (* len overruns: false/torn *)
                  (* crc scope is (len_bytes ++ payload); the crc field at m+8 sits
                     between them on disk, so reconstruct it skipping bytes m+8..m+11 *)
                  else if crc32 (String.substring (s, m + 4, 4) ^ String.substring (s, m + 12, len)) <> crc
                  then loop (m + 1) acc                          (* crc mismatch: false/torn *)
                  else (case Exn.capture decode_record (String.substring (s, m + 12, len)) of
                          Exn.Res r => loop (m + 12 + len) (r :: acc)
                        | Exn.Exn _ => loop (m + 12 + len) acc)  (* framed but undecodable: skip *)
              end
   in loop 0 [] end

end


signature PHI_PROOF_STORE = sig

type proof_id = string
type proof_cache = Time.time * string

(*A record has two keys: its proof id, under which it is stored, and
  optionally the digest of the goal it proved.  `proofs` is the file's live
  set, keyed by id.  `by_hash` is the second index: goal digest -> (time, text)
  of the most recent write carrying that digest that was not short-circuited
  by update_cached_proof.  Which record that is when several ids share a
  digest is deliberately unspecified; every by-hash hit is replay-verified
  before use.  It lives in memory only, is rebuilt from the file's frames on
  load (tombstoned records included), and is insert-only except for
  invalidate_proof_cache_by_hash.  See ai-artifacts/PROOF_STORE_DOUBLE_KEY_PLAN.md.*)
type proof_record = {hash: Hasher.digest option, time: Time.time, proof: string}
type store = {proofs: proof_record Symtab.table,
              by_hash: proof_cache Hasher.Tab.table,
              async_tasks: Task_Queue.task list}

(*Where this theory's store file lives.  Exported because user-facing messages
  name that path, and the naming convention must have exactly one source.*)
val store_path : theory -> Path.T

val get_store : theory -> store
val force_reload : theory -> store
val register_async_task : Task_Queue.task -> theory -> unit

val compact_and_store : theory -> unit
val close_store : theory -> unit
val invalidate_store : theory -> unit
(* val check_cache : string (*Document_ID*) -> Proof.context -> unit *)
val report_cache_is_outdated : bool (*whether warn*) -> theory -> unit

(*Each key fails on its own: a record that does not replay under its id is
  tombstoned (invalidate_proof_cache: the id is gone, the digest entry stays --
  the text is still a proof of that goal), a by_hash entry that does not replay
  is forgotten in memory only (invalidate_proof_cache_by_hash: no frame, the
  file is untouched).*)
val get_cached_proof : theory -> proof_id -> proof_cache option
val get_cached_proof_by_hash : theory -> Hasher.digest -> proof_cache option
val update_cached_proof : theory -> {id: proof_id, hash: Hasher.digest option} -> proof_cache -> unit
val invalidate_proof_cache : bool (*whether warn*) -> proof_id -> theory -> unit
val invalidate_proof_cache_by_hash : Hasher.digest -> theory -> unit

type proof = string

(*Budget for replaying a cached proof: the time recorded when it was found, plus
  slack for a machine that is busier now than it was then.  Overrunning it
  invalidates the entry and re-searches the proof from scratch.

  The result is a NOMINAL time handed to Timeout.apply, which multiplies this
  machine's timeout_scale in itself -- so never multiply the factor in here.*)
val tolerant_time : Time.time -> Time.time

(*The write-side counterpart: divide a measured elapsed time by this machine's
  timeout_scale, so what lands in the store is standard-machine time and a slow
  machine does not hand every other machine an inflated replay budget.  Every
  write point must pass its measurement through this before storing it.*)
val standard_time : Time.time -> Time.time

val try_cached_proof_by_hash :
         (Time.time -> proof -> context_state -> context_state option) (*evaluator*)
      -> (string option (*original cached proof*) -> (Time.time * proof) * context_state)
      -> context_state
      -> (Time.time * proof) * context_state

(*Variant keyed by Hasher.goal_at i — caches a per-subgoal proof.
  Use i = 0 to mean "the whole sequent";
  use i >= 1 to key on the i-th subgoal in isolation.*)
val try_cached_proof_by_hash_at :
         int (*subgoal index, 0 = whole sequent*)
      -> (Time.time -> proof -> context_state -> context_state option) (*evaluator*)
      -> (string option (*original cached proof*) -> (Time.time * proof) * context_state)
      -> context_state
      -> (Time.time * proof) * context_state

val enable_proof_store : bool Config.T

end


structure Phi_Proof_Store : PHI_PROOF_STORE = struct

val enable_proof_store = Attrib.setup_config_bool \<^binding>\<open>enable_proof_store\<close> (K true)

type proof_id = string
type proof_cache = Time.time * string
type proof_record = {hash: Hasher.digest option, time: Time.time, proof: string}
type store = {proofs: proof_record Symtab.table,
              by_hash: proof_cache Hasher.Tab.table,
              async_tasks: Task_Queue.task list}

val empty_store = {proofs = Symtab.empty, by_hash = Hasher.Tab.empty, async_tasks = []} : store

open Proof_Store_Format  (*MAGIC, crc32, frame, scan, encode_put, encode_tombstone, ...*)

(*The only writers of `proofs` and `by_hash`.  A write overwrites the digest
  entry but never deletes the superseded one (that text still proves its own
  goal); a tombstone leaves `by_hash` alone.  Deleting there on a tombstone
  cascades: when an obligation is inserted ahead of n others, every one of
  them fails under its shifted id and would delete the very entry its
  successor is about to look up.  Hence the single deletion is
  store_forget_hash, reached only when a by_hash hit itself failed to replay.*)
fun store_update_proof (id, r : proof_record) ({proofs, by_hash, async_tasks}:store)
      = {proofs = Symtab.update (id, r) proofs,
         by_hash = (case #hash r of
                      SOME h => Hasher.Tab.update (h, (#time r, #proof r)) by_hash
                    | NONE => by_hash),
         async_tasks = async_tasks} : store

(*Dropping async_tasks here predates the second key and its reason is not
  recorded; the effect is that Theory.at_end then sees no registered task and
  compacts at once instead of deferring.  Kept as it was: a separate question.*)
fun store_invalidate_proof id ({proofs, by_hash, ...}:store)
      = {proofs = Symtab.delete_safe id proofs, by_hash = by_hash, async_tasks = []} : store

fun store_forget_hash h ({proofs, by_hash, async_tasks}:store)
      = {proofs = proofs, by_hash = Hasher.Tab.delete_safe h by_hash, async_tasks = async_tasks} : store

fun store_add_async task ({proofs, by_hash, async_tasks}:store)
      = {proofs = proofs, by_hash = by_hash, async_tasks = task :: async_tasks} : store

(*Fold a file's records, in file order, into a store: last write wins, TOMB
  deletes the id.  Total by construction -- a raise here would let compact_store
  rewrite the file from a half-built table.*)
fun replay records =
  fold (fn PUT {id, hash, time_ms, proof} =>
             store_update_proof (id, {hash = hash, time = Time.fromMilliseconds time_ms, proof = proof})
         | TOMB id => store_invalidate_proof id)
       records empty_store

(*The one conversion from a live record back to a frame.*)
fun put_frame id ({hash, time, proof} : proof_record) =
  encode_put {id = id, hash = hash, time_ms = Time.toMilliseconds time, proof = proof}

fun store_base thy =
      Path.append (Resources.master_directory thy) (Path.basic (Context.theory_name {long=false} thy))

fun store_path thy = Path.ext "proof-store" (store_base thy)

(* The pre-rename file name.  Only ever READ, and only by migrate_legacy on the
   first touch of a theory's store; nothing appends to it again. *)
fun legacy_cache_path thy = Path.ext "proof-cache" (store_base thy)

fun lock_path thy = Path.ext "lock" (store_path thy)   (* <thy>.proof-store.lock *)

(* Whether the cache location admits the writes this module performs: creating
   the lock file and the compaction temp file, appending to the data file,
   unlinking it. Probed with access(2) -- Isabelle's File structure has no
   writability predicate (Pure/General/file.ML), File.exists answers existence
   only.

   access(2) answers false for a path that does not exist, so the DIRECTORY is
   the thing to probe for the create case; the files are probed only when they
   are already there. A read-only data file matters even under a writable
   directory: File.append would fail while File.rm would SUCCEED (unlink needs
   only directory permission) -- and silently deleting a deliberately read-only
   cache is worse than not writing at all. The lock file is probed separately
   because with_file_lock opens it O_RDWR even when it already exists. *)
fun accessible path modes =
  \<^try>\<open>OS.FileSys.access (File.platform_path path, modes) catch _ => false\<close>

fun probe_writable thy =
  let val dir = Resources.master_directory thy
      val data = store_path thy
      val lock = lock_path thy
   in File.is_dir dir andalso
      accessible dir [OS.FileSys.A_WRITE, OS.FileSys.A_EXEC] andalso
      (not (File.exists data) orelse accessible data [OS.FileSys.A_WRITE]) andalso
      (not (File.exists lock) orelse accessible lock [OS.FileSys.A_WRITE])
  end

(* Read the store from a new-format file. Any non-new-format or corrupt file
   is treated as empty -- there is NO backward compatibility with the pre-frame
   format; old caches are discarded. Best-effort: a scan failure degrades to
   empty, and so does an unreadable file -- a cache primed by another user
   under a tight umask would otherwise raise EACCES from Bytes.read straight
   into the user's proof (the read happens before any write, so the
   writability probe cannot help).

   TWO readers, deliberately, because there are two callers with OPPOSITE needs.

   `read_file_state_exn` lets an I/O failure escape, and is what compaction must
   use: `compact_store` feeds this result straight back to `write_state_new`, so
   a reader that degrades to `empty_store` there does not degrade -- it TRUNCATES
   the user's cache to nothing and renames the empty payload over it.  Letting the
   exception out instead aborts the rewrite with the file byte-intact, and
   `compact_store`'s own handler demotes the verdict.  Triggers are not only
   permissions: EIO, an NFS ESTALE, EMFILE under a parallel build, or Size on a
   large cache all raise here from an ordinary mode-0644 file.

   `read_file_state` degrades, and is what the pure read path uses.

   In BOTH, a scan failure still discards: a corrupt or truncated file is
   treated as empty, which is the pre-existing contract and is unchanged.  The
   catch-all wraps `scan` only.  `replay` is total, so a raise from it is a bug
   and must abort compaction rather than be turned into an empty table. *)
fun read_file_state_exn path =
  if not (File.is_file path) then empty_store
  else
    let val raw = Bytes.content (Bytes.read path)   (* I/O failure escapes, by design *)
     in if is_new_format raw
        then replay (\<^try>\<open>scan raw catch _ => []\<close>)
        else empty_store
    end

fun read_file_state path =
  \<^try>\<open>read_file_state_exn path catch _ => empty_store\<close>

(* process id, used to make the compaction temp file unique across processes *)
val proc_pid = SysWord.toString (Posix.Process.pidToWord (Posix.ProcEnv.getpid ()))

(* Atomically write the live records as a fresh new-format file (tmp + rename).
   The temp file name carries the pid so two processes compacting the same
   theory never write the same temp path (they are already serialised by the
   fcntl lock, but a unique name removes that dependence). File.write neither
   unlinks nor truncates back on failure, so a failed rename (or a mid-write
   ENOSPC) would orphan the temp file; unlink it and rethrow, leaving the
   verdict to the caller's guard. *)
fun write_state_new path (proofs : proof_record Symtab.table) =
  let val payload =
        String.concat (Symtab.fold (fn (id, r) => fn acc => put_frame id r :: acc) proofs [])
      val tmp = Path.ext ("tmp." ^ proc_pid) path
   in \<^try>\<open>
        (File.write tmp payload;
         OS.FileSys.rename {old = File.platform_path tmp, new = File.platform_path path})
        catch exn => (\<^try>\<open>File.rm tmp\<close>; Exn.reraise exn)\<close>
  end

(* Read up to n leading bytes of a file (cheap header probe). *)
fun read_header path n =
  if File.is_file path then File_Stream.open_input (File_Stream.input_size n) path else ""

(* Run `body ()` while holding an exclusive fcntl (F_WRLCK) write lock on a
   DEDICATED lock file (separate fd from the data file -- which File.append
   opens/closes constantly -- to avoid the "any close releases the lock" trap).
   The fd lifetime is exactly the lock hold: opened here, closed on exit.
   The blocking setlkw wait stays interruptible; the body is uninterruptible. *)
local
  val lock_smode = Posix.FileSys.S.flags
        [Posix.FileSys.S.irusr, Posix.FileSys.S.iwusr,
         Posix.FileSys.S.irgrp, Posix.FileSys.S.iroth]
  fun mk_flock lt = Posix.IO.FLock.flock
        {ltype = lt, whence = Posix.IO.SEEK_SET, start = 0, len = 0, pid = NONE}
in
fun with_file_lock lk body =
  Thread_Attributes.uninterruptible_body (fn run =>
    let
      val fd = Posix.FileSys.createf
                 (File.platform_path lk, Posix.FileSys.O_RDWR,
                  Posix.FileSys.O.flags [], lock_smode)
      (* acquire under `run` so the blocking wait stays interruptible; on failure
         (incl. interrupt) close the fd, then reraise *)
      val acq = Exn.capture (fn () => run (fn () => Posix.IO.setlkw (fd, mk_flock Posix.IO.F_WRLCK)) ()) ()
      val _ = (case acq of Exn.Exn _ => ignore (Exn.capture (fn () => Posix.IO.close fd) ()) | _ => ())
      val _ = Exn.release acq
      val result = Exn.capture body ()
      val _ = Exn.capture (fn () => Posix.IO.close fd) ()  (* closing releases the fcntl lock *)
    in Exn.release result end)
end

(* Per-CACHE-FILE append lock: the in-process append mutex (so sibling threads of
   THIS process don't interleave writes to the same file -- fcntl locks are
   per-process and don't serialise sibling threads).  The bool it carries is
   `confirmed`: whether the on-disk file has been upgraded to the new format
   this process, so a repeat append can skip ensure_new_format.

   Keyed on the cache FILE, not the theory: both things this holds are properties
   of the file.  A long-theory-name key was wrong in both directions -- same long
   name in two directories shared one `confirmed` flag (a stale true skips
   ensure_new_format and appends frames onto a foreign file, losing that run's
   records), while two different long names whose SHORT names collide in one
   directory share a file yet got two different mutexes.

   NEVER evicted, deliberately.  This var IS the mutex: dropping it while another
   thread sits inside `Synchronized.change v` lets the next store_append_lock
   mint a fresh var, so two threads then append unserialised -- reachable via the
   async at_end branch.  Deleting while HOLDING v does not help either, since the
   blocked thread already has the reference; a safe eviction would need
   refcounting the holders.  So the table grows with the number of distinct cache
   files touched, and a path key grows it faster than a name key did (Isa-REPL
   gives every client connection its own base_dir while clients reuse one scratch
   theory name).  That is the price of correctness here, recorded rather than
   hidden. *)

(* Strhashtab is MUTABLE, so unlike a Symtab-in-a-Synchronized.var it is not
   thread-safe by construction: the lookup-or-insert below is a compound
   operation and must happen inside `append_locks_guard`, or two threads racing
   on a fresh key would mint two locks for one file and append unserialised.
   Nothing outside this function may touch the table. *)
val append_locks : bool Synchronized.var Strhashtab.table = Strhashtab.empty 16

val append_locks_guard : unit Synchronized.var =
  Synchronized.var "phi_store.append_locks" ()

fun store_append_lock key =
  Synchronized.change_result append_locks_guard (fn () =>
    (case Strhashtab.lookup append_locks key of
       SOME v => (v, ())
     | NONE =>
         let val v = Synchronized.var ("phi_store.append." ^ key) false
          in Strhashtab.update append_locks (key, v); (v, ()) end))

(* The warning is emitted at most once per LOCATION, not once per theory or per
   proof: it is the directory the user has to fix, and a theory can reach a write
   site many times.  warned_dirs is a leaf lock (probe_writable takes none), so it
   adds no cycle to the v -> fcntl -> openning_stores order below. *)
val warned_dirs : unit Symtab.table Synchronized.var =
  Synchronized.var "phi_store.warned_dirs" Symtab.empty

fun warn_not_writable thy =
  let val dir = Path.implode (Resources.master_directory thy)
   in if Synchronized.change_result warned_dirs (fn tab =>
           (Symtab.defined tab dir, Symtab.update (dir, ()) tab))
      then ()
      else warning ("Proof cache for theory " ^ Context.theory_name {long=true} thy ^
                    " is not writable (" ^ Path.print (store_path thy) ^
                    "); cached proofs will be read but not recorded.")
  end

(* Identifies the cache FILE, and is used ONLY as the append-lock key -- never
   dereferenced, never opened, never written anywhere.  So the only property that
   matters is: same file <-> same string.

   Normalised on every use rather than taken as spelled, so two spellings of one
   directory cannot yield two locks for one file and let appends interleave.

   File.standard_path = Path.implode o Path.expand, and expand is what does the
   work: begin_theory stores File.symbolic_path master_dir (resources.ML:243),
   and with `~` in ISABELLE_DIRECTORIES almost every master_dir here comes out
   variable-rooted -- `~/Current/...`, for which Path.is_absolute is FALSE.
   expand resolves $USER_HOME / $ISABELLE_HOME / $AFP to a root, so those
   canonicalise fully.  That is the common case, and the one a bare Path.implode
   would have got wrong.

   Deliberately NOT File.absolute_path, which differs only by resolving a
   genuinely relative path against OS.FileSys.getDir ().  That is the one thing
   we must not do: Isa-REPL chdirs per master_dir group while loading
   (REPL.ML:376), process-globally, so a cwd-dependent key could give ONE theory
   two keys at two moments -- splitting its own lock and interleaving appends for
   real.  A stable key with a coarse alias is strictly better than an unstable
   one.  Isa-REPL now absolutises its base dir on entry (Server.ML `startup` and
   the \x05file handler), so a genuinely relative master_dir should not arise;
   expand-only normalisation here is the defence that holds even if one does. *)
fun store_file_key thy = File.standard_path (store_path thy)

(* NOT memoised, deliberately.  Measured on this machine: the probe is 10.4 us
   and a memo lookup 0.24 us, against a call site that only runs when a proof is
   about to be WRITTEN -- i.e. right after a sledgehammer success (seconds) and
   right before a file append.  Saving 10 us there is unmeasurable, while the
   memo cost real correctness: a verdict cached under one key poisoned another
   location, a `chmod u+w` could not take effect until the entry was evicted, and
   the table grew without bound.  Probing every time makes all of that vanish and
   is what a user expects -- fix the permissions, caching resumes at once. *)
fun store_is_writable thy =
  let val ok = probe_writable thy
   in if ok then () else warn_not_writable thy; ok end

(* Run a durable-write body only if the cache location is writable, and never
   let a filesystem failure escape into the proof -- a cache is an optimisation,
   not a proof obligation. \<^try> re-raises interrupts, so this stays safe under
   the Timeout that wraps sledgehammer. *)
fun try_write thy body =
  if not (store_is_writable thy) then ()
  else \<^try>\<open>body () catch _ => ()\<close>
    (* Nothing to demote: the verdict is re-probed on the next attempt, so a
       transient failure (ENOSPC clearing, a remount, an NFS hiccup) recovers by
       itself instead of disabling the cache for the rest of the process. *)

(* One-shot migration of the pre-rename <thy>.proof-cache into <thy>.proof-store.
   Goes through this module's own write funnel: writability probe -> in-process
   mutex -> fcntl lock -> \<^try>, so a read-only or otherwise unwritable location
   simply does not migrate (the read path keeps falling back to the legacy file
   there).  The old file is left in place, never deleted.

   RE-CHECKING under the lock is the point: between the fast-path test and the
   lock another process may have migrated AND appended new records, and renaming
   our own stale snapshot over that would drop them.

   read_file_state_exn, not the degrading reader: a reader that answers
   empty_store on an I/O failure would hand write_state_new an empty table and
   silently write the legacy content away.

   CALL IT from the five public entry points only, at the very top of their
   bodies -- NEVER from load_store_raw / get_store_i (lock order is
   v -> fcntl -> openning_stores; calling it there closes the cycle) and never
   inside append_record's or compact_store's `Synchronized.change v` body
   (that var is not reentrant). *)
fun migrate_legacy thy =
  let val new_path = store_path thy
      val old_path = legacy_cache_path thy
      val v = store_append_lock (store_file_key thy)
   in if File.is_file new_path orelse not (File.is_file old_path)
      then ()                                          (* fast path, no lock *)
      else Synchronized.change v (fn confirmed =>
        if not (store_is_writable thy) then confirmed
        else \<^try>\<open>
          with_file_lock (lock_path thy) (fn () =>
            (if File.is_file new_path then ()
             else write_state_new new_path (#proofs (read_file_state_exn old_path));
             confirmed))
          catch _ => confirmed\<close>)
  end

(* Before appending, if the on-disk file exists but is NOT in the new format
   (an old/incompatible/corrupt file), discard it so we never append binary
   frames onto foreign content. No backward compatibility. Reached only from
   inside append_record's guarded body -- do NOT call it from a read path, its
   File.rm succeeds even on a read-only cache file. *)
fun ensure_new_format path =
  let val hdr = read_header path 4
   in if hdr = "" orelse is_new_format hdr then () else File.rm path end

(* The single funnel for all durable writes. In-process mutex (per-theory var)
   -> cross-process fcntl lock -> append one framed record. Holds the fcntl lock
   across the entire (buffered) File.append so >4KB frames can never interleave
   between processes; crash mid-frame is recovered by crc on next load.
   The writability guard sits OUTSIDE with_file_lock, never inside: with_file_lock
   opens the lock file O_RDWR and so fails BEFORE the body ever runs. The
   in-process mutex is still taken either way -- it carries the `confirmed` flag
   and the invalidate/append ordering. On failure we return the INCOMING
   `confirmed`: a confirmed format stays confirmed, an unconfirmed one is not
   falsely upgraded. *)
fun append_record thy bytes =
  let val path = store_path thy
      val v = store_append_lock (store_file_key thy)
   in Synchronized.change v (fn confirmed =>
        if not (store_is_writable thy) then confirmed
        else \<^try>\<open>
          with_file_lock (lock_path thy) (fn () =>
            ((if confirmed then () else ensure_new_format path);
             File.append path bytes;
             true))
          catch _ => confirmed\<close>)
  end

(* Compaction: under the lock, re-read the file (capturing every process's
   appends + tombstones), replay to the deduped live set, and atomically rewrite
   as a fresh new-format file. Also upgrades a never-appended legacy file.
   Guarded like append_record -- this is what protects the Theory.at_end hook
   below, whose deferred Future.forks branch would otherwise surface an IO.Io
   as a spurious error long after the theory has finished. *)
fun compact_store thy =
  let val path = store_path thy
      val v = store_append_lock (store_file_key thy)
   in Synchronized.change v (fn confirmed =>
        if not (store_is_writable thy) then confirmed
        else \<^try>\<open>
          with_file_lock (lock_path thy) (fn () =>
            (if File.is_file path then write_state_new path (#proofs (read_file_state_exn path)) else ();
             true))
          catch _ => confirmed\<close>)
  end

(* Beside its store, every open theory carries one more table: what THIS session
   has already written under each key.  It is what separates a real key
   collision -- two different obligations reaching one proof id -- from an
   ordinary cross-build update of a key that was merely read off the file.
   Asking `proofs` instead would report every such update as a collision.

   It holds a digest and a few leading characters, never the proof text: an
   aoa_replay blob runs to hundreds of thousands of characters, and this table
   lives as long as the theory does.

   It is monotone within the session, and deliberately NOT derived from
   `proofs`.  `proofs` loses a key to store_invalidate_proof, and the main
   collision path runs straight through that loss (L2 hit -> replay fails ->
   tombstone -> rewrite), so a mark kept in `proofs` would erase its own
   evidence and the collision count would be a constant zero.  Hence
   store_invalidate_proof, force_reload and invalidate_store all leave it
   alone; close_store drops it, and that is precisely the session boundary. *)
type written = (string * string * int) Symtab.table
  (*key -> SHA1 of the proof text, its leading characters, standard-machine ms*)

val proof_head_len = 120
fun proof_mark (t, text) =
  let val syms = Symbol.explode text
   in (SHA1.rep (SHA1.digest text),
       if length syms <= proof_head_len then text
       else String.concat (take proof_head_len syms) ^ " ...",
       Time.toMilliseconds t)
  end

fun written_of tab name =
  case Symtab.lookup tab name of SOME (_, _, w) => w | NONE => Symtab.empty

val openning_stores : (store * bool * written) Symtab.table Synchronized.var
  = Synchronized.var "\<phi>-System.openning_stores" Symtab.empty

(* Read fallback: where migration could not run (an unwritable location) the new
   file simply is not there, and the legacy one still holds every record -- so
   read it rather than come up empty.  Deliberately NOT inside migrate_legacy's
   guard: this path takes no lock and must stay callable from get_store_i. *)
fun load_store_raw thy =
  let val path = store_path thy
      val path = if File.is_file path then path else legacy_cache_path thy
   in read_file_state path end

fun force_reload thy =
 (migrate_legacy thy;                                        (*D44: outside the critical section*)
  Synchronized.change_result openning_stores (fn tab =>
    let val name = Context.theory_name {long=true} thy
        val c = load_store_raw thy
        (*re-reading the file says nothing about what this session wrote*)
        val w = written_of tab name
     in (c, Symtab.update (name, (c, false, w)) tab) end ))

(*The whole entry, for the writer that needs the written table too; get_store_i
  is the same thing for the readers that only want the store.*)
fun get_entry_i thy tab =
  case Symtab.lookup tab (Context.theory_name {long=true} thy)
      of SOME e => (e, tab)
       | _ => let val e = (load_store_raw thy, false, Symtab.empty)
               in (e, Symtab.update_new (Context.theory_name {long=true} thy, e) tab) end

fun get_store_i thy tab =
  let val ((c, _, _), tab') = get_entry_i thy tab in (c, tab') end

fun get_store thy =
 (migrate_legacy thy;                                        (*D44*)
  Synchronized.change_result openning_stores (get_store_i thy))

fun register_async_task task thy =
  let val name = Context.theory_name {long=true} thy
      val _ = migrate_legacy thy                             (*D44*)
   in Synchronized.change openning_stores (fn tab =>
      case Symtab.lookup tab name
        of SOME (c, flag, w) => Symtab.update (name, (store_add_async task c, flag, w)) tab
         | _ => let val c = store_add_async task (load_store_raw thy)
                 in Symtab.update_new (name, (c, false, Symtab.empty)) tab end )
  end

(* Persistence is now continuous (each update appends immediately), so storing
   is just compaction; closing just drops the in-memory entry. *)
fun compact_and_store thy = compact_store thy

fun close_store thy =
  (* Only the in-memory proof table is per-theory state to drop here.  There is no
     writability verdict to evict any more (it is probed, not cached), and the
     append lock must NOT be evicted -- see store_append_lock.
     Dropping the entry drops the written table with it, and that is deliberate:
     it is what makes "this session" mean "this theory, start to end". *)
  Synchronized.change openning_stores
    (Symtab.delete_safe (Context.theory_name {long=true} thy))

(* Drop the data file and reset the in-memory entry as ONE per-theory critical
   section (under the same `v` that serialises appends), so a concurrent append
   cannot slip between the disk-rm and the memory-reset. Lock order here is
   v -> fcntl -> openning_stores; nothing acquires v while holding
   openning_stores, so there is no cycle. The in-memory half is unconditional:
   when the disk half is skipped, a bad cached proof is still dropped for this
   session, we merely cannot record the tombstone durably. *)
fun invalidate_store thy =
  (* two keys: the mutex/flag is per cache FILE, the openning_stores entry below
     is per theory. *)
  let val name = Context.theory_name {long=true} thy in
  Synchronized.change (store_append_lock (store_file_key thy)) (fn _ =>
    (try_write thy (fn () =>
       with_file_lock (lock_path thy) (fn () =>
         if File.is_file (store_path thy) then File.rm (store_path thy) else ()));
     Synchronized.change openning_stores (fn tab =>
       (*dropping the data does not un-write what this session wrote*)
       Symtab.update (name, (empty_store, true, written_of tab name)) tab);
     false))
  end

fun get_cached_proof thy id =
  Option.map (fn r => (#time r, #proof r)) (Symtab.lookup (#proofs (get_store thy)) id)

fun get_cached_proof_by_hash thy h = Hasher.Tab.lookup (#by_hash (get_store thy)) h

fun collision_message id (_, old_head, old_ms) (_, new_head, new_ms) =
  "Proof store: this session has written two DIFFERENT proofs under one key.\n\
  \  key: " ^ id ^ "\n\
  \  first (" ^ string_of_int old_ms ^ " ms): " ^ old_head ^ "\n\
  \  now replaced by (" ^ string_of_int new_ms ^ " ms): " ^ new_head ^ "\n\
  \Two proof obligations share one proof id.  The first proof is gone, and \
  \whichever of the two obligations next meets the survivor will fail to replay \
  \it -- with the AoA gate shut, that is a failed build.  \
  \See PROOF_ID_COLLISION_FIX_PLAN.md."

(*This guard cannot stop a key collision, only make the build that produces one
  say so on the spot, instead of leaving it to surface days later in another
  theory as an unexplained replay failure.  It sits at the single point every
  writer goes through, so it also sees the writers that a Post_App probe hook
  structurally cannot (holds_fact, led_future_proof).

  Its two questions go to two different tables on purpose -- the reasons are
  with the declaration of `written` above.  The skip half additionally drops the
  benign duplicate appends of the rw_access retry path.

  The time in `s` must ALREADY be standard-machine time -- every caller passes
  its measurement through standard_time first.  Normalising here instead would
  double-divide the callers that (per the time-semantics rule) do it themselves
  before handing the record over.*)
fun update_cached_proof thy {id, hash} s =
 (migrate_legacy thy;                                        (*D44: a write can be the first touch*)
  let val name = Context.theory_name {long=true} thy
      val mark = proof_mark s
      val r = {hash = hash, time = #1 s, proof = #2 s} : proof_record
      (*The message is built inside the critical section but emitted outside it:
        output synchronises on its own, and this section already serialises the
        concurrent writers (\<phi>SH.record_proof, hammer_or_AoA_store_write).*)
      val (do_append, msg) =
        Synchronized.change_result openning_stores (fn tab =>
          let val ((c, _, w), tab') = get_entry_i thy tab
              (*the whole record, time included: a skipped write then leaves
                proofs[id] byte-identical, so the frame it would append is
                redundant*)
              val live_and_identical = Symtab.lookup (#proofs c) id = SOME r
           in if live_and_identical
              then ((false, NONE), tab')
              else let val msg = case Symtab.lookup w id
                                   of SOME old =>
                                        if #1 old = #1 mark then NONE
                                        else SOME (collision_message id old mark)
                                    | NONE => NONE
                    in ((true, msg),
                        Symtab.update
                          (name, (store_update_proof (id, r) c, true,
                                  Symtab.update (id, mark) w)) tab')
                   end
          end)
      val _ = case msg of SOME m => warning m | NONE => ()
   in if do_append then append_record thy (put_frame id r) else ()
  end)

fun report_cache_is_outdated warn thy =
  if warn
  then warning ("Proof cache for theory " ^ Context.theory_name {long=true} thy ^ " is outdated!")
  else ()

fun invalidate_proof_cache warn id thy =
 (report_cache_is_outdated warn thy;
  migrate_legacy thy;                                        (*D44*)
  Synchronized.change openning_stores (fn tab =>
    let val (_, tab') = get_store_i thy tab
     in Symtab.map_entry (Context.theory_name {long=true} thy)
                         (*w survives: this is the very path a collision takes,
                           and a mark dropped here is evidence destroyed*)
                         (fn (c, _, w) => (store_invalidate_proof id c, true, w)) tab'
    end);
  append_record thy (encode_tombstone id))

(*Narrows an entry that exists: only reachable after get_cached_proof_by_hash
  answered SOME.  An entry already dropped by close_store needs nothing --
  by_hash is memory only and the next load rebuilds it from the frames.*)
fun invalidate_proof_cache_by_hash h thy =
  Synchronized.change openning_stores
    (Symtab.map_entry (Context.theory_name {long=true} thy)
       (fn (c, f, w) => (store_forget_hash h c, f, w)))

(** Document_ID of each construct to detect if caches are invalid **)
(*
val doc_ids : string Phi_ID.Tab.table Synchronized.var
      = Synchronized.var "\<phi>-System.doc_ids" Phi_ID.Tab.empty

fun check_cache' construct doc_id thy =
  let fun clean_tab tab =
            Phi_ID.Tab.fold (fn (k,_) =>
              if Phi_ID.dep' construct k
              then Phi_ID.Tab.delete k
              else I) tab tab
   in if null (snd construct)
         orelse (Synchronized.change_result doc_ids (fn tab =>
            case Phi_ID.Tab.lookup tab construct
              of SOME id' =>
                  if id' = doc_id
                  then (true , tab)
                  else (false, Phi_ID.Tab.update (construct, doc_id) (clean_tab tab))
               | _ =>  (true , Phi_ID.Tab.update (construct, doc_id) tab)))
      then ()
      else invalidate_proof_cache (Phi_ID.encode construct) thy
  end

fun check_cache doc_id ctxt =
  case Phi_ID.get ctxt
    of SOME phid => check_cache' phid doc_id (Proof_Context.theory_of ctxt)
     | _ => () *)

(*TODO: maybe we need some way to clean up unused cache entries.*)


(* At theory end, compact the append log (dedup + drop superseded/tombstoned
   records). Appends are already durable, so we only defer the COMPACTION behind
   still-running async proof tasks REGISTERED via register_async_task: it lets
   those tasks' appends land before we rewrite. A late append from a registered
   task after store_and_close still goes to disk durably; it would re-insert a
   stale in-memory openning_stores entry (harmless, dropped next load) -- the
   deferral keeps that from happening for the registered tasks. *)
val _ = Theory.setup (Theory.at_end (fn thy => (
  let val tasks = #async_tasks (get_store thy)
    in if null tasks then (compact_store thy; close_store thy)
       else ((* tracing "There are asynchronous proof tasks. The proof cache will be compacted \
                       \once they are finished." ; *)
             (*interrupts=true for the same reason as \<phi>SH.record_proof: this body
               takes the fcntl lock, and with_file_lock's `run` restores the attributes
               in effect on entry, so forking uninterruptible would make the blocking
               setlkw wait uncancellable.*)
             Future.forks {name="\<phi>System.compact_store", group=NONE, deps = tasks, pri=1, interrupts=true}
              [(fn _ => (compact_store thy; close_store thy
                         (* ; tracing "The proof cache has been compacted." *)))] ;
            ())
    end
  ; NONE)))

(* Guard the divisor: timeout_scale is a user-settable real, and 0 (or a
   negative) would blow up or negate every stored time. *)
fun standard_time t = Time.scale (1.0 / Real.max (Timeout.scale (), 0.001)) t

(*** Proof cache by hash ***)

(* prf' carries the RAW measured elapsed; standard_time normalises it once here,
   so the record holds standard-machine time and the read path (which passes it
   through tolerant_time into Timeout.apply) gets the factor applied exactly
   once. *)
fun update_cache_by_hash hash prf' (ctxt, sequent') =
  let val prf' = apfst standard_time prf' in (
       (* Silenced: sledgehammer_solver.ML already traces the same message at
          its record points; this copy was the un-migrated twin.
       tracing (
          "Find proof (" ^ hash ^ ", time: " ^ Time.toString (fst prf') ^ "): " ^
           (if snd prf' = "" then "classical automation" else "\n" ^ snd prf')
       ) ; *)
       update_cached_proof (Proof_Context.theory_of ctxt) {id = Hasher.hex hash, hash = SOME hash} prf' ;
       (snd prf', sequent')) end

type proof = string
val time_delt = Time.fromMilliseconds 1000
fun tolerant_time t = Time.scale 1.5 t + time_delt

fun try_cached_proof_by_hash_with_key key_fn evaluator fallback (ctxt, sequent) =
  let val hash = key_fn (ctxt, sequent)
      fun fallback' origin_prf =
            let val (prf', ret) = fallback origin_prf
             in update_cache_by_hash hash prf' (ctxt, sequent)
              ; (prf', ret)
            end
   in if Config.get ctxt enable_proof_store
    then case get_cached_proof (Proof_Context.theory_of ctxt) (Hasher.hex hash)
          of NONE => fallback' NONE
           | SOME (time,prf) =>
              let val ctxt' = ctxt (*if prf = "" then ctxt else Phi_Envir.freeze_dynamic_lemmas ctxt*)
               in case ( evaluator (tolerant_time time) prf (ctxt', sequent)
                         handle Timeout.TIMEOUT _ => NONE )
                    of SOME ret => ((time,prf), ret)
                     | NONE => fallback' (SOME prf)
              end
    else fallback NONE
  end

(* Keyed on the LEADING subgoal, like every other single-goal entry point.  It
   used to key on Hasher.goal (the whole proposition, conclusion included); that
   formula is not invariant under the fork/promise transformation and must not
   survive anywhere, least of all behind an exported name. *)
val try_cached_proof_by_hash = try_cached_proof_by_hash_with_key (Hasher.goal_at 1)

fun try_cached_proof_by_hash_at i = try_cached_proof_by_hash_with_key (Hasher.goal_at i)

end

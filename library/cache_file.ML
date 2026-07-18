(* Building Cache *)

(* ===========================================================================
   Proof cache on-disk format: a crash-robust, multi-process-safe append log.

   The file is a sequence of self-delimited frames:

     [ magic : u32 BE = 0x6ABCDEF6 ][ len : u32 BE ][ crc32 : u32 BE ][ payload : len bytes ]

   crc32 is the standard IEEE 802.3 CRC-32 over (be32 len ++ payload).
   payload is a MessagePack-encoded record:

     PUT  (key, time_ms, value)   <->  (1, (key, time_ms, value))
     TOMB key                     <->  (2, key)

   Reading scans for the magic, validates the crc and that len fits, then
   applies records in file order (last write wins; TOMB deletes the key).
   A torn/half-written trailing frame, or a magic byte-sequence that happens
   to occur inside a payload, fails the crc check and the scanner resynchronises
   at the next magic occurrence -- so a crash never corrupts earlier records and
   never causes a wrong record to be accepted (beyond the 2^-32 crc collision).

   MessagePack comes from the Performant_Isabelle_ML base session (mlmsgpack).
   This structure is deliberately exposed (no signature ascription) so the
   format can be unit-tested directly.
   =========================================================================== *)
structure Proof_Cache_Format = struct

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

datatype record = PUT of string * int * string | TOMB of string

local
  structure P = MessagePackBytesIO.Pack
  structure U = MessagePackBytesIO.Unpack
  val put_packer = P.packPair (P.packInt, P.packTuple3 (P.packString, P.packInt, P.packString))
  val tomb_packer = P.packPair (P.packInt, P.packString)
  val rec_unpacker =
    U.unpackPair_dep' U.unpackInt (fn tag =>
      if tag = 1 then U.>> (U.unpackTuple3 (U.unpackString, U.unpackInt, U.unpackString), PUT)
      else if tag = 2 then U.>> (U.unpackString, TOMB)
      else raise U.Unpack)
in
fun encode_record r =
  let val outs = BytesIO.mkOutstream ()
   in (case r of PUT (k, t, v) => put_packer (1, (k, t, v)) outs
               | TOMB k => tomb_packer (2, k) outs);
      BytesIO.toString outs
  end
fun decode_record payload = #1 (U.doUnpack rec_unpacker (BytesIO.fromString payload))
end

fun frame payload =
  let val len_bytes = be32 (Word32.fromInt (size payload))
   in MAGIC ^ len_bytes ^ be32 (crc32 (len_bytes ^ payload)) ^ payload end

fun encode_put (k, t, v) = frame (encode_record (PUT (k, t, v)))
fun encode_tombstone k = frame (encode_record (TOMB k))

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

(* replay records (file order) into the proof table; last write wins, TOMB deletes *)
fun replay records =
  fold (fn PUT (k, t, v) => Symtab.update (k, (Time.fromMilliseconds t, v))
         | TOMB k => Symtab.delete_safe k)
       records Symtab.empty

end


signature PHI_CACHE_DB = sig

type proof_id = string
type proof_cache = Time.time * string
type cache = {proofs: proof_cache Symtab.table,
              async_tasks: Task_Queue.task list}

val get_cache : theory -> cache
val force_reload : theory -> cache
val register_async_task : Task_Queue.task -> theory -> unit

val store_cache : theory -> unit
val store_and_close_cache : theory -> unit
val invalidate_cache : theory -> unit
val invalidate_proof_cache : bool (*whether warn*) -> proof_id -> theory -> unit
(* val check_cache : string (*Document_ID*) -> Proof.context -> unit *)
val report_cache_is_outdated : bool (*whether warn*) -> theory -> unit

val get_cached_proof : theory -> proof_id -> (Time.time * string) option
val update_cached_proof : theory -> proof_id * (Time.time * string) -> unit

(*Here we provide another mechanism which records the proof to the hash digest of the proposition.
  It is useful when the user is editing a code before a lemma of a cached proof, the proof-id of the
  lemma can be changed due to the editing, but the hash digest will not only if the proposition of
  the lemma itself is unchanged, so the proof can be still cached and saves the user from annoying
  proof re-search.
  However, the hash cache DB is heavy in both calculating the hash (having to enumerate every term
  and type with many string concatenations, costing about hundreds milliseconds) and storing the
  record as the hash has no way to be short (the scope is in global!) but of 20 bytes using SHA1.
  Therefore, this feature is only enabled during the interactive editing time.
*)

val access_hash_cache : Hasher.digest -> proof_cache option
val update_hash_cache : Hasher.digest -> proof_cache -> unit
val clean_hash_cache  : unit -> unit

type proof = string
val try_cached_proof_by_hash :
         (Time.time -> proof -> context_state -> context_state option) (*evaluator*)
      -> (string option (*original cached proof*) -> (Time.time * proof) * context_state)
      -> context_state
      -> (Time.time * proof) * context_state

(*Variant keyed by Hasher.goal_at i — caches a per-subgoal proof.
  Use i = 0 to mean "the whole sequent" (equivalent to try_cached_proof_by_hash);
  use i >= 1 to key on the i-th subgoal in isolation.*)
val try_cached_proof_by_hash_at :
         int (*subgoal index, 0 = whole sequent*)
      -> (Time.time -> proof -> context_state -> context_state option) (*evaluator*)
      -> (string option (*original cached proof*) -> (Time.time * proof) * context_state)
      -> context_state
      -> (Time.time * proof) * context_state

val enable_proof_cache : bool Config.T

end


structure Phi_Cache_DB : PHI_CACHE_DB = struct

val enable_proof_cache = Attrib.setup_config_bool \<^binding>\<open>enable_proof_cache\<close> (K true)

type proof_id = string
type proof_cache = Time.time * string
type cache = {proofs: (Time.time * string) Symtab.table,
              async_tasks: Task_Queue.task list}

val empty_cache = {proofs = Symtab.empty, async_tasks = []} : cache

open Proof_Cache_Format  (*MAGIC, crc32, frame, scan, replay, encode_put, encode_tombstone, ...*)

fun cache_update_proof (id,s) ({proofs, async_tasks}:cache)
      = {proofs = Symtab.update (id,s) proofs,
         async_tasks = async_tasks} : cache

fun cache_invalidate_proof id ({proofs,async_tasks}:cache)
      = {proofs = Symtab.delete_safe id proofs (*Symtab.fold (fn (k,_) =>
                      if Phi_ID.dep id k
                      then Symtab.delete k
                      else I) proofs proofs*),
         async_tasks = []
        } : cache

fun cache_add_async task ({proofs,async_tasks}:cache)
      = {proofs = proofs, async_tasks = task :: async_tasks} : cache

fun cache_path thy =
      Path.append (Resources.master_directory thy) (Path.basic (Context.theory_name {long=false} thy))
   |> Path.ext "proof-cache"

fun lock_path thy = Path.ext "lock" (cache_path thy)   (* <thy>.proof-cache.lock *)

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
      val cache = cache_path thy
      val lock = lock_path thy
   in File.is_dir dir andalso
      accessible dir [OS.FileSys.A_WRITE, OS.FileSys.A_EXEC] andalso
      (not (File.exists cache) orelse accessible cache [OS.FileSys.A_WRITE]) andalso
      (not (File.exists lock) orelse accessible lock [OS.FileSys.A_WRITE])
  end

(* Read the proof table from a new-format file. Any non-new-format or corrupt
   file is treated as empty -- there is NO backward compatibility; old caches
   are discarded. Best-effort: a decode failure degrades to empty, and so does
   an unreadable file -- a cache primed by another user under a tight umask
   would otherwise raise EACCES from Bytes.read straight into the user's proof
   (the read happens before any write, so the writability probe cannot help).

   TWO readers, deliberately, because there are two callers with OPPOSITE needs.

   `read_file_state_exn` lets an I/O failure escape, and is what compaction must
   use: `compact_cache` feeds this result straight back to `write_state_new`, so
   a reader that degrades to `Symtab.empty` there does not degrade -- it TRUNCATES
   the user's cache to nothing and renames the empty payload over it.  Letting the
   exception out instead aborts the rewrite with the file byte-intact, and
   `compact_cache`'s own handler demotes the verdict.  Triggers are not only
   permissions: EIO, an NFS ESTALE, EMFILE under a parallel build, or Size on a
   large cache all raise here from an ordinary mode-0644 file.

   `read_file_state` degrades, and is what the pure read path uses.

   In BOTH, a decode failure still discards: a corrupt or truncated file is
   treated as empty, which is the pre-existing contract and is unchanged. *)
fun read_file_state_exn path =
  if not (File.is_file path) then Symtab.empty
  else
    let val raw = Bytes.content (Bytes.read path)   (* I/O failure escapes, by design *)
     in if is_new_format raw
        then \<^try>\<open>replay (scan raw) catch _ => Symtab.empty\<close>
        else Symtab.empty
    end

fun read_file_state path =
  \<^try>\<open>read_file_state_exn path catch _ => Symtab.empty\<close>

(* process id, used to make the compaction temp file unique across processes *)
val proc_pid = SysWord.toString (Posix.Process.pidToWord (Posix.ProcEnv.getpid ()))

(* Atomically write the proof table as a fresh new-format file (tmp + rename).
   The temp file name carries the pid so two processes compacting the same
   theory never write the same temp path (they are already serialised by the
   fcntl lock, but a unique name removes that dependence). File.write neither
   unlinks nor truncates back on failure, so a failed rename (or a mid-write
   ENOSPC) would orphan the temp file; unlink it and rethrow, leaving the
   verdict to the caller's guard. *)
fun write_state_new path proofs =
  let val payload =
        String.concat (Symtab.fold (fn (k,(t,v)) => fn acc =>
                          encode_put (k, Time.toMilliseconds t, v) :: acc) proofs [])
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

(* Per-CACHE-PATH append var: doubles as the in-process append mutex (so sibling
   threads of THIS process don't interleave writes to the same file -- fcntl
   locks are per-process and don't serialise sibling threads) and caches whether
   the on-disk file has been confirmed/upgraded to the new format this process.

   Keyed on the path, like writable_vars and for the same reason: both things it
   holds are properties of the FILE, not of the theory.  A long-theory-name key
   got this wrong in both directions -- same name in two directories shared one
   `confirmed` flag (so a stale true skipped ensure_new_format and appended new
   frames onto a foreign file, losing that run's records), and two different long
   names whose SHORT names collide in one directory share a file yet would get
   two different mutexes.

   NOT evicted in store_and_close_cache, deliberately, unlike writable_vars: this
   var IS the append mutex, and dropping it while another thread sits inside
   `Synchronized.change v` lets the next theory_append_var mint a fresh var, so
   two threads then append unserialised -- reachable via the async at_end branch.
   With a path key there is nothing to gain from evicting it anyway. *)
val append_vars : bool Synchronized.var Symtab.table Synchronized.var =
  Synchronized.var "phi_cache.append_vars" Symtab.empty

fun theory_append_var name =
  Synchronized.change_result append_vars (fn tab =>
    case Symtab.lookup tab name of
      SOME v => (v, tab)
    | NONE => let val v = Synchronized.var ("phi_cache.append." ^ name) false
               in (v, Symtab.update_new (name, v) tab) end)

(* Per-theory writability verdict (see probe_writable), memoised alongside the
   append vars so a write costs one Symtab lookup, not five syscalls. A write
   that fails anyway -- a race with a remount, ENOSPC, an NFS refusal -- flips
   the entry to false through note_write_failure, so we do not pay a doomed
   open() per proof afterwards. The entry is dropped at theory end (see
   store_and_close_cache): without that, a `chmod u+w` could never take effect
   in a long-lived process, and two theories of the same short name from
   different directories would share one verdict.
   Because the verdict is re-probed after every eviction, the WARNING is not
   gated on it but on a process-global set of already-reported directories --
   it is the location, not the theory instance, the user has to fix.
   writable_vars and warned_dirs are leaf locks (probe_writable takes none), so
   they add no cycle to the v -> fcntl -> openning_caches order below. *)
val writable_vars : bool Symtab.table Synchronized.var =
  Synchronized.var "phi_cache.writable" Symtab.empty

val warned_dirs : unit Symtab.table Synchronized.var =
  Synchronized.var "phi_cache.warned_dirs" Symtab.empty

fun warn_not_writable thy =
  let val dir = Path.implode (Resources.master_directory thy)
   in if Synchronized.change_result warned_dirs (fn tab =>
           (Symtab.defined tab dir, Symtab.update (dir, ()) tab))
      then ()
      else warning ("Proof cache for theory " ^ Context.theory_name {long=true} thy ^
                    " is not writable (" ^ Path.print (cache_path thy) ^
                    "); cached proofs will be read but not recorded.")
  end

(* Keyed on the probed PATH, not on the theory name.  probe_writable is a
   predicate over cache_path/lock_path/master_directory, none of which is a
   function of the theory name alone: two theories sharing a long name but living
   in different directories denote DIFFERENT cache files, and a name key makes
   them share one verdict -- so a read-only directory's `false` poisons a
   perfectly writable one, which then records nothing, silently (the warning
   fires only on the NONE branch).  Constructible today: Resources.begin_theory
   has no global name registry and Isa-REPL takes base_dir per request, with only
   a thread-local duplicate-name guard.  This key matches probe_writable's
   granularity exactly, and agrees with warned_dirs' location key. *)
fun writable_key thy = Path.implode (cache_path thy)

fun cache_is_writable thy =
  let val name = writable_key thy
   in Synchronized.change_result writable_vars (fn tab =>
        case Symtab.lookup tab name of
          SOME b => (b, tab)
        | NONE => let val b = probe_writable thy
                      val _ = if b then () else warn_not_writable thy
                   in (b, Symtab.update_new (name, b) tab) end)
  end

fun note_write_failure thy =
  Synchronized.change writable_vars (Symtab.update (writable_key thy, false))

(* Run a durable-write body only if the cache location is writable, and never
   let a filesystem failure escape into the proof -- a cache is an optimisation,
   not a proof obligation. \<^try> re-raises interrupts, so this stays safe under
   the Timeout that wraps sledgehammer. *)
fun try_write thy body =
  if not (cache_is_writable thy) then ()
  else \<^try>\<open>body () catch _ => note_write_failure thy\<close>

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
  let val path = cache_path thy
      val v = theory_append_var (writable_key thy)
   in Synchronized.change v (fn confirmed =>
        if not (cache_is_writable thy) then confirmed
        else \<^try>\<open>
          with_file_lock (lock_path thy) (fn () =>
            ((if confirmed then () else ensure_new_format path);
             File.append path bytes;
             true))
          catch _ => (note_write_failure thy; confirmed)\<close>)
  end

(* Compaction: under the lock, re-read the file (capturing every process's
   appends + tombstones), replay to the deduped live set, and atomically rewrite
   as a fresh new-format file. Also upgrades a never-appended legacy file.
   Guarded like append_record -- this is what protects the Theory.at_end hook
   below, whose deferred Future.forks branch would otherwise surface an IO.Io
   as a spurious error long after the theory has finished. *)
fun compact_cache thy =
  let val path = cache_path thy
      val v = theory_append_var (writable_key thy)
   in Synchronized.change v (fn confirmed =>
        if not (cache_is_writable thy) then confirmed
        else \<^try>\<open>
          with_file_lock (lock_path thy) (fn () =>
            (if File.is_file path then write_state_new path (read_file_state_exn path) else ();
             true))
          catch _ => (note_write_failure thy; confirmed)\<close>)
  end

val openning_caches : (cache * bool) Symtab.table Synchronized.var
  = Synchronized.var "\<phi>-System.openning_caches" Symtab.empty

fun load_cache_raw thy =
  {proofs = read_file_state (cache_path thy), async_tasks = []} : cache

fun force_reload thy =
  Synchronized.change_result openning_caches (fn tab =>
    let val c = load_cache_raw thy
     in (c, Symtab.update (Context.theory_name {long=true} thy, (c, false)) tab) end )

fun get_cache_i thy tab =
  case Symtab.lookup tab (Context.theory_name {long=true} thy)
      of SOME (x, _) => (x, tab)
       | _ => let val c = load_cache_raw thy
               in (c, Symtab.update_new (Context.theory_name {long=true} thy, (c, false)) tab) end

fun get_cache thy =
  Synchronized.change_result openning_caches (get_cache_i thy)

fun register_async_task task thy =
  let val name = Context.theory_name {long=true} thy
   in Synchronized.change openning_caches (fn tab =>
      case Symtab.lookup tab name
        of SOME (c, flag) => Symtab.update (name, (cache_add_async task c, flag)) tab
         | _ => let val c = cache_add_async task (load_cache_raw thy)
                 in Symtab.update_new (name, (c, false)) tab end )
  end

(* Persistence is now continuous (each update appends immediately), so storing
   is just compaction; closing just drops the in-memory entry. *)
fun store_cache thy = compact_cache thy

fun store_and_close_cache thy =
  (* TWO keys: openning_caches is per theory, writable_vars is per cache path. *)
  let val name = Context.theory_name {long=true} thy
   in Synchronized.change openning_caches (Symtab.delete_safe name);
      Synchronized.change writable_vars (Symtab.delete_safe (writable_key thy))
  end

(* Drop the data file and reset the in-memory entry as ONE per-theory critical
   section (under the same `v` that serialises appends), so a concurrent append
   cannot slip between the disk-rm and the memory-reset. Lock order here is
   v -> fcntl -> openning_caches; nothing acquires v while holding
   openning_caches, so there is no cycle. The in-memory half is unconditional:
   when the disk half is skipped, a bad cached proof is still dropped for this
   session, we merely cannot record the tombstone durably. *)
fun invalidate_cache thy =
  (* two keys, as in store_and_close_cache: the mutex/flag is per cache PATH,
     the openning_caches entry below is per theory. *)
  let val name = Context.theory_name {long=true} thy in
  Synchronized.change (theory_append_var (writable_key thy)) (fn _ =>
    (try_write thy (fn () =>
       with_file_lock (lock_path thy) (fn () =>
         if File.is_file (cache_path thy) then File.rm (cache_path thy) else ()));
     Synchronized.change openning_caches (Symtab.update (name, (empty_cache, true)));
     false))
  end

fun get_cached_proof thy = Symtab.lookup (#proofs (get_cache thy))

fun update_cached_proof thy (id,s) =
 (Synchronized.change openning_caches (fn tab =>
    let val (_, tab') = get_cache_i thy tab
     in Symtab.map_entry (Context.theory_name {long=true} thy)
                         (fn (c, _) => (cache_update_proof (id,s) c, true)) tab'
    end);
  append_record thy (encode_put (id, Time.toMilliseconds (#1 s), #2 s)))

fun report_cache_is_outdated warn thy =
  if warn
  then warning ("Proof cache for theory " ^ Context.theory_name {long=true} thy ^ " is outdated!")
  else ()

fun invalidate_proof_cache warn id thy =
 (report_cache_is_outdated warn thy;
  Synchronized.change openning_caches (fn tab =>
    let val (_, tab') = get_cache_i thy tab
     in Symtab.map_entry (Context.theory_name {long=true} thy)
                         (fn (c, _) => (cache_invalidate_proof id c, true)) tab'
    end);
  append_record thy (encode_tombstone id))

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
   stale in-memory openning_caches entry (harmless, dropped next load) -- the
   deferral keeps that from happening for the registered tasks. *)
val _ = Theory.setup (Theory.at_end (fn thy => (
  let val tasks = #async_tasks (get_cache thy)
    in if null tasks then (compact_cache thy; store_and_close_cache thy)
       else (tracing "There are asynchronous proof tasks. The proof cache will be compacted \
                     \once they are finished." ;
             Future.forks {name="\<phi>System.compact_cache", group=NONE, deps = tasks, pri=1, interrupts=false}
              [(fn _ => (compact_cache thy; store_and_close_cache thy;
                         tracing "The proof cache has been compacted."))] ;
            ())
    end
  ; NONE)))

(*** Proof cache by hash ***)

val hash_cache : proof_cache Symtab.table Synchronized.var
      = Synchronized.var "\<phi>System.proof_cache.hash" Symtab.empty

fun access_hash_cache hash =
  let val hc = Synchronized.value hash_cache
   in Symtab.lookup hc hash end

fun update_hash_cache hash prf =
  Synchronized.change hash_cache (Symtab.update (hash, prf))

fun clean_hash_cache () =
  Synchronized.change hash_cache (K Symtab.empty)

fun update_cache_by_hash hash prf' (ctxt, sequent') = (
       tracing (
          "Find proof (" ^ hash ^ ", time: " ^ Time.toString (fst prf') ^ "): " ^
           (if snd prf' = "" then "classical automation" else "\n" ^ snd prf')
       ) ;
       update_hash_cache hash prf';
       update_cached_proof (Proof_Context.theory_of ctxt) (hash, prf') ;
       (snd prf', sequent'))

type proof = string
val time_delt = Time.fromMilliseconds 1000

fun try_cached_proof_by_hash_with_key key_fn evaluator fallback (ctxt, sequent) =
  let val hash = key_fn (ctxt, sequent)
      fun fallback' origin_prf =
            let val (prf', ret) = fallback origin_prf
             in update_cache_by_hash hash prf' (ctxt, sequent)
              ; (prf', ret)
            end
   in if Config.get ctxt enable_proof_cache
    then case get_cached_proof (Proof_Context.theory_of ctxt) hash
          of NONE => fallback' NONE
           | SOME (time,prf) =>
              let val ctxt' = ctxt (*if prf = "" then ctxt else Phi_Envir.freeze_dynamic_lemmas ctxt*)
               in case ( evaluator (Time.scale 1.5 time + time_delt) prf (ctxt', sequent)
                         handle Timeout.TIMEOUT _ => NONE )
                    of SOME ret => ((time,prf), ret)
                     | NONE => fallback' (SOME prf)
              end
    else fallback NONE
  end

val try_cached_proof_by_hash = try_cached_proof_by_hash_with_key Hasher.goal

fun try_cached_proof_by_hash_at i = try_cached_proof_by_hash_with_key (Hasher.goal_at i)

end
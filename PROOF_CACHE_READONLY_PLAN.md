# Graceful degradation of the proof cache on a non-writable cache directory

Status: **IMPLEMENTED** (§4 in full, in `library/cache_file.ML`). Revision 3 records the two
places where the implementation deviates from Revision 2's code, and the test results.

Deviations found while implementing (Revision 3):

1. **§4.2's snippet emits the warning on the memo-miss branch — that is incompatible with
   §4.2a's own eviction.** Once the entry is evicted at theory end, every re-check is a miss
   and re-warns. §4.2a already anticipated this ("pair it with a process-global *already
   warned* set keyed on `Resources.master_directory thy`") but the code block was never
   updated. As implemented, `cache_is_writable` calls `warn_not_writable`, which consults a
   process-global `warned_dirs : unit Symtab.table Synchronized.var` keyed on
   `Path.implode (Resources.master_directory thy)` and warns only on first sight of a
   location. The *verdict* is still keyed per theory, per §4.2a's closing instruction. This
   also delivers §8's R5 mitigation for free.
2. **§4.6's `\<^try>\<open>File.rm tmp\<close>` in statement position needs no `ignore`.** It
   was checked: Poly/ML under this distribution accepts the discarded `unit option` without
   a warning, so the snippet stands as written.

Everything else in §4 is implemented verbatim. `Path.print` was double-checked against §5's
claim and is correct: `warning ("… " ^ Path.print p)` renders as `"/abs/path"` (the markup is
stripped by the front end).

Test results: §7.2 cases A, B, C, D, E, F, H, I, J were run against a scratch copy under
`/tmp` as uid 1002; all matched the expected column. G is covered by B/C/E (the test theory
calls `invalidate_proof_cache` and the on-disk cache is byte-identical afterwards). The
`File.rm tmp` orphan-cleanup branch of §4.6 was not exercised directly — it needs a failure
*between* a successful `File.write` and the `rename`, which the DAC setups cannot produce.

Revision 2. This document has been through a two-turn adversarial review (0 blockers, 2
majors, 4 minors; 7 findings rejected as low quality). The surviving findings are folded
in, and the places where revision 1 was **wrong** are marked as such rather than quietly
edited — see §0.1 (blast radius), §4.2a (memo eviction), §4.10 (the read path could still
raise), §4.6 (tmp orphan on ENOSPC), §5 (`Path.print` does not produce `~~/…`; warning
timing), §6.2/§6.3 (two withdrawn arguments against redirect).

All line numbers refer to
`/home/qiyuan/Current/MLML/contrib/auto_sledgehammer/library/cache_file.ML`
at the state of commit `5fab892` (branch `main`).

---

## 0. Problem statement and the one correction to the brief

`cache_file.ML:223-225` derives the cache path from the theory's own directory:

```sml
fun cache_path thy =
      Path.append (Resources.master_directory thy) (Path.basic (Context.theory_name {long=false} thy))
   |> Path.ext "proof-cache"

fun lock_path thy = Path.ext "lock" (cache_path thy)   (* <thy>.proof-cache.lock *)
```

Under the conda package (`conda/recipe.yaml`) the session source is installed at
`$PREFIX/share/auto-sledgehammer`, so `Resources.master_directory thy` is that directory.
It may be read-only, or shared between users. `conda/recipe.yaml` already documents this as
a KNOWN ISSUE in a comment under `requirements`:

> the proof cache is written next to the theory. `library/cache_file.ML:223-225` derives it
> from `Resources.master_directory thy`, which under conda is
> `$PREFIX/share/auto-sledgehammer` -- a directory that may be read-only or shared between
> users.

**Correction to the brief.** The brief states that "two such files are committed in this
repo". They are **not**. `.gitignore:20-23` explicitly ignores them:

```
Auto_Sledgehammer_Doc.proof-cache
Auto_Sledgehammer.proof-cache
*.proof-cache.lock
*.proof-cache.tmp*
```

and commit `c20b346` ("Harden proof-cache: pid-unique temp, atomic invalidate, **untrack
cache**") is what removed them from tracking. `git ls-files | grep -i cache` returns only
`library/cache_file.ML`. The files present on disk

```
-rw-rw-r-- 0 Jul 16 21:30 Auto_Sledgehammer.proof-cache
-rw-r--r-- 0 Jun 20 01:35 Auto_Sledgehammer.proof-cache.lock
-rw-r--r-- 0 Jul  7 00:01 AS_Validate.proof-cache.lock
```

are untracked build residue (and all three are zero bytes). This materially changes §6:
there is **no** git-committed shipped cache whose location must be preserved, so the
"redirect" option is less disruptive than the brief assumed. It is still not free — see §6.

Desired behaviour (per the user): if the cache cannot be written, **do not write it, and do
not raise**. Reading an existing cache must keep working.

### 0.1 Blast radius — smaller than it looks, and this scopes the whole document

`cache_path` is derived **per theory**, from *that theory's* `master_directory`. So the
affected set is exactly the theories whose master directory lies under the read-only
prefix. Today that is **one theory: the shipped `Auto_Sledgehammer.thy`** — which contains
no `auto_sledgehammer` invocation and therefore never records anything, so its cache is
always empty.

A conda user's own theories live in the user's own directories and cache next to their own
sources. They are **not** affected by a read-only `$PREFIX` at all.

This corrects a framing used earlier in the design discussion, that "skip when read-only"
would mean conda users get no caching. It would not. Concretely, the failure being fixed
is: the unconditional `Theory.at_end` hook enters `with_file_lock` **before** the
emptiness test, so merely *loading* the shipped theory from a read-only prefix raises.
That also explains why §4.5 puts the guard **outside** `with_file_lock` rather than inside
it — inside is too late.

Keep this scope in mind when reading §6: it is why redirect buys much less than it appears
to.

---

## 1. Complete inventory of write / mutate sites

I read the whole file (510 lines). Every filesystem-mutating operation, in file order:

| # | Line(s) | Enclosing function | Operation | Path touched |
|---|---------|--------------------|-----------|--------------|
| W1 | 252 | `write_state_new` | `File.write tmp payload` — creates `<thy>.proof-cache.tmp.<pid>` | temp file in cache dir |
| W2 | 253 | `write_state_new` | `OS.FileSys.rename {old = …tmp, new = …path}` | cache dir (unlink + link) |
| W3 | 275-277 | `with_file_lock` | `Posix.FileSys.createf (…, O_RDWR, …, lock_smode)` — **creates the lock file if absent, and opens it O_RDWR even if present** | `<thy>.proof-cache.lock` |
| W4 | 280 | `with_file_lock` | `Posix.IO.setlkw (fd, F_WRLCK)` — blocking fcntl write lock | lock file (kernel state, not disk content) |
| W5 | 284 | `with_file_lock` | `Posix.IO.close fd` — already wrapped in `Exn.capture`, cannot escape | lock fd |
| W6 | 307 | `ensure_new_format` | `File.rm path` when the existing file is not new-format | cache file |
| W7 | 319 | `append_record` | `File.append path bytes` — the single durable-write funnel | cache file |
| W8 | 380 | `invalidate_cache` | `File.rm (cache_path thy)` | cache file |

Note W3 is *not* only a create: `Posix.FileSys.createf` with `O_RDWR` fails with `EACCES`
even when the lock file already exists but is mode `0444`, so both the "read-only
directory" and the "read-only file" cases hit it.

**Callers that reach these sites** (so we know which entry points must be guarded):

- `append_record` (313-321) → W3, W4, W6, W7. Called from
  `update_cached_proof:393` and `invalidate_proof_cache:407`.
- `compact_cache` (326-333) → W3, W4, W1, W2. Called from `store_cache:366` and from the
  `Theory.at_end` hook at `447-457` (both the synchronous branch at 449 and the deferred
  `Future.forks` branch at 452-454).
- `invalidate_cache` (376-383) → W3, W4, W8.

**Pure-read sites** (must keep working unchanged):

- `read_file_state:232-238` — `File.is_file`, `Bytes.read`.
- `read_header:257-258` — `File_Stream.open_input`.
- `load_cache_raw:338-339`, `get_cache_i:346-350`, `force_reload:341-344`,
  `get_cached_proof:385`.

**Nothing outside `cache_file.ML` writes these paths.** Verified by grepping the whole
`MLML` tree for `proof-cache`, `proof_cache`, `cache_path`, `lock_path` across
`*.ML`/`*.thy`/`*.py`/`*.scala`. Hits, and their nature:

- `library/sledgehammer_solver.ML` — only via the `Phi_Cache_DB` API
  (`get_cached_proof:1307`, `update_cached_proof:1329`, `update_hash_cache:1328`,
  `invalidate_proof_cache:1367`, `register_async_task:712`, `enable_proof_cache:1034,1347`).
- `contrib/Isa-REPL/library/sledgehammer.ML:253` — `Phi_Cache_DB.invalidate_proof_cache`.
- `contrib/Isa-Mini/Agent/agent_server.ML:332,342,397,1326-1327` — its own
  `AoA_use_proof_cache` / `AoA_store_proof_cache` configs, plus
  `Config.put Phi_Cache_DB.enable_proof_cache false`. No path access.
- `contrib/Isa-Mini/IsaMini/AoA/proof_cache.py` — an unrelated **sqlite** cache
  (`aoa_proof_cache.db`); shares only the word "cache".
- `Auto_Sledgehammer_Doc.thy`, `Test/Test_Ground_Eval.thy`, `Test/Test_Staged_Fastforce.thy`,
  and the AoA `Tests/*.thy` — mention `enable_proof_cache` only.

So the fix is entirely contained in `cache_file.ML`, and specifically in three functions:
`with_file_lock`'s callers, `append_record`, `compact_cache`, `invalidate_cache`.

---

## 2. Detection strategy

### 2.1 What the environment actually offers (verified, not assumed)

Checked `/home/qiyuan/Current/MLML/contrib/Isabelle2025-2/src/Pure/General/file.ML`. The
relevant part of the `FILE` signature is: `standard_path`, `platform_path`, `bash_path`, `bash_paths`,
`bash_platform_path`, `absolute_path`, `full_path`, `tmp_path`, `exists`, `rm`, `is_dir`,
`is_file`, `check_dir`, `check_file`, `fold_dir`, `read_dir`, `read`, `read_lines`,
`write`, `append`, `write_list`, `append_list`, `eq`.

**There is no writability predicate in `File`.** `File.exists` is
`can OS.FileSys.fileId o platform_path` (`file.ML:92`) — existence only.
`Isabelle_System` (`src/Pure/System/isabelle_system.ML:16-23`) offers `make_directory`,
`copy_file`, `create_tmp_path`, `with_tmp_file`, `rm_tree`, `with_tmp_dir` — no
writability predicate either, and `make_directory:139` round-trips through
`Scala.function`, which is heavier than we want.

`OS.FileSys.access` **is** available and behaves as required. Verified by running under
this exact distribution:

```
$ contrib/Isabelle2025-2/bin/isabelle ML_process -e 'use ".../p.ML";'
A_WRITE /tmp: true
A_WRITE /: false
A_WRITE missing: false
```

Two facts from that run matter:

1. `OS.FileSys.access` exists in this Poly/ML and honours real permissions.
2. It returns **`false` for a nonexistent path**. Therefore probing the *cache file*
   directly is wrong when the cache does not exist yet — that is the ordinary first-run
   case and would be misread as "read-only". The **directory** must be probed for the
   create case, and the **file** only when it exists.

`\<^try>\<open>… catch _ => …\<close>` is also confirmed available and correct here. Its
expansion is `Isabelle_Thread.try_catch`
(`src/Pure/ML/ml_antiquotations.ML:369-385`), defined at
`src/Pure/Concurrent/isabelle_thread.ML:180-183`:

```sml
fun try_catch e f =
  Thread_Attributes.uninterruptible_body (fn run =>
    run e () handle exn =>
      if Exn.is_interrupt exn then Exn.reraise (check_interrupt exn) else f exn);
```

i.e. it swallows ordinary exceptions but **re-raises interrupts** — exactly the property a
best-effort write wrapper needs, and the idiom this file already uses at line 236.

### 2.2 Up-front probe vs. try-and-catch at each site

**Try-and-catch alone is not sufficient**, for three reasons:

1. `with_file_lock` (272-286) fails at W3, i.e. *before* the body runs. A per-site
   `\<^try>` inside the body never executes. We would have to wrap the whole
   `with_file_lock` call — at which point we are already changing the same three call
   sites the probe approach changes, so try-and-catch buys no locality.
2. `append_record:316-320` runs inside `Synchronized.change v`, whose result is the
   `confirmed` flag. Swallowing an exception there must still yield a `bool`; the natural
   answer (`false`) means "re-probe the format next time", i.e. we would retry the failing
   `open` on every single proof. On a read-only prefix with a proof-heavy theory that is
   one `EACCES` syscall pair per proof, forever.
3. W2 (`OS.FileSys.rename`) can fail *after* W1 succeeded, leaving a stray
   `.proof-cache.tmp.<pid>`. Catching there needs a cleanup path anyway.

**Probe-only is also not sufficient**, because the probe is TOCTOU-racy (a directory can be
remounted read-only, or the file `chmod`ed, between probe and write) and because probing
cannot anticipate `ENOSPC`, `EROFS` on a bind mount, NFS `EACCES`, etc.

**Recommendation: both, layered.**

- A **cheap up-front probe, computed once per theory and memoised**, decides whether we
  even attempt writes. This is the primary mechanism and gives us a single, well-timed
  place to emit the user-facing warning (§5).
- A **`\<^try>` wrapper at the write funnel** is the safety net for everything the probe
  cannot foresee. It must not warn (it would be unbounded) — it silently degrades, and the
  memoised verdict is flipped to `false` so subsequent proofs stop retrying.

### 2.3 What exactly to probe

Both directions the brief names must be handled:

- **read-only dir, writable-or-absent file**: the lock file (W3) and the compaction temp
  file (W1) cannot be created. Even if `<thy>.proof-cache` happened to exist mode `0666`,
  `File.append` on it would succeed but the *lock* would not, so `append_record` still
  fails. → **the directory must be writable, unconditionally.**
- **writable dir, read-only existing cache file**: `File.append` (W7) fails with `EACCES`;
  `File.rm` (W6, W8) *succeeds* (unlink needs only directory write permission) — which
  would be worse than failing, because a "graceful" path must not delete a read-only cache
  the admin deliberately shipped. → **if the cache file exists, it must itself be
  writable.**

So the predicate is:

```
writable(thy)  ==  dir is a directory
              AND  access(dir, [A_WRITE, A_EXEC])
              AND  (not exists(cache_file) orelse access(cache_file, [A_WRITE]))
              AND  (not exists(lock_file)  orelse access(lock_file,  [A_WRITE]))
```

`A_EXEC` on the directory is required for traversal (creating a file needs both write and
search permission). The lock file is checked because W3 opens it `O_RDWR`; a mode-`0444`
lock file left behind by a root-run build in a world-writable directory would otherwise
fail every write. (Both `.lock` files currently on disk here are mode `0644` and one of
them, `AS_Validate.proof-cache.lock`, has no corresponding data file at all — evidence that
lock files outlive caches and must be checked independently.)

### 2.4 Cost

Three `access(2)` calls plus two `stat(2)` (via `File.exists`) per **theory**, not per
proof. The verdict lives in the same `Symtab` keyed by long theory name that
`append_vars` already uses (292-300), so the steady-state cost of a proof that writes is
one `Symtab.lookup` under a `Synchronized.var` — identical to what `append_record` already
pays at line 315. This satisfies "must not stat on every single proof".

The verdict is computed **lazily, at the first write site that needs it** (§4.4/§4.5/§4.7),
not eagerly at load time. `load_cache_raw` (338-339) would be the natural place to compute
it *early*, but doing so puts a filesystem probe on the load path of every theory —
including the overwhelming majority whose directory is perfectly writable and which will
never consult the verdict. The cost of laziness is only that the warning may arrive late
(see §5, "Timing"); the cost of eagerness is paid by everyone.

---

## 3. Concurrency and the lock file

The invariant we must preserve: **the fcntl lock is only ever needed to protect a write.**
No read path calls `with_file_lock` — verified: `read_file_state:232`, `read_header:257`,
`load_cache_raw:338`, `get_cached_proof:385` take no lock. Compaction reads *under* the
lock (331) but only because it then rewrites.

Therefore, when the directory is not writable:

**The lock is simply never acquired, because no write is ever attempted.** We do not need a
"lock-free write" mode, a fallback lock location, or a timeout.

Concretely: the guard goes **outside** `with_file_lock`, at each of the three call sites
(317, 330, 379), not inside it. `with_file_lock` itself is left byte-for-byte unchanged.
That is what makes deadlock and busy-wait structurally impossible:

- No `Posix.IO.setlkw` is ever entered, so there is nothing to block on. (A retry loop
  around `createf` would be the busy-wait trap; we have none.)
- The in-process `Synchronized.change v` mutex (316, 329, 378) is still taken and still
  released — the guarded body just returns immediately. We must keep taking it, because it
  is also the carrier of the `confirmed` flag and of the invalidate/append ordering
  documented at 371-375; skipping it would be a lock-protocol change, not a no-op.
- The documented lock order `v -> fcntl -> openning_caches` (373-374) is preserved: we drop
  the middle link, never reorder.
- `invalidate_cache` (376-383) must still perform its **in-memory** half
  (`Synchronized.change openning_caches …` at 381) even when the disk half is skipped.
  Skipping only the `with_file_lock`/`File.rm` at 379-380 leaves the in-memory invalidation
  intact, which is the correct semantics: a bad cached proof is dropped for this session
  even though we cannot record the tombstone durably.

One residual hazard worth stating explicitly: on a **shared, writable** directory
(multi-user machine, not read-only) nothing changes — the existing fcntl protocol already
covers it. This plan does not attempt to fix cross-user permission churn on a shared
writable cache (user A creates `0644`, user B cannot append). §2.3's file-level check
*detects* that case and degrades gracefully rather than raising, which is the requested
behaviour, but the two users will not share a cache. If shared-cache-across-users is
wanted, that is the redirect option in §6, not this one.

---

## 4. Exactly what to change

Style follows the surrounding file and `.claude/skills/isabelle-ml-style`: 2-space nesting,
`thy` for theories, `\<^try>\<open>… catch _ => …\<close>` as already used at line 236,
comment blocks in the same voice as 240-246 / 260-264 / 302-312.

### 4.1 New: the writability probe and its memo (insert after `lock_path`, i.e. after line 227)

```sml
(* Whether the cache directory (and, if they already exist, the data and lock files)
   admit the writes this module performs: creating the lock file and the compaction
   temp file, appending to the data file, unlinking it.  Probed with access(2) --
   Isabelle's File structure has no writability predicate (see Pure/General/file.ML),
   and File.exists only answers existence.

   Note access(2) answers false for a path that does not exist, so the DIRECTORY is
   the thing to probe for the create case; the files are probed only when present.
   A read-only data file matters even under a writable directory: File.append would
   fail, while File.rm would succeed -- and silently deleting a deliberately
   read-only cache is worse than not writing at all. *)
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
```

`accessible` is wrapped in `\<^try>` because `OS.FileSys.access` raises `OS.SysErr` on a
dangling symlink or an unreadable parent directory; `\<^try>` re-raises interrupts
(`isabelle_thread.ML:180-183`), so this cannot swallow a cancellation.

### 4.2 New: the memo var, mirroring `append_vars` (insert after `theory_append_var`, i.e. after line 300)

```sml
(* Per-theory writability verdict, probed once (see probe_writable) and cached
   alongside the append vars.  A write that fails anyway -- a race with a remount,
   ENOSPC, an NFS refusal -- flips the entry to false via note_write_failure, so we
   stop paying a doomed open() per proof. *)
val writable_vars : bool Symtab.table Synchronized.var =
  Synchronized.var "phi_cache.writable" Symtab.empty

fun cache_is_writable thy =
  let val name = Context.theory_name {long=true} thy
   in Synchronized.change_result writable_vars (fn tab =>
        case Symtab.lookup tab name of
          SOME b => (b, tab)
        | NONE =>
            let val b = probe_writable thy
                val _ =
                  if b then ()
                  else warning ("Proof cache for theory " ^ name ^ " is not writable (" ^
                                Path.print (cache_path thy) ^
                                "); cached proofs will be read but not recorded.")
             in (b, Symtab.update_new (name, b) tab) end)
  end

fun note_write_failure thy =
  Synchronized.change writable_vars
    (Symtab.update (Context.theory_name {long=true} thy, false))
```

Emitting the `warning` inside `change_result` means it fires exactly once per memo entry.

#### 4.2a The memo entry MUST be evicted, or a false verdict is permanent

`Synchronized.change_result` is `guarded_access var (SOME o f)`
(`Pure/Concurrent/synchronized.ML:14-16, :96`) — it applies `f` exactly once, so an entry
is never re-probed. Nothing above removes entries. Two consequences, both silent:

- **No recovery.** In a long-lived process (PIDE/jEdit, an Isa-REPL server) a user who sees
  the warning, runs `chmod u+w`, and re-checks the same theory takes the `SOME` branch and
  still gets no caching — and no second warning, because the warning lives only on the
  `NONE` branch. Only a process restart helps.
- **Cross-theory leak.** The key is the theory name, so two ad-hoc theories from different
  master directories can share one. A poisoned verdict from a read-only directory then
  disables caching for a perfectly writable one.

The file already solves exactly this for the sibling per-theory table: `store_and_close_cache`
(`cache_file.ML:368-369`) does `Symtab.delete_safe` on `openning_caches` at theory end. Do
the same, right next to it:

```sml
(* in store_and_close_cache, alongside the existing openning_caches deletion *)
val _ = Synchronized.change writable_vars (Symtab.delete_safe name)
```

`writable_vars` is a **leaf** lock — `probe_writable` takes none — so this adds no cycle to
the `v -> fcntl -> openning_caches` order documented in §3.

Two caveats to carry into the implementation:

- In the deferred `Future.forks` branch (`cache_file.ML:452-454`) `store_and_close_cache`
  runs asynchronously, so the name-collision half of this fix is best-effort.
- Per-theory-instance eviction re-arms the warning on every re-check. Pair it with a
  separate **process-global "already warned" set keyed on `Resources.master_directory thy`**
  so the warning stays once-per-location rather than once-per-check.

Do **not** key the *verdict* on the master directory: §2.3's predicate is per-file (it
probes `cache_path` and `lock_path` individually), and §7.2 case D is precisely a writable
directory holding a non-writable cache file.

### 4.3 New: the best-effort write wrapper (insert immediately after `note_write_failure`)

```sml
(* Run a durable-write body only if the cache location is writable, and never let a
   filesystem failure escape into the proof: a cache is an optimisation.  A failure
   demotes the theory to non-writable so we do not retry once per proof. *)
fun try_write thy body =
  if not (cache_is_writable thy) then ()
  else \<^try>\<open>body () catch _ => note_write_failure thy\<close>
```

### 4.4 `append_record` (313-321)

Before:

```sml
fun append_record thy bytes =
  let val path = cache_path thy
      val v = theory_append_var (Context.theory_name {long=true} thy)
   in Synchronized.change v (fn confirmed =>
        with_file_lock (lock_path thy) (fn () =>
          ((if confirmed then () else ensure_new_format path);
           File.append path bytes;
           true)))
  end
```

After:

```sml
fun append_record thy bytes =
  let val path = cache_path thy
      val v = theory_append_var (Context.theory_name {long=true} thy)
   in Synchronized.change v (fn confirmed =>
        if not (cache_is_writable thy) then confirmed
        else \<^try>\<open>
          with_file_lock (lock_path thy) (fn () =>
            ((if confirmed then () else ensure_new_format path);
             File.append path bytes;
             true))
          catch _ => (note_write_failure thy; confirmed)\<close>)
  end
```

Note this one cannot use `try_write`: its body returns the `confirmed : bool` the
`Synchronized.change` must produce, not `unit`. Returning the *incoming* `confirmed`
(rather than `false`) on failure is deliberate — a previously confirmed format stays
confirmed, and an unconfirmed one is not falsely upgraded.

### 4.5 `compact_cache` (326-333)

Before:

```sml
fun compact_cache thy =
  let val path = cache_path thy
      val v = theory_append_var (Context.theory_name {long=true} thy)
   in Synchronized.change v (fn _ =>
        with_file_lock (lock_path thy) (fn () =>
          (if File.is_file path then write_state_new path (read_file_state path) else ();
           true)))
  end
```

After:

```sml
fun compact_cache thy =
  let val path = cache_path thy
      val v = theory_append_var (Context.theory_name {long=true} thy)
   in Synchronized.change v (fn confirmed =>
        if not (cache_is_writable thy) then confirmed
        else \<^try>\<open>
          with_file_lock (lock_path thy) (fn () =>
            (if File.is_file path then write_state_new path (read_file_state path) else ();
             true))
          catch _ => (note_write_failure thy; confirmed)\<close>)
  end
```

This is what protects the `Theory.at_end` hook (447-457), including the deferred
`Future.forks` branch at 452-454 — an uncaught `IO.Io` inside that future would surface as
a spurious error long after the theory finished.

### 4.6 `write_state_new` (247-254) — tmp cleanup

W1/W2 are now only reached under `compact_cache`'s guard, so they cannot raise into the
user. But a failure at W2 after a success at W1 leaves `<thy>.proof-cache.tmp.<pid>` behind.
`.gitignore:23` already ignores `*.proof-cache.tmp*`, so this is cosmetic in-repo, but
in a shared prefix it accumulates. Recommended tightening:

Before (252-253):

```sml
   in File.write tmp payload;
      OS.FileSys.rename {old = File.platform_path tmp, new = File.platform_path path}
  end
```

After — note the guarded region **includes `File.write`**, which an earlier draft left
outside it:

```sml
   in \<^try>\<open>
        (File.write tmp payload;
         OS.FileSys.rename {old = File.platform_path tmp, new = File.platform_path path})
        catch exn => (\<^try>\<open>File.rm tmp\<close>; Exn.reraise exn)\<close>
  end
```

`File.write` must be inside, because that is where the orphan is actually created.
`File.write` = `File_Stream.open_output` = `with_file BinIO.openOut BinIO.closeOut`
(`file.ML:132,135`; `file_stream.ML:29-41`): it creates/truncates the file, `Exn.capture`s
the body, closes, then re-raises — **nothing unlinks on failure**. Measured on Isabelle2025-2:
a mid-write failure left a 7-byte `X.proof-cache.tmp.999` on disk, and `File.write` to
`/dev/full` raises `Io{SysErr("No space left on device", ENOSPC), function = "output"}` —
`function = "output"` proves the `open` had already succeeded, so on a real ENOSPC the tmp
file exists. ENOSPC is also the failure class §2.2/§4.2 name as `note_write_failure`'s
reason, so this branch is in scope by the plan's own reasoning.

The rethrow keeps `compact_cache`'s handler in charge of the verdict; only the orphan is
cleaned. The bare inner `\<^try>\<open>File.rm tmp\<close>` (no `catch`) expands to
`Isabelle_Thread.try`, which yields an `option` — so a `File.rm` failure when `tmp` was
never created (EACCES/EROFS at open, the primary read-only-prefix case) is harmlessly
discarded. `\<^try>…catch` re-raises interrupts (`isabelle_thread.ML:180-183`), so cleanup
will not fire on cancellation.

### 4.7 `invalidate_cache` (376-383)

Before:

```sml
fun invalidate_cache thy =
  let val name = Context.theory_name {long=true} thy in
  Synchronized.change (theory_append_var name) (fn _ =>
    (with_file_lock (lock_path thy) (fn () =>
       if File.is_file (cache_path thy) then File.rm (cache_path thy) else ());
     Synchronized.change openning_caches (Symtab.update (name, (empty_cache, true)));
     false))
  end
```

After:

```sml
fun invalidate_cache thy =
  let val name = Context.theory_name {long=true} thy in
  Synchronized.change (theory_append_var name) (fn _ =>
    (try_write thy (fn () =>
       with_file_lock (lock_path thy) (fn () =>
         if File.is_file (cache_path thy) then File.rm (cache_path thy) else ()));
     Synchronized.change openning_caches (Symtab.update (name, (empty_cache, true)));
     false))
  end
```

The in-memory reset at 381 and the `false` result at 382 are unchanged and unconditional —
see §3.

### 4.8 `ensure_new_format` (305-307)

No change. Its `File.rm` (W6) is reached only from inside `append_record`'s guarded body.
It is worth stating in a comment that this is now only reached under the writability guard,
so that a future reader does not "helpfully" call it from a read path.

### 4.9 Sites deliberately NOT changed

- `with_file_lock` (265-286) — unchanged, per §3.
- `read_header`, `load_cache_raw`, `force_reload`, `get_cache_i`, `get_cache`,
  `get_cached_proof` — read paths, must keep working on a read-only prefix that ships a
  good cache.
- `read_file_state` — **one change, see §4.10.** It is a read path, but as written it can
  still raise, which would defeat the whole point of this plan.

### 4.10 `read_file_state` (232-238) — the read path can still raise

This is the gap that matters most, because **the read always happens before any write**, so
the write-side probe of §4.2 never runs and cannot help.

As written, the guard is `File.is_file` (`:233`) and the `\<^try>` covers only
`replay (scan raw)` (`:236`) — `Bytes.read` (`:235`) sits **outside** it:

```sml
fun read_file_state path =
  if not (File.is_file path) then Symtab.empty
  else
    let val raw = Bytes.content (Bytes.read path)
     in if is_new_format raw then \<^try>\<open>replay (scan raw) catch _ => Symtab.empty\<close>
        else Symtab.empty
    end
```

Failure, in exactly the scenario this plan exists for: a **shared** `$PREFIX/share/auto-sledgehammer`
where user A primed `Foo.proof-cache` under `umask 077` (mode 0600, owner A). User B runs
`by auto_sledgehammer`: `File.is_file` is true, and `Bytes.read` raises
`Io{SysErr("Permission denied", EACCES), function="BinIO.openIn"}`. `get_cached_proof`
(`:384`) is called from `sledgehammer_solver.ML:1306` with **no handler**, and `auto`'s
`\<^try>` re-raises non-`Auto_Fail` exceptions — so the `Io` surfaces as an error inside the
user's proof.

Narrow (it needs a non-default umask; 0644/0664 caches are fine), but it is a hard error in
a proof, and the fix is one line — widen the existing `\<^try>` to cover the whole body,
which preserves its documented "a decode failure degrades to empty" contract:

**After:**

```sml
fun read_file_state path =
  if not (File.is_file path) then Symtab.empty
  else \<^try>\<open>
    let val raw = Bytes.content (Bytes.read path)
     in if is_new_format raw then replay (scan raw) else Symtab.empty end
    catch _ => Symtab.empty\<close>
```

`\<^try>` re-raises interrupts (`isabelle_thread.ML:180-183`), so this stays Timeout-safe.

Do **not** add `A_READ` to `probe_writable`: that predicate answers writability, and a
mode-0222 file is genuinely appendable. Once the read degrades to empty, §5's "cached
proofs will be read but not recorded" remains accurate.
- `hash_cache` and friends (461-472) — purely in-memory, unaffected.
- The `PHI_CACHE_DB` signature (137-192) — no change. This is important: `sledgehammer_solver.ML`,
  `Isa-REPL/library/sledgehammer.ML:253` and `Isa-Mini/Agent/agent_server.ML` all bind
  against it, and a signature change would ripple into three other repos.

---

## 5. What the user should see

The codebase already uses two channels, and they are used for different registers:

- `warning` — `cache_file.ML:397` (`report_cache_is_outdated`) and
  `sledgehammer_solver.ML:1366` ("A cached proof fails. Re-searching proofs...").
- `tracing` — `cache_file.ML:450, 454` (compaction deferral / completion),
  and `update_cache_by_hash:475`.

`warning` is the right channel: a silently disabled cache changes user-visible performance,
so it belongs in the yellow band, not in tracing (which is off by default in many
front-ends).

**Message, once per theory**, emitted from `cache_is_writable` (§4.2) on the miss branch:

```
Proof cache for theory Foo is not writable ("/home/user/miniconda3/envs/isa/share/auto-sledgehammer/Foo.proof-cache");
cached proofs will be read but not recorded.
```

Wording notes:
- Names the theory, matching `report_cache_is_outdated:397`'s existing phrasing
  ("Proof cache for theory " ^ name ^ " is …").
- The path is the **raw absolute path, in quotes** — that is exactly what `Path.print`
  emits (`path.ML:194-198`: `print_markup` quotes `implode_path`; no rewriting). An earlier
  draft of this section claimed `Path.print` renders a symbolic `~~/…` form. It does not.
  Symbolic rewriting lives only in `File.symbolic_path` (`file.ML:49-68`), and even that
  returns the raw path here, because a conda `$PREFIX/share` matches no entry of
  `ISABELLE_DIRECTORIES` (`~`, `$ISABELLE_HOME_USER`, `~~`, `$ISABELLE_COMPONENTS_BASE`,
  `$AFP_BASE`, `$AFP`). `~~` denotes `ISABELLE_HOME`, and a conda `$PREFIX` is not
  `ISABELLE_HOME`, so the symbolic form is unobtainable for this path by any function.
  Keep `Path.print`: the quoted absolute path is precisely what a user needs in order to
  `ls -ld` the directory and diagnose a false verdict (§8).
- Explicitly says reads still work, so the user does not conclude the cache is dead.

**Timing.** The warning is emitted from `cache_is_writable`'s miss branch, which is reached
only from the three write sites of §4.4/§4.5/§4.7. So on a theory whose proofs are **all
cache hits**, no write site is reached during the body and the warning arrives at theory
end — or, in the deferred-compaction path, from a detached future. An earlier draft of §2.4
promised it arrives "once, early, and in the theory's own output"; that promise is
withdrawn. Probing eagerly in `load_cache_raw` to restore it is deliberately **not** done:
it would move a filesystem probe onto the load path of every theory, including the vast
majority that are unaffected.

**How spam is avoided.** The message is emitted inside
`Synchronized.change_result writable_vars` on the `NONE` branch only. The entry is inserted
in the same atomic step, so every subsequent lookup takes the `SOME` branch and is silent.
Concurrent first-touch from sibling threads is serialised by the `Synchronized.var`, so
exactly one thread can be on the `NONE` branch.

`note_write_failure` (the safety net) deliberately does **not** warn. It fires only in
races and exotic filesystem failures where the up-front probe said "writable"; warning there
would be unbounded in the pathological case and confusing in the common one. If a
diagnostic is wanted, `tracing` is the appropriate channel — but I recommend silence,
because the probe already covers every case a user can act on.

**Do not** use `Output.warning` directly: `warning` is the standard Isabelle/ML entry point
and is what this file already uses.

---

## 6. The alternative: redirect to `ISABELLE_HOME_USER`

### 6.1 What it would look like

`ISABELLE_HOME_USER` is per-conda-env (the base package patches it to
`~/.isabelle/Isabelle2025-2-conda-<env>`), always writable, and per-user. Referring to it
from ML is well-trodden in the distribution itself — e.g.
`HOL/Tools/Sledgehammer/sledgehammer_mash.ML:132`
(`Path.expand (Path.explode "$ISABELLE_HOME_USER/mash_state")`),
`sledgehammer_util.ML:146`, `HOL/Tools/SMT/smt_replay.ML:294`,
`HOL/Library/code_test.ML:142`. So the mechanism is idiomatic.

The change would be confined to `cache_path` (223-225):

```sml
fun cache_path thy =
  let val local_path =
        Path.append (Resources.master_directory thy)
          (Path.basic (Context.theory_name {long=false} thy))
        |> Path.ext "proof-cache"
   in if writable local_path then local_path
      else Path.expand (Path.explode "$ISABELLE_HOME_USER/proof-cache")
             + Path.basic (<key>) |> Path.ext "proof-cache"
  end
```

plus one `Isabelle_System.make_directory` for the redirect directory.

### 6.2 Evaluation

**Correctness.** The headline benefit is much smaller than it first appears — see §0.1.
Redirect does **not** rescue "conda users' caching", because conda users' own theories
already cache next to their own sources and are unaffected by a read-only `$PREFIX`. The
only cache under the prefix belongs to the shipped `Auto_Sledgehammer.thy`, which records
nothing and is therefore always empty. So redirect's real benefit today is: *nothing
observable*. Its honest future trigger is a **shipped session that carries real cached
proofs of its own**, or a read-only AFP / vendored / CI source tree — not the conda
packaging that motivated this document.

It also introduces a failure mode the current design does not have — the cache
becomes *stale relative to a source tree it no longer sits next to*. Today, deleting a
checkout deletes its cache; after redirect, a stale entry survives a `git checkout` of a
different branch. The append-log format's tombstones and the hash-keyed path
(`try_cached_proof_by_hash`, 486-508) mitigate this — a stale proof that no longer replays
is detected at `sledgehammer_solver.ML:1366` and invalidated — but the *proof-id* keyed path
(`get_cached_proof thy id`, `sledgehammer_solver.ML:1307`) is keyed on a document-derived id
whose collision behaviour across unrelated projects I have **not** verified. That is a real
gap in my analysis, not a rhetorical hedge.

**Collision across projects.** This is the decisive objection. `cache_path` keys on
`Context.theory_name {long=false}` — the **short** name. Two different projects each with a
`Utils.thy` would share one `$ISABELLE_HOME_USER/proof-cache/Utils.proof-cache`. Fixable —
key on `{long=true}`, or on a hash of `Resources.master_directory` — but that is a real
design decision with its own migration question (existing local caches are keyed the old
way and would all be missed once), not a one-line path swap.

**Code churn.** Larger than it looks. Beyond `cache_path`: the redirect directory must be
created (a `Scala.function` round-trip via `Isabelle_System.make_directory:139`, which adds
a Scala dependency to a module that currently has none); `lock_path` follows automatically
but now lives in a directory shared by every project, so lock-file naming must be
collision-free too; and the `.gitignore` entries (`.gitignore:20-23`) become dead.

**Existing in-repo workflow.** Here the brief's premise was wrong (§0) — the caches are
**not** committed, they are gitignored. So "redirect breaks the committed-cache workflow"
is not an argument that applies. What *does* apply: developers currently expect
`rm *.proof-cache` in the checkout to clear the cache, and expect the cache to travel with
(and die with) the working tree. Redirect silently breaks that muscle memory, and the
non-obvious new location makes "why is it still using a stale proof" much harder to debug.

### 6.3 Recommendation

**Implement "skip when read-only" (§4) now. Do not implement redirect now.** I agree with
the user, and not merely deferentially:

1. Skip is *strictly conservative*: it can only turn a crash into a no-op. Every existing
   workflow is bit-identical when the directory is writable, which is every current
   development setup. Redirect changes behaviour for **all** users to fix a problem only
   conda users have.
2. Redirect buys nothing observable today (§0.1, §6.2): the affected set is one shipped
   theory whose cache is always empty. That, not the collision question, is the decisive
   reason to defer it.

   (Two claims made in earlier drafts of this section have been **withdrawn** as
   unsupported. First, that cross-project sharing is "soundness-adjacent": it is not — the
   kernel re-checks every cached proof, so the worst case is a wasted replay, not an
   unsound theorem. Second, that a name collision is the decisive objection: entries are
   keyed by a content hash rather than by the short theory name, so a shared location is
   less dangerous than that argument assumed. Neither changes the recommendation; both were
   wrong reasons for a right answer, and are recorded here so they are not repeated.)
3. The skip fix is a prerequisite for redirect anyway — redirect still needs the exact same
   writability predicate to decide when to redirect, and still needs a non-raising fallback
   for the case where `ISABELLE_HOME_USER` is itself unwritable (read-only `$HOME`, CI
   sandboxes). Doing skip first is not wasted work; it is the first half.

**Suggested combination, as a later step.** Once §4 is in and the conda package ships
without erroring, add redirect as an *opt-in* behind a config, e.g.

```sml
val proof_cache_home = Attrib.setup_config_bool \<^binding>\<open>proof_cache_in_home\<close> (K false)
```

keyed on `Context.theory_name {long=true}` plus a digest of the master directory, with the
§4 skip logic as the fallback when the home location also fails. That sequencing lets conda
users opt into caching without imposing a location change on anyone else, and lets the
collision question be settled by measurement rather than by argument.

---

## 7. Test plan

### 7.1 Simulating a read-only directory

Preferred, no root required — copy the session into a scratch dir and drop write
permission:

```bash
cp -a contrib/auto_sledgehammer /tmp/as-ro
rm -f /tmp/as-ro/*.proof-cache /tmp/as-ro/*.proof-cache.lock
chmod a-w /tmp/as-ro
isabelle build -d /tmp/as-ro Auto_Sledgehammer
```

Do **not** run this as root: root bypasses `access(2)`'s DAC check for directories, so the
probe would report writable and the test would be vacuous. Verify with
`id -u` (must be nonzero) before trusting a green result.

For the read-only-file case, leave the directory writable and `chmod a-w` the
`.proof-cache` (and separately the `.lock`).

A stronger variant, if a real read-only mount is wanted:
`mount -o bind,ro` or a squashfs image. Not necessary for the DAC paths above, but it is the
only way to exercise `EROFS` (as opposed to `EACCES`), which is the code path
`note_write_failure` exists for.

### 7.2 Matrix and expected observable behaviour

| Case | Setup | Expected |
|------|-------|----------|
| A. Writable dir (baseline) | current checkout, unchanged | Byte-identical to today: cache created, appended, compacted at theory end. `git diff` of a regenerated cache against a pre-change one should be empty for the same proof set. **This is the most important test** — it is the no-regression case. |
| B. Read-only dir, no cache | `/tmp/as-ro`, caches removed, `chmod a-w` | Build succeeds. Exactly one `warning` per theory: "Proof cache for theory X is not writable …". No `.proof-cache`, no `.lock`, no `.tmp.<pid>` created. Every proof re-searched. |
| C. Read-only dir, valid cache present | populate the cache in a writable copy first, then `chmod a-w` the dir | Build succeeds and is **fast** — cache hits observable via `sledgehammer_solver.ML:1310` (`[auto'i] cache HIT`) with `sh_log` enabled. File mtime unchanged after the build (proves no write). **Warning timing:** on an all-hits theory no write site runs during the body, so the warning arrives at theory end, not at first use (see §5, "Timing") — assert that it appears, not *when*. |
| D. Writable dir, read-only cache file | `chmod a-w Auto_Sledgehammer.proof-cache` | Build succeeds, cache **read** (hits observable), one warning, and critically the file is **still present and still read-only** afterwards — this is the case where an unguarded `File.rm` (W6/W8) would have succeeded and destroyed it. |
| E. Writable dir, read-only lock file | `chmod a-w *.proof-cache.lock`, data file writable | One warning; no writes. (Without the lock-file clause of §2.3 this case raises.) |
| F. Race / demotion | make the dir writable, start a build, `chmod a-w` mid-build | No error surfaces. `note_write_failure` demotes; remaining proofs skip silently. Hard to time reliably — acceptable to verify by temporarily forcing `probe_writable` to return `true` and confirming the `\<^try>` arms catch. |
| G. Invalidation under read-only | case C plus a deliberately broken cached proof | `sledgehammer_solver.ML:1366` warns "A cached proof fails", `invalidate_proof_cache` runs, the proof is re-searched and succeeds, no exception, and the on-disk cache is **unchanged** (the tombstone could not be recorded). |
| H. Deferred compaction | a theory with async tasks (`register_async_task:712`) under a read-only dir | The `Future.forks` at 452-454 completes without a delayed error message. Exactly one message is emitted from the compaction future, and it must be a `warning`, **not** an error. This is the case most likely to be missed, because the failure would appear seconds after the theory finished. |
| I. Cache file exists but is **not readable** by this uid | populate the cache, then `chmod 600` it as another user (or `chown`), and build as a second user | Build succeeds; the cache is treated as **empty**; no `Io`/EACCES escapes into the proof. This is §4.10 — without that fix `Bytes.read` raises straight into the user's proof, and the write-side probe never gets a chance to help because the read happens first. |
| J. Memo eviction / recovery | under a long-lived process (Isa-REPL or jEdit): build case B, then `chmod u+w` the directory, then re-check the same theory | Caching **resumes**. Without the §4.2a eviction the verdict is memoised for the process lifetime and the user gets no caching and no second warning until restart. |

### 7.3 Unit-level check

`Proof_Cache_Format` is deliberately exposed without signature ascription (comment at
24-25: "so the format can be unit-tested directly"). The new `probe_writable` / `accessible`
live in `Phi_Cache_DB`, which **is** ascribed to `PHI_CACHE_DB` (195) and so cannot be
tested from outside. Options: (a) test only through the matrix above; (b) add
`val cache_is_writable : theory -> bool` to the signature. I recommend (a) — keeping the
signature stable matters (§4.9), and the matrix covers the behaviour.

---

## 8. Risks

**R1 — False "read-only" verdict silently disables caching for someone who should have it.**
The worst outcome of this change: proofs get slower with only a yellow warning to explain
it. Concrete triggers:
- Directory writable but non-searchable (`--x` missing). Handled: we probe `A_EXEC` too.
- ACLs / SELinux where `access(2)` and the actual `open(2)` disagree. `access(2)` uses the
  *real* uid, `open(2)` the *effective* one; under setuid they differ. Isabelle is not
  setuid, so this is theoretical, but it is the known weak spot of `access(2)`.
- Running as root: `access(2)` reports writable for a mode-`0444` directory, so root gets a
  probe "yes" and then a real failure — caught by the `\<^try>` net, degrading to silence
  rather than a warning. Acceptable; noted in §7.1 so tests do not run as root.
- **Mitigation**: the warning names the exact path, so a user can `ls -ld` it and see why.
  An alternative probe — actually creating and deleting a temp file — would be exact but
  costs a create+unlink per theory and, worse, *writes* into a directory we are trying to
  establish we may not write to. Rejected.

**R2 — Behaviour change for the in-repo development workflow.** In case A the code path is
`cache_is_writable → SOME true → identical body`. The only added cost is one probe per
theory (three `access` + two `stat`) and one `Symtab` lookup per write, against a
Sledgehammer invocation measured in seconds. No observable change. The residual risk is a
bug in the guard itself inverting the condition — hence case A is the highest-priority test.

**R3 — Losing invalidation durability.** Under read-only, `invalidate_proof_cache:400-407`
updates memory but its tombstone append is dropped. A bad cached proof therefore returns on
the next session, is re-detected at `sledgehammer_solver.ML:1366`, and is re-invalidated.
Correct but repeatedly slow. Unavoidable without a writable location — and it is precisely
the argument §6 makes for eventually offering redirect.

**R4 — The safety net hides real bugs.** `\<^try>\<open>… catch _ => …\<close>` at the write
funnel swallows *any* non-interrupt exception, including a genuine encoding bug in
`encode_put` or `write_state_new`. Before this change such a bug surfaced loudly. Two
mitigations, both cheap: keep the `\<^try>` scope as narrow as shown in §4 (it wraps only
`with_file_lock`/`File.append`, not the payload construction at 248-250 — note
`write_state_new`'s `String.concat`/`Symtab.fold` runs *inside* `compact_cache`'s guarded
body, so consider hoisting payload construction out of the guarded region); and, if
paranoia warrants, log via `tracing` in `note_write_failure` behind a debug flag.

**R5 — Warning fatigue on a many-theory read-only build.** One warning per theory means a
50-theory read-only build emits 50 warnings. Per-theory is still the right granularity
(the verdict is per-theory and could differ), but if this proves noisy, a process-global
"already warned about this directory" set keyed on `Resources.master_directory` would
reduce it to one per directory. Recommend shipping per-theory and revisiting if it annoys.

**R6 — Unverified claim, stated as such.** I did not verify the collision behaviour of the
proof-id key (`Phi_ID`-derived, `sledgehammer_solver.ML:1307`) across unrelated projects.
That matters only for §6's redirect option, not for the recommended §4 change, but it must
be settled before redirect is implemented.

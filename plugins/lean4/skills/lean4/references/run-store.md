# Run Store (`run-store/v1`)

**Status:** storage foundation for #82 (persisted proving state). This reference is the contract for the primitive `lean4-skills-run-store` (`lib/scripts/run_store.py`). It stores [`run-contract/v1`](handoff-contract.md) records durably; it does **not** wire them into any command, update Replan, or recover a restarted session — those are later work under #82, which stays open.

**Executable evidence:** `tests/test_run_store.py` (round-trip, arbitrary-JSON validator hardening, damaged-journal policy, cache staleness, fault injection at every durability step, competing locks, containment, Git behaviour). Check 43 pins this document's wording; the tests establish correctness.

## Layout

```
storage_root  = $LEAN4_RUN_STORE  or  <project-root>/.lean4-skills
run_directory = storage_root/runs/<run-id>
    manifest.json    run-store-manifest/v1  — written once, immutable
    events.jsonl     run-store-event/v1     — append-only journal, one object per line
    handoff.json     run-store-handoff/v1   — disposable cache of the latest handoff
    .lock, *.tmp     auxiliary (writer lock, uniquely named temp files)
```

**Manifest + journal are authoritative.** The cache is a convenience view the journal always overrides.

| File | Shape |
|---|---|
| `manifest.json` | `{schema, run_id, created, plugin_version, storage_root, tracker_session_id: string\|null, prior_run: run-id\|null, dispatch}` — `dispatch` is the first `run-contract/v1` dispatch record verbatim; it is **not** duplicated in the journal. `tracker_session_id` is nullable: no tracker is required. |
| `events.jsonl` | each line `{schema: "run-store-event/v1", seq, ts, kind, payload}`; `seq` starts at 1, dense, strictly increasing. `kind` ∈ `dispatch` (every redispatch after the first), `handoff` (the full record), `note`. `dispatch`/`handoff` payloads are unchanged `run-contract/v1` records validated by `run_contract_validate.py`. `note` payload: `{kind: candidate\|failed-avenue\|search-result\|blocker-diagnosis\|definition-gap\|source-note, text, lean: string\|null}`. |
| `handoff.json` | `{schema: "run-store-handoff/v1", seq, payload}` — absent until the first handoff. |

**Run boundary.** One command invocation is one run: its redispatches are `dispatch` events in the same journal. A later invocation creates a **new** run, optionally naming `prior_run`. "Rerun" below means only the latter.

**Run identity.** `run-id = <UTC yyyymmddThhmmssZ>-<8 hex of sha256(target|scope|mode|tracker_session_id-or-none|created)>`, fixed charset and length, validated before any path is built. `created` (and `--now`) must be exactly `YYYY-MM-DDTHH:MM:SSZ` — offsets, date-only, and fractional forms are refused (`bad_timestamp`); the stamp is zero-padded from components so any accepted year yields a loadable id. Creation reserves the directory exclusively; an existing directory is a `run_exists` error, never shared storage. On load or mutation the manifest's `run_id` must equal the directory's id, else `integrity_failure`.

## Journal integrity

- **Only an unterminated final fragment is recoverable**: `load` returns the validated prefix, reports `truncated_tail`, and leaves the bytes untouched. Excluded from the returned history never means deleted.
- A newline-terminated malformed line, a schema-invalid event, a `seq` gap, or a duplicate `seq` is **corruption**: `load` returns the valid prefix with `corrupt` at the offending line; nothing is rewritten.
- **Appending to a damaged journal is refused** (`journal_damaged`, exit 3) in either case. Recovery is a new run with `prior_run` set. A repair operation is deferred.
- A directory without a valid `manifest.json` is `incomplete_run` (never loaded, never appended to). A published manifest with a missing journal, or one whose `run_id` names another run, is `integrity_failure`, not an empty history.

## Reads are validated observed prefixes

`load` never locks. It captures the journal's size at open and reads only through that boundary; the result is a **validated observed prefix**, not a durably committed snapshot — a reader can see a complete line before its writer's `fsync`, and a trailing fragment observed concurrently is not proof of a crashed writer. A writer decides "damaged" only after acquiring the lock and re-reading.

The cache is disposable in the strong sense: any failure to read it — missing, malformed, a directory or FIFO where the file should be, a read error — is reported as `handoff_cache_stale` and never prevents loading the journal (cache opens are non-blocking, and only regular files are read). The manifest and journal keep their stricter treatment (`incomplete_run`, `journal_unreadable`).

**Effective handoff** = the last `handoff` event in the validated prefix. The cache is `current` only when its `seq` **and** payload equal that event; otherwise `load` reports `handoff_cache_stale` (missing, malformed, older, or disagreeing). A cache whose `seq` is ahead of the prefix never contributes history.

Persisted records use a **host-independent path grammar**: a stored `file_baseline` path is judged absolute by its serialized form (`/…`, `C:\…`, `C:/…`, `\\server\…`), never by the reading host's `os.path` (Python 3.13's Windows `isabs` rejects `/x`), so a POSIX-written run loads unchanged on Windows; host-local custody checks stay host-local. Results are emitted as UTF-8 with lone surrogates escaped, never a crash.

Loaded content is **historical evidence, never current certification**: `load` changes no trust status, authorizes no edit, and a stored `file_baseline` is never a custody check. A restarted session must inspect and reconcile source drift against the stored baseline (`lean4-skills-file-baseline check`) **before** recording a fresh one; recording a new baseline does not bless intervening changes. There is no `verified` state in v1.

## Durability, by operation

| Operation | Steps (in order) |
|---|---|
| `append` | serialize one complete UTF-8 JSON line (an unpaired surrogate is refused as `invalid_payload` before any change) → under the writer lock, **publication barriers first**: `fsync(run dir)` → `fsync(runs dir)` (a loadable run may have been left by a `create` that failed at its last barriers, and synchronizing the journal's bytes does not make the entries needed to reach it durable; a barrier failure is `publish_unsynced`, nothing appended) → `write` until every byte is written (short writes retried) → `fsync(journal)` → acknowledge |
| `set-handoff` | `append` as above → write a uniquely named temp + `fsync` → `rename` via the directory fd → `fsync(run dir)`. A failed rename removes its temp; temps are unique per attempt, so one failure never blocks the next replacement |
| store init (every `create`) | the parent of `storage_root` must already exist (`no_parent_anchor` otherwise — the store never creates an ancestor chain it could not synchronize) → `mkdir storage_root` / `mkdir runs` if missing → `fsync(storage_root)` → `fsync(parent of storage_root)`, **repeated on every `create`** because an existing entry does not prove an earlier publication reached disk; then publish `runs/.gitignore` if absent: unique temp + `fsync` → `link` into place (fails on an existing file, so user policy is never overwritten and a failed initialization leaves no half-written file) → `fsync(runs)`. Any failure here is a refusal (`store_init_unsynced`, `gitignore_write_failed`): no run exists yet |
| `create` | reserve `runs/<run-id>` exclusively → create + `fsync` the empty journal → write + `fsync` a uniquely named temp manifest → `rename` to `manifest.json` → `fsync(run dir)` → `fsync(runs dir)` → acknowledge; the creation lock is held through that final barrier |

On macOS, `F_FULLFSYNC` is attempted after `fsync` on **file** descriptors (directories get `fsync` only); its failure is reported, not ignored. Tests inject a failure at each step, and separate process-kill tests (SIGKILL at a chosen `fsync`) check the on-disk state a restarted process finds: a committed journal with a stale cache, a stale `.lock`, and possibly a leftover `*.tmp` — auxiliary residue that never blocks later operations.

**Write outcomes** (the wrapper's exit code in brackets):

| Outcome | Meaning |
|---|---|
| `committed` [0] | journal synchronized and, for `set-handoff`, cache replacement completed under the stated guarantees |
| `journal_only` [5] | journal synchronized; cache completion not confirmed |
| `nothing_written` [3] | this operation is known not to have changed the journal (validation, lock, platform, containment refusal; the refusal `code` says which) |
| `indeterminate` [6] | partial write or unconfirmed durability (`fsync` failed after bytes landed), or an unexpected `OSError` the store did not classify; inspect with `load` before any retry |

Two qualifications. `journal_only` does **not** guarantee the next `load` sees a stale cache: the rename may have landed before the directory sync failed. A process killed after committing but before returning yields **no** outcome. Callers reconcile with `load` before retrying; these outcomes are honest, not exactly-once delivery.

## Lock

One mutation (`create`, `append`, or `set-handoff` = append + cache replacement) holds `run_directory/.lock`, created with `O_EXCL`. **Any existing lock blocks** (`busy`, exit 3); its `{pid, host, acquired}` contents are diagnostic only and are never used to break a lock. v1 has no `--break-stale-lock`. Released on normal completion and handled failures — including a failure to write the lock's own contents (`lock_init_failed`), which removes the lock this operation created; a crash may leave a stale lock — recovery is manual: with no store process running, delete `.lock` (and any `*.tmp`). Readers do not lock (see above). Local Linux/macOS filesystems only; no distributed semantics are claimed.

## Platform boundary and containment

Mutations are implemented and tested for **Linux and macOS** (POSIX hosts with `dir_fd` support on `open`/`rename`/`mkdir`/`unlink`/`stat`/`link`); CI runs the storage suite on both. Elsewhere `create`, `append`, and `set-handoff` exit 3 `unsupported_platform` **before touching the filesystem**. `load` and `validate` work everywhere: on supported hosts `load` uses the same descriptor-relative path as mutations; elsewhere it uses a portable **read-only** path backend that refuses symlinked `storage_root`/`runs`/run directories and files by inspection (best effort, not race-proof — it never mutates). CI runs that path on Windows against the prebuilt fixture under `tests/fixtures/run_store/` and checks that a mutation there is refused without creating anything. A Windows mutation backend is a separate follow-up; realpath checks are never substituted under a claim of equivalent protection.

Containment covers the store's **own** filesystem operations: run ids are validated first; the **parent** of `storage_root` is the user's anchor (resolved with `realpath`, opened as given), and the `storage_root` entry, `runs`, `<run-id>`, and each file are opened relative to the already-open parent directory descriptor with `O_NOFOLLOW` (which guards only the final component of a single open, hence one open per component), so a symlinked `storage_root` — e.g. `project/.lean4-skills` pointing outside the project — is refused (`containment`) and a symlink swapped in after any check is still refused. Manifests record the resolved root. Paths inside stored dispatch/baseline payloads are data and are not checked.

## Git

**Ignored by default:** the first `create` publishes `storage_root/runs/.gitignore` containing `*` — only if no such file exists; an existing file is preserved verbatim (publication is by `link`, which cannot overwrite). Ignore rules never untrack an indexed file, so `create` **refuses** (`git_tracked`) when any path under `runs/` is already in the index of the repository that **contains the storage location** — whichever repository that is, not only the project's. Committing runs is not a v1 feature.

## CLI

```
lean4-skills-run-store [--root DIR | --project-root DIR] create      --dispatch FILE|- [--tracker-session-id ID] [--prior-run ID] [--now ISO]
lean4-skills-run-store [...]                              append      --run-id ID --kind dispatch|handoff|note --payload FILE|-
lean4-skills-run-store [...]                              set-handoff --run-id ID --payload FILE|-
lean4-skills-run-store [...]                              load        --run-id ID
lean4-skills-run-store                                    validate    --kind manifest|event|dispatch|handoff|note|cache FILE|-
```

Every command prints one `run-store-result/v1` (or `run-store-load/v1`) JSON object. Exit codes: 0 ok/committed, 2 usage or malformed input, 3 refused (nothing written), 5 `journal_only`, 6 `indeterminate`.

## Deferred (later PRs against #82)

Command wiring (cycle engine, prove/autoprove), Replan writes, handoff summaries referencing notes, restart reconciliation flow; then `/lean4:inspect`, `/lean4:resume`, dashboards, richer note types, a journal repair operation, and stale-lock breaking.

## See Also

- [handoff-contract.md](handoff-contract.md) — the records this store persists
- [cycle-engine.md § Run Contract](cycle-engine.md#run-contract-run-contractv1)
- `lean4-skills-file-baseline` — custody checks a restarted session must redo

# Handoff Contract (`run-contract/v1`)

The versioned protocol that binds the **parent**, **worker**, and **human**
roles across proving commands (`prove`, `autoprove`) and proof-editing agents.
It has two records — a **dispatch** record (parent → worker) and a **handoff**
record (worker → parent/human) — plus a **rerun guard** that stops a proving
mode from relaunching on the same blocker without new evidence.

This contract is **documentation, not runtime code**: it defines what the roles
exchange, not an enforcement engine. "Durable" here means each record is
**serializable and transferable** across a subagent, an inline pass, and a human
handoff — the *same* record shape regardless of who plays a role. **Filesystem
persistence is out of scope (Issue #82).**

The contract binds the **logical roles**, not processes: a host without
subagents plays parent and worker inline in the main thread and satisfies the
same records (see [No-subagent fallback](cycle-engine.md#run-contract-run-contractv1)).

It does not invent vocabulary — it names pieces the cycle engine already uses:
the [blocker signature](cycle-engine.md#stuck-definition), the
[pre-flight dispatch block](cycle-engine.md#pre-flight-context-for-subagent-dispatch),
the [`file-baseline/v1`](cycle-engine.md#file-baselines-and-drift-issue-102)
custody chain, the Blocked-Goal Triage classes from
[sorry-filling.md](sorry-filling.md), and the review stuck-mode `next_action`
enum.

---

## Dispatch record (parent → worker)

The concrete instantiation is the
[Pre-flight Context block](cycle-engine.md#pre-flight-context-for-subagent-dispatch);
this table is its canonical field contract. Every field is required unless a
nullability is given.

| Field | Type | Notes |
|-------|------|-------|
| `schema` | const `"run-contract/v1"` | record identity |
| `record` | const `"dispatch"` | |
| `target` | string | file, `file:line`, or fully-qualified declaration |
| `scope` | enum `sorry` \| `deps` \| `file` \| `changed` \| `project` | proving scope |
| `mode` | enum `prove` \| `autoprove` \| `golf` | dispatching mode |
| `capabilities` | array of string | tools available to the worker (e.g. `lean-lsp`, `search`); may be empty |
| `owned_files` | array of `file-baseline/v1` custody entries | the exclusive-ownership set, each carrying the baseline the parent recorded immediately before dispatch — **ownership**, not changes |
| `prior_blocker` | string \| null | the preceding handoff's `blocker_signature`; `null` on first dispatch |
| `budget` | object `{max_cycles, max_stuck_cycles, runtime}` | each subfield nullable (no explicit bound) |

**Ownership rule (unchanged):** never dispatch concurrent workers with
overlapping `owned_files`; serialize or keep one in-thread. `owned_files`
carries `file-baseline/v1` records so the worker can `check` before every
mutation and `advance` only what it changed
([custody chain](cycle-engine.md#file-baselines-and-drift-issue-102)).

---

## Handoff record (worker → parent/human)

Emitted at every **stop or stuck boundary** — compact enough for a human or
another agent to consume in one pass.

| Field | Type | Notes |
|-------|------|-------|
| `schema` | const `"run-contract/v1"` | |
| `record` | const `"handoff"` | |
| `status` | enum `solved` \| `stuck` \| `stopped` | |
| `blocker_class` | enum \| null | Blocked-Goal Triage class ([sorry-filling.md](sorry-filling.md)): `definitional-equality` \| `missing-intro-constructor-cases` \| `missing-rewrite` \| `arithmetic` \| `missing-library-lemma` \| `typeclass-coercion-elaboration` \| `needs-helper-lemma`. **`null` iff `status == solved`.** |
| `blocker_signature` | string \| null | the cycle engine's `(file, line, primary_error_code_or_text_hash)` signature ([Stuck Definition](cycle-engine.md#stuck-definition)). **`null` iff `status == solved`.** |
| `attempted_tools` | array of string | tools/queries tried |
| `best_candidates` | array | candidate lemmas/tactics tried and their outcomes |
| `failed_avenues` | array | approaches ruled out, so a rerun does not repeat them |
| `evidence` | object | the stuck-handoff evidence: LSP queries attempted, top candidate lemmas returned, `lean_multi_attempt` outcomes |
| `files_owned` | array of `file-baseline/v1` custody entries | the ownership set held — **distinct from** `files_changed` |
| `files_changed` | array of string | files the worker actually modified |
| `next_action` | enum `continue` \| `deep` \| `repair` \| `redraft` \| `golf` \| `stop` | the **shipped** review stuck-mode vocabulary |
| `new_evidence_required_for_rerun` | string \| null | what must change before a relaunch is justified. **`null` iff `status == solved`.** |

`files_owned` reports **custody** (what the worker was authorized to edit, with
baselines); `files_changed` reports **effect** (what it wrote). A worker may own
files it never changes; the parent advances baselines only for `files_changed`.

---

## Rerun guard

A relaunch of the same `(target, scope, mode)` is **forbidden** when the new
dispatch's blocker would match the prior handoff's `blocker_signature` **and**
there is no auditable **evidence delta**. A qualifying evidence delta is any one
of:

- a materially changed **goal or diagnostic**,
- an **advanced `file-baseline/v1`** baseline (accepted new content),
- a **newly verified candidate** lemma,
- **changed source**, or
- a **newly available capability/tool**.

If none holds, do not relaunch — route to `review --mode=stuck`, `formalize`, or
human handoff. This is the single definition of the rule; `prove.md`,
`autoprove.md`, and `SKILL.md` reference it rather than restating it.

---

## Human-in-the-loop

After a clear blocker in an interactive session, the parent presents options
(continue with new evidence / switch to `formalize` / `review --mode=stuck` /
stop and hand off) and **never assumes autonomous continuation**. The handoff
record is the artifact the human reads to choose — the same record a subagent or
inline worker would return.

## See Also

- [cycle-engine.md § Run Contract](cycle-engine.md#run-contract-run-contractv1) — roles, delegation expectations, no-subagent fallback
- [cycle-engine.md § Stuck Definition](cycle-engine.md#stuck-definition) — the `blocker_signature`
- [cycle-engine.md § File baselines and drift](cycle-engine.md#file-baselines-and-drift-issue-102) — `file-baseline/v1` custody
- [sorry-filling.md](sorry-filling.md) — Blocked-Goal Triage classes

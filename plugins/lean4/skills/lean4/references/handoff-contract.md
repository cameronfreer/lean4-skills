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
| `worker` | enum \| null | the dispatched agent: `sorry-filler-deep` \| `proof-repair` \| `proof-golfer` \| `axiom-eliminator`; `null` for an inline main-thread pass |
| `parameters` | object | worker-specific typed inputs (`{}` when none) — e.g. proof-golfer's search mode + candidate patterns, axiom-eliminator's axiom list, deep-mode safety budgets, proof-repair's structured error |
| `capabilities` | array of string | tools available to the worker (e.g. `lean-lsp`, `search`); may be empty |
| `owned_files` | array of string | the exclusive-ownership **paths** — ownership, not changes |
| `file_baseline` | `file-baseline/v1` | the **single** baseline record whose `files` array covers `owned_files`, computed by the parent immediately before dispatch (the primitive emits one object, not per-file entries) |
| `prior_blocker` | string \| null | the preceding handoff's `blocker_signature`; `null` on a first dispatch |
| `evidence_delta` | array of string | the auditable evidence justifying this (re)dispatch — **empty on a first dispatch**; each entry names what changed (see [Rerun guard](#rerun-guard)) |
| `budget` | object `{max_cycles: integer\|null, max_stuck_cycles: integer\|null, runtime: duration-string\|null}` | `null` subfield = no explicit bound; `runtime` is a duration string (e.g. `"120m"`) |
| `context` | object (below) | the pre-collected LSP starting state (MCP may be unavailable in a worker) |

`context` carries the pre-flight state — every member is **required**;
unavailable values use `null` or `[]` rather than being omitted:

| `context` member | Type | Notes |
|------------------|------|-------|
| `prior_failure` | string \| null | why the previous approach failed; `null` on a first dispatch |
| `goal_state` | string \| null | `lean_goal` at the target |
| `diagnostics` | array of string | `lean_diagnostic_messages`, summarized |
| `search_results` | array of `{tool: string, query: string, top: array of string}` | prior planning-phase searches |
| `candidates_tested` | array of `{snippet: string, result: string}` | `lean_multi_attempt` outcomes |
| `code_actions` | array of string | `lean_code_actions` for relevant lines |
| `scratch_location` | string | e.g. `/tmp` (never repo root) |

**Ownership rule:** never dispatch concurrent workers with overlapping
`owned_files`; serialize or keep one in-thread. The single `file_baseline`
covers the owned set so the worker can `check` before every mutation and
`advance` only what it changed
([custody chain](cycle-engine.md#file-baselines-and-drift-issue-102)).

---

## Handoff record (worker → parent/human)

Emitted at every **stop or stuck boundary** — compact enough for a human or
another agent to consume in one pass.

| Field | Type | Notes |
|-------|------|-------|
| `schema` | const `"run-contract/v1"` | |
| `record` | const `"handoff"` | |
| `target` | string | **echoes the dispatch `target`** — makes the handoff self-identifying (the rerun guard's `same_task` reads it) |
| `scope` | enum `sorry` \| `deps` \| `file` \| `changed` \| `project` | echoes the dispatch `scope` |
| `mode` | enum `prove` \| `autoprove` \| `golf` | echoes the dispatch `mode` |
| `status` | enum `solved` \| `stuck` \| `stopped` | |
| `stop_reason` | enum \| null | **non-null iff `status == stopped`**: `max-stuck` \| `max-cycles` \| `max-runtime` \| `user-stop` \| `queue-empty` \| `protocol-error` \| `operational-error`. `null` for `solved`/`stuck`. |
| `stop_detail` | string \| null | **non-null iff `stop_reason ∈ {protocol-error, operational-error}`** (e.g. file-baseline drift, malformed dispatch, unavailable checker); `null` otherwise |
| `blocker_kind` | enum \| null | why a blocker-driven stop happened: `proof` \| `false-statement` \| `safety-guard` \| `capability` \| `protocol` \| `operational`. **Non-null iff the stop was blocker-driven** — see Blocker fields below. |
| `blocker_class` | enum \| null | the proof-triage class, **non-null iff `blocker_kind == proof`** ([sorry-filling.md](sorry-filling.md)): `definitional-equality` \| `missing-intro-constructor-cases` \| `missing-rewrite` \| `arithmetic` \| `missing-library-lemma` \| `typeclass-coercion-elaboration` \| `needs-helper-lemma`. `null` for a `safety-guard`/`false-statement`/etc. blocker (e.g. deep regression, scope exceeded, header-fence, rollback failure). |
| `blocker_signature` | string \| null | the cycle engine's `(file, line, primary_error_code_or_text_hash)` signature ([Stuck Definition](cycle-engine.md#stuck-definition)). Same nullability as `blocker_kind`. |
| `attempted_tools` | array of string | tools/queries tried |
| `best_candidates` | array of `{candidate: string, outcome: string}` | lemmas/tactics tried and how each fared |
| `failed_avenues` | array of string | approaches ruled out, so a rerun does not repeat them |
| `evidence` | object `{queries: array of string, top_candidates: array of string, attempts: array of {snippet: string, result: string}, goal_delta: string\|null, diagnostic_delta: string\|null}` | the stuck-handoff evidence: LSP queries attempted, top candidate lemmas returned, `lean_multi_attempt` outcomes, and the goal / diagnostic change since dispatch (#73 requires reporting goal change; both are qualifying rerun-evidence classes) |
| `files_owned` | array of string | the ownership set held (echoes the dispatch's `owned_files`) — **distinct from** `files_changed` |
| `files_changed` | array of string | files the worker actually modified |
| `file_baseline` | `file-baseline/v1` | the **final current baseline** (adopt/patch rules below) |
| `artifacts` | array of `{kind: string, content: string}` | worker products the parent consumes — a **patch-only** worker returns `[{"kind": "unified-diff", "content": "..."}]` (with `files_changed: []`); `[]` when there is no product |
| `next_action` | enum `continue` \| `deep` \| `repair` \| `redraft` \| `golf` \| `stop` | the **shipped** review stuck-mode vocabulary |
| `new_evidence_required_for_rerun` | string \| null | what must change before a relaunch is justified. Same nullability as `blocker_kind`. |

**Blocker fields** (`blocker_kind`, `blocker_signature`,
`new_evidence_required_for_rerun`) are **non-null iff the stop was
blocker-driven** — `status == stuck`, or `status == stopped` with
`stop_reason == max-stuck`. `blocker_class` is non-null only when
`blocker_kind == proof` (the seven proof-triage classes); a **`safety-guard`**
stop (deep regression, deep scope exceeded, header-fence violation, rollback
failure) or a `false-statement`/`capability` blocker sets `blocker_kind`
accordingly and leaves `blocker_class` `null`. All blocker fields are **`null`**
for `status == solved` and for every non-blocker stop — budget/user/queue
(`max-cycles` / `max-runtime` / `user-stop` / `queue-empty`) **and** operational
aborts (`protocol-error` / `operational-error`), which carry their cause in
`stop_detail`. A `queue-empty` stop with claims remaining therefore reruns freely
— no `blocker_signature` for the guard to match.

**Custody vs effect.** `files_owned` reports custody (echoing the dispatch's
`owned_files`); `files_changed` reports effect (what the worker wrote). The
`file_baseline` is the single `file-baseline/v1` record for the owned set: a
direct-editing worker advances it after each mutation and returns the **final**
one, which the parent **adopts** as-is — re-advancing at handoff would bless
drift occurring after the worker's last `check`. A patch-only worker (e.g.
proof-repair) does not edit: it returns `files_changed: []`, the parent's own
`file_baseline` unchanged, and its diff in `artifacts` as
`{"kind": "unified-diff", "content": "..."}`; the **parent** then checks,
applies, and advances the patch itself.

---

## Rerun guard

The predicate is evaluated **from the two records** — no future blocker is
guessed. The handoff echoes `target`/`scope`/`mode`, so the task triple is
self-identifying:

```text
same_task =
     new_dispatch.target == prior_handoff.target
  && new_dispatch.scope  == prior_handoff.scope
  && new_dispatch.mode   == prior_handoff.mode
```

A relaunch is **forbidden** when all four hold:

- `same_task`, **and**
- `prior_handoff.blocker_signature` is **non-null** (the prior stop was blocker-driven), **and**
- `new_dispatch.prior_blocker == prior_handoff.blocker_signature` (the same blocker), **and**
- `new_dispatch.evidence_delta` is empty (nothing new to try).

The non-null condition is load-bearing: a non-blocker stop
(`queue-empty`/`max-cycles`/`max-runtime`/`user-stop`) has a `null` signature,
and a `null == null` match must **not** forbid the rerun — those reruns are
always allowed. A first dispatch carries `prior_blocker: null` and an empty `evidence_delta`, so
it is never forbidden. A qualifying `evidence_delta` entry is any of:

- a materially changed **goal or diagnostic**,
- an **advanced `file-baseline/v1`** baseline (accepted new content),
- a **newly verified candidate** lemma,
- **changed source**, or
- a **newly available capability/tool**.

When the predicate forbids a relaunch, route to `review --mode=stuck`,
`formalize`, or human handoff instead.

**Operational and protocol stops.** A `protocol-error` or `operational-error`
handoff has **null** blocker fields, so the signature predicate above never
applies — but it must not be relaunched blindly either (the same malformed
dispatch, unavailable checker, or unreconciled drift would just repeat). Such a
stop may be relaunched **only** when the new dispatch's `evidence_delta` is
nonempty and describes how the prior `stop_detail` was resolved (e.g.
baseline reconciled, checker restored, dispatch corrected). Normal
queue/budget/user stops remain freely rerunnable.

This is the single definition of the rule; `prove.md`, `autoprove.md`, and
`SKILL.md` **reference** it rather than restating the predicate.

---

## Human-in-the-loop

After a clear blocker in an interactive session, the parent presents options
(continue with new evidence / switch to `formalize` / `review --mode=stuck` /
stop and hand off) and **never assumes autonomous continuation**. The handoff
record is the artifact the human reads to choose — the same record a subagent or
inline worker would return.

## Blocker-class vocabulary and the stuck review

`/lean4:review --mode=stuck` reports a **Primary blocker class** as human
phrases; the handoff record's `blocker_class` is their kebab-case enum:

| review phrase | `blocker_class` |
|---------------|-----------------|
| definitional equality | `definitional-equality` |
| missing intro-constructor-cases | `missing-intro-constructor-cases` |
| missing rewrite | `missing-rewrite` |
| arithmetic | `arithmetic` |
| missing library lemma | `missing-library-lemma` |
| typeclass-coercion-elaboration | `typeclass-coercion-elaboration` |
| needs helper lemma | `needs-helper-lemma` |

The stuck review block is **not itself a complete handoff record** — it carries
no `schema`/`record`/`status`, no `blocker_signature`, and no custody fields. It
**supplies** the evidence and the blocker vocabulary; the **parent** wraps that
into a `run-contract/v1` handoff record (mapping the phrase to the enum above).

## See Also

- [cycle-engine.md § Run Contract](cycle-engine.md#run-contract-run-contractv1) — roles, delegation expectations, no-subagent fallback
- [cycle-engine.md § Stuck Definition](cycle-engine.md#stuck-definition) — the `blocker_signature`
- [cycle-engine.md § File baselines and drift](cycle-engine.md#file-baselines-and-drift-issue-102) — `file-baseline/v1` custody
- [sorry-filling.md](sorry-filling.md) — Blocked-Goal Triage classes

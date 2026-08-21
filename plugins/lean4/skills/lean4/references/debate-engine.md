# Debate Engine Reference

> One parametrized multi-perspective deliberation procedure, shared by every workflow that
> needs to weigh genuinely competing options. Each workflow instantiates it with its own
> panel, triggers, and gate — it never runs unless the instance's trigger fires **and** the
> user has opted in.

## Overview

Several workflows hit the same structural problem: a decision point with two or more
defensible answers where committing to the first plausible one is the failure mode — which
formalization of an informal claim, whether a review finding is real, how to respond to a
struggling learner. The debate engine is the shared procedure for those points. A small
panel of named perspectives each answers one question with a committed position, an
adjudication rule turns the positions into one outcome, and the workflow consumes the
outcome and tells the user what happened in one line.

Design rules, in priority order:

1. **Opt-in.** A debate under the default gate never runs without the user approving it —
   the workflow proposes, the user decides. Trigger detection itself must be free.
2. **Bounded.** Every instance fixes a round count and an evidence budget up front. A
   debate that cannot resolve within budget falls back to the workflow's default path and
   says so.
3. **Advisory.** The outcome feeds the workflow's existing decision point. It never adds
   new side effects: a debate in a read-only workflow stays read-only, and a debate never
   commits, writes, or edits anything itself.
4. **Host-agnostic.** The default substrate is inline reasoning by the session agent, which
   works on every host. Subagent panels are a reserved substrate for future instances and
   degrade to inline when dispatch is unavailable.

## Parameters

An instance of the debate engine is a choice of values for these eight parameters. The
implemented instances below are exactly such parameter choices — there is no other
debate machinery.

| Parameter | What it fixes |
|-----------|---------------|
| `panel` | 2–4 named perspectives. Each is defined by the single question it must answer, and each must commit to a position — hedging is not a position. |
| `substrate` | `inline` (default): the session agent reasons through each perspective in turn, independently, before comparing them. `subagent` (reserved): each perspective runs as an independent agent per [subagent-workflows.md](subagent-workflows.md), with pre-collected context per [cycle-engine.md](cycle-engine.md#pre-flight-context-for-subagent-dispatch). No current instance uses `subagent`. |
| `rounds` | Maximum deliberation rounds. Inline instances use 1. |
| `evidence` | What the panel reasons over, plus the budget for *new* tool calls (default 0 — reason over already-collected context only). Thin evidence is reported in the outcome, not papered over. |
| `trigger` | The automatically detected circumstances under which the workflow proposes a debate. Detection must use information the workflow already has. |
| `gate` | How the user opts in: `proposal` (a `--debate=ask\|auto\|off` flag; see the protocol below) or `always-inline` (permitted only for zero-tool-call instances whose sole user-visible effect is a one-line note; effect scope is then gated by instance-specific flags). |
| `adjudication` | The decision rule that turns the panel's positions into one outcome, including its tiebreak order. |
| `outcome` | The structured result the workflow consumes at its existing decision point, plus the one-line user-visible note. |

## Gate and Opt-In Protocol

Instances with the `proposal` gate expose a `--debate` flag on their command:

| Value | Behavior |
|-------|----------|
| `ask` (default) | On trigger, show a one-line proposal and wait. Never auto-run. |
| `auto` | On trigger, run without prompting. Always emit the outcome note. |
| `off` | No debates and no proposals. Trigger detection is not announced. |

The proposal is one line — the trigger's concrete reason, then the choice:

```
Debate available (draft): two materially different formalizations survive —
Finset.range sum vs Fin n sum. Run a 1-round formalization debate? [yes / no / always / never]
```

- `yes` / `no` decide this occurrence only.
- `always` / `never` persist for the session: `always` behaves as `--debate=auto` for the
  rest of the session, `never` as `--debate=off`. Both are announced when applied and are
  overridden by an explicit `--debate` flag on a later invocation.
- At most one proposal per decision point. Declining is remembered — do not re-propose the
  same debate for the same target.
- If the proposal cannot be shown (non-interactive context), treat the answer as `no`.
  Opt-in is never assumed and never silently coerced to `auto`.

The `always-inline` gate has no flag and no proposal: the instance runs as part of its host
step. It is permitted only when the debate spends no new tool calls and its only direct
user-visible effect is a one-line note, so there is no cost or side effect to opt into. Any
further effects (for example profile changes in learn) must be gated by the instance's own
flags.

## Deliberation Procedure

The inline substrate, per round:

1. **State positions independently.** For each panel perspective in order, answer its
   defining question in 1–3 sentences, committed and specific, before comparing it with any
   other perspective's answer. Cite evidence from the instance's evidence set — a position
   that cites nothing is thin, and says so.
2. **Adjudicate.** Apply the instance's adjudication rule to the stated positions. Genuine
   disagreement is signal: record what the losing positions claimed, do not paper over it.
3. **Emit the outcome.** Hand the structured result to the workflow's decision point and
   show the one-line note:

   ```
   *Debate (draft, 1 round): chose the Finset.range encoding — Fidelity and Idiom agreed;
   Provability's Fin n alternative kept in the depth-check menu.*
   ```

If the rule cannot produce a decision within `rounds`, fall back to the workflow's default
path and say so in the note. A debate never loops beyond its round budget.

The `subagent` substrate follows the same shape with perspectives as independent agents; it
additionally requires the dispatch preconditions in
[subagent-workflows.md](subagent-workflows.md) and degrades to inline when they are not
met. It is reserved for future instances (see the matrix) and intentionally unspecified
beyond this until the first such instance ships.

## Instance Matrix

Planned coverage of the workflow family. "Implemented" means wired into the command doc
with a contract test; "planned" rows are design intent only and bind nothing.

| Workflow | Decision point | Panel sketch | Substrate | Status |
|----------|----------------|--------------|-----------|--------|
| draft | which formalization of the informal claim | Fidelity / Idiom / Provability | inline | **implemented** — [below](#draft-formalization-debate) |
| review | is this finding real, and at what severity | Advocate / Skeptic / Maintainer | inline | **implemented** — [below](#review-finding-adjudication) |
| learn | how to respond to the learner's last message | Pace / Method / Depth | inline | **implemented** — [below](#learn-pedagogical-self-debate) |
| prove | proof strategy for a high-difficulty sorry | mathematical structure / tactic mechanics / failure modes | subagent candidate | planned |
| refactor | which simplification strategy to apply | mathlib leverage / helper extraction / restructuring cost | inline | planned |
| golf | how far to compress a proof | brevity / readability / robustness | inline | planned |
| formalize | composes the draft instance (statement phase) and the prove instance (proving phase) | — | per phase | planned |

`autoprove` and `autoformalize` are deliberately absent — see
[Deferred: Autonomous Commands](#deferred-autonomous-commands).

## Implemented Instances

### Draft: Formalization Debate

Wired into `/lean4:draft` — see [draft.md](../../../commands/draft.md).

| Parameter | Value |
|-----------|-------|
| `panel` | **Fidelity**: "Does this statement assert exactly the informal claim — no vacuity, no accidental strengthening or weakening?" **Idiom**: "Is this the mathlib-idiomatic encoding and level of generality — canonical types, existing predicates, right typeclass assumptions?" **Provability**: "Which candidate can actually be proven with reasonable effort, given the search results?" |
| `substrate` / `rounds` | inline / 1 |
| `evidence` | The claim text, the candidate statements, search results and diagnostics already collected by the drafting steps. Budget: at most 2 new LSP search calls across the whole panel (Provability typically spends them). |
| `trigger` | Any of: (1) two or more materially different candidate statements survive drafting — different encoding, quantifier structure, or typeclass generality, not cosmetic variants; (2) faithfulness risk — the leading candidate may be vacuous, trivially true, or weaker/stronger than the informal claim; (3) repeated strict elaboration failures that implicate the statement shape rather than the proof. |
| `gate` | `proposal` via draft's `--debate` flag (default `ask`). |
| `adjudication` | Fidelity outranks Idiom outranks Provability. A candidate that fails Fidelity is eliminated regardless of other merits. A tie after ranking presents both candidates instead of picking one. |
| `outcome` | The chosen candidate becomes the drafted statement. Rejected-but-viable candidates are kept as depth-check "alternative formalization" entries, never silently dropped. One-line note as in the procedure above. |

### Review: Finding Adjudication

Wired into `/lean4:review` — see [review.md](../../../commands/review.md). Batch mode
only: stuck-mode reviews are a fast triage path owned by the proving commands and never
run debates or proposals.

| Parameter | Value |
|-----------|-------|
| `panel` | **Advocate**: "What is the strongest concrete case that this finding is real and worth the reader's time?" **Skeptic**: "What is the strongest case that this is a false positive or noise — cite the specific rule, context, or counter-reading?" **Maintainer**: "Would a mathlib reviewer ask for this change, and does the proposed remedy cost more than it fixes?" (Background vocabulary: [mathlib-review-taxonomy.md](mathlib-review-taxonomy.md).) |
| `substrate` / `rounds` | inline / 1 |
| `evidence` | The analysis outputs review already produced (build status, sorry audit, axiom check, style pass, golf scan). Budget: 0 new tool calls — adjudication reasons over collected output only. |
| `trigger` | A candidate finding from review's existing analyses where any of: (1) the evidence is uncertain — no specific rule, lemma, or diagnostic backs it; (2) the severity or category boundary is contested; (3) the proposed remedy is destructive enough that a false positive would be costly (delete-or-replace class suggestions). |
| `gate` | `proposal` via review's `--debate` flag (default `ask`). One proposal covers all triggered findings in the report, not one per finding. |
| `adjudication` | A finding is reported only if the Advocate's case survives the Skeptic's strongest objection; the Maintainer's answer sets severity and placement. Unresolved findings are not reported as recommendations. |
| `outcome` | Findings that fail adjudication move from Recommendations to a short "Set aside by adjudication" list with one-line reasons — visible, but out of the action path. Human-readable report only: the `--json` schema is unchanged (machine-readable adjudication markers are deferred to the #115 schema work). Review stays read-only; the debate adjudicates findings that review's existing analyses already produced — it filters and labels, it does not create new finding sources (broadening what review emits remains #110). |

### Learn: Pedagogical Self-Debate

The pre-existing step 5 of `/lean4:learn`, unchanged in behavior — this section only names
its parameters as a debate-engine instance. Behavior is normative in
[learn.md](../../../commands/learn.md) and
[learn-pathways.md](learn-pathways.md#pedagogical-self-debate).

| Parameter | Value |
|-----------|-------|
| `panel` | Pace / Method / Depth advisors, as defined in learn-pathways.md. |
| `substrate` / `rounds` | inline / 1 |
| `evidence` | Already-discovered session information only — the No Lean Verification rule. Budget: 0 new tool calls. |
| `trigger` | The per-style When to Run table (mandatory in `game` and `socratic`; skipped for trivial navigation in `tour` and `exercise`). |
| `gate` | `always-inline` — no `--debate` flag, because the instance spends no tool calls and its only direct output is the `*Pedagogy: ...*` note. Its further effects (Learning Profile writes) are gated by `--adaptive` and the explicit-flag precedence rules, which is exactly the effect-scope gating the `always-inline` gate requires. |
| `adjudication` | Momentum tiebreak (keep the learner engaged over completeness), then time-sensitivity. |
| `outcome` | A named strategy from the fixed strategy set, plus the `*Pedagogy: ...*` note with presentation-dependent visibility. |

## Failure Handling

| Failure | Response |
|---------|----------|
| No decision within `rounds` | Fall back to the workflow's default path; say so in the note. |
| Evidence budget exhausted mid-debate | Adjudicate on what was gathered; mark the outcome as thin-evidence. |
| Proposal cannot be shown (non-interactive) | Treat as `no`. Never coerce to `auto`. |
| `subagent` substrate unavailable (future instances) | Degrade to inline with the same panel and note the degradation. |
| Trigger fires repeatedly on the same target | Propose once; a declined proposal is not repeated for that target. |

## Deferred: Autonomous Commands

`autoprove` and `autoformalize` cannot prompt mid-run, so the `proposal` gate as specified
cannot apply to them. Their precedent for `ask`-shaped flags is startup coercion with a
warning (for example `--commit=ask` → `auto`), but debate opt-in is deliberately **not**
given that treatment: silently coercing a consent gate to `auto` would spend debate budget
the user never approved. Wiring the autonomous commands requires a startup-time opt-in
design (approve classes of debates before the run begins, with per-run budgets), which is
out of scope here and tracked as follow-on work to this module.

## See Also

- [draft.md](../../../commands/draft.md) — draft instance wiring and flag
- [review.md](../../../commands/review.md) — review instance wiring and flag
- [learn.md](../../../commands/learn.md) — learn instance host step
- [learn-pathways.md](learn-pathways.md#pedagogical-self-debate) — learn instance behavior (normative)
- [subagent-workflows.md](subagent-workflows.md) — dispatch preconditions for the reserved `subagent` substrate
- [cycle-engine.md](cycle-engine.md) — shared prove/autoprove mechanics the planned prove instance would integrate with
- [mathlib-review-taxonomy.md](mathlib-review-taxonomy.md) — background vocabulary for the review instance's Maintainer perspective

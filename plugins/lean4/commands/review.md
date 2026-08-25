---
name: review
description: Read-only code review of Lean proofs
user_invocable: true
---

# Lean4 Review

Read-only review of Lean proofs for quality, style, and optimization opportunities.

**Non-destructive:** Files are restored after analysis.

## Usage

```
/lean4:review                              # Review changed files (default)
/lean4:review File.lean                    # Review specific file
/lean4:review File.lean --line=89          # Review single sorry
/lean4:review File.lean --line=89 --scope=deps  # Review sorry + its dependencies
/lean4:review --scope=project              # Review entire project (prompts)
/lean4:review --mathlib-review             # Force the mathlib-review bar (Layer 2)
```

## Invocation Contract

Interpret this command's inputs per the
[Command Invocation Contract](../skills/lean4/references/command-invocation.md).

**Primary path (hook-validated):** If a `validated-invocation` block for this
command appears in context, treat it as the authoritative interpretation of
parser-decidable inputs and do **not** re-parse the raw invocation text for
those inputs. Start by reading all parser-decided fields from the block. Emit
the final **Resolved Inputs** summary from the block values.
See [Validated Invocation Block](../skills/lean4/references/command-invocation.md#validated-invocation-block-host-provided).

**Fallback path (other hosts):** If no `validated-invocation` block is present,
parse the raw invocation text against this command's input table before acting.

Startup requirements:

1. Emit a **Resolved Inputs** block with explicit values, defaults, and any
   ignored flags — including the effective **Layer-2 activation** decision and
   its source (`flag`, `repository_kind`, `contributing_upstream`, the helper's
   validated `intent.source`, or `helper-failure`; see
   [Mathlib Review Layer](#mathlib-review-layer-layer-2)).
2. Refuse to start on startup validation errors — including passing both
   `--mathlib-review` and `--no-mathlib-review` (`--mathlib-review` with
   `--no-mathlib-review` → startup validation error).

## Inputs

| Arg | Required | Description |
|-----|----------|-------------|
| target | No | File or directory to review |
| --scope | No | `sorry`, `deps`, `file`, `changed`, or `project` |
| --line | No | Line number for single-sorry scope |
| --codex | No | External review via Codex (interactive handoff) |
| --llm | No | Use llm CLI with model |
| --hook | No | Run custom analysis script |
| --json | No | Output structured JSON for external tools |
| --mode | No | `batch` (default) or `stuck` (triage) |
| --mathlib-review | No | Force the Layer-2 mathlib-review bar at full strictness, overriding project-context detection. Mutually exclusive with `--no-mathlib-review`. |
| --no-mathlib-review | No | Force Layer-2 findings to advisory, overriding project-context detection. Mutually exclusive with `--mathlib-review`. |

## Scope Behavior

**Scope levels:**
| Scope | Description |
|-------|-------------|
| `sorry` | Single sorry at --line (requires target file + --line) |
| `deps` | Sorry + same-file helpers and directly referenced lemmas (requires target file + --line) |
| `file` | All sorries in target file |
| `changed` | Files modified since last commit (git diff) |
| `project` | Entire project (requires confirmation) |

**Defaults:**
- No args → `--scope=changed`
- Target file provided → `--scope=file`
- Target + `--line` → `--scope=sorry`
- Triggered by prove/autoprove → matches current focus (`sorry` or `file`)

**Note:** Scope filtering is implemented by the reviewing agent, not the underlying scripts. The agent reads script output and filters results to match the requested scope.

**Project-wide confirmation:**
```
⚠️  This will review the entire project.
Proceed? (yes / no)
```

**Output header always shows scope:**
```markdown
## Lean4 Review Report
**Scope:** Core.lean:89 (single sorry)
```

## Review Modes

**Batch mode (default):**
- Purpose: "What changed in this batch" + basic hygiene — full review report with all sections
- Use: Regular cadence reviews, manual quality checks

**Stuck mode:**
- Trigger: prove/autoprove invokes stuck mode per its detection triggers when no progress is detected. Can also be invoked manually.
- Purpose: "What's blocking progress on current focus" — top 3 blockers with actionable next steps
- Lightweight: Skips full golf analysis and complexity metrics; focuses on blockers only

**Stuck mode output format:**
```markdown
## Stuck Review — Core.lean:89

**Primary blocker class:** missing library lemma

**Top 3 blockers:**
1. Missing lemma about tendsto_atTop → search Mathlib.Topology.Order
2. Typeclass instance missing for MeasurableSpace β → add `haveI`
3. Proof too long (38 lines) → extract helper lemma first

**Evidence:**
- searches — `lean_leansearch "tendsto atTop of monotone"`, `lean_loogle "Tendsto _ atTop"`
- returned lemmas — `tendsto_atTop_mono`, `Tendsto.comp`
- attempts — `exact tendsto_atTop_mono h` (type mismatch), `apply Tendsto.comp` (unification goal)

**Flag:** Statement may be false (optional — see below)

**Recommended next action:** Search for tendsto variants in Topology/Order
**Why first:** the top blocker is a missing lemma, so search dominates more tactic attempts
**next_action:** continue
```

The **Primary blocker class** value uses the Blocked-Goal Triage vocabulary from [sorry-filling.md](../skills/lean4/references/sorry-filling.md) (definitional equality / missing intro-constructor-cases / missing rewrite / arithmetic / missing library lemma / typeclass-coercion-elaboration / needs helper lemma) and classifies the top blocker — the listed blockers may span classes. The **Evidence** block records the searches attempted, top candidate lemmas returned, and `lean_multi_attempt` outcomes required by the cycle-engine stuck-handoff contract. This block **supplies the evidence and blocker vocabulary** that the parent wraps into a `run-contract/v1` [handoff record](../skills/lean4/references/handoff-contract.md#blocker-class-vocabulary-and-the-stuck-review) — it is not itself a complete record (it carries no `schema`/`record`/`status`/`blocker_signature`/custody fields), and its human blocker phrases map to the record's kebab-case `blocker_class` enum. These fields are part of the human-readable stuck report only — they are **not** represented in the `lean4-review-output/v2` interchange contract, which carries per-finding suggestions, not stuck-triage narrative.

**next_action classification (stuck mode):** `continue` (retryable), `deep` (needs escalation), `repair` (compiler blocker), `redraft` (statement-shape blocker), `golf` (sorry-free), `stop` (no path). Informational unless autoprove outer loop is active.

**Falsification flag:** Include when analysis suggests statement may be false:
- Decidable goal that failed `decide` or `native_decide`
- Repeated proof failures with no viable approach
- prove/autoprove passed falsification signal from earlier preflight

Example: `**Flag:** Statement may be false (decidable goal failed decide)`

**Blocker priority (stuck mode):**
1. Build errors/diagnostics in focus
2. Sorries on critical path (target line or its dependencies)
3. Custom axioms introduced in focus
4. Long/fragile proofs (performance risk)
5. Falsification signals (decidable goal that failed `decide`, repeated proof failures)

For strategy-level proof simplification (mathlib leverage, helper extraction, congr-lemma patterns), run `/lean4:refactor` or `/lean4:refactor --dry-run`.

## Actions — Layer 1: core proof hygiene (always-on)

The agent selects files based on scope, then runs these analyses (per file or directory):

1. **Build Status** - `lake build` (project-wide); for scoped review (`--scope=file`), use `lean_diagnostic_messages(file)` + `lake env lean <path/to/File.lean>` (run from project root) first
2. **Sorry Audit** - `lean4-skills-sorry-analyzer <target> --format=json --report-only`
3. **Axiom Check** - `lean4-skills-check-axioms-inline <target> --report-only`
4. **Style Review** - Check mathlib conventions (naming, structure, tactics, 100-char line width). Flag lines wrapped under 100 chars that fit on one line (common: `mkAppM` calls, short struct literals, single-expression tactic lines).
5. **Golfing Opportunities** - `lean4-skills-find-golfable <target> --filter-false-positives`
6. **Complexity Metrics** - Proof sizes, longest proofs, tactic patterns

**Stuck mode:** Steps 5–6 are skipped; focus is on blockers (steps 1–4) for quick triage.

Layer 1 findings are always blockers-or-hygiene for the current project. The
second-pass **mathlib-review layer** below runs on top of them.

## Mathlib Review Layer (Layer 2)

A second pass surfaces what mathlib's own PR-review guide asks for, in four
first-class sections mapped onto the shipped
[mathlib-review taxonomy](../skills/lean4/references/mathlib-review-taxonomy.md)
(#114) and the `category` values in
[`lean4-review-schema.json`](../skills/lean4/references/lean4-review-schema.json)
(#115). This layer **consumes** those references; it does not restate their
vocabulary.

1. **Documentation Review** — module + declaration docstrings on public API, proof sketches on intricate arguments, cross-references. *Categories:* `docstring`, `module-doc`.
2. **Library Integration Review** — duplicate/more-general existing results, file placement, heavier-than-needed imports, lowest sensible module. *Categories:* `file-placement`, `import-hygiene`.
3. **API / Generalization Review** — weakest reasonable assumptions, structure-vs-conjunction, blocked generalizations. *Categories:* `api`, `generalization` (settled rule `rule_id: vacuous-api`, `severity: advisory`).
4. **Attributes & Instances Review** — `@[simp]` justification, new-instance diamond risk, `@[ext]`, `@[reducible]`. *Categories:* `attribute`, `simp`, `instance`.

### Layer-2 activation

Layer 2 runs at **full strictness** (findings alongside Layer-1) only when the
work is plausibly aimed at upstream mathlib; otherwise its findings are
**advisory**. Resolve the mode in this order — **conflict validation precedes
precedence**:

1. **Conflict first.** Only flags resolving to `true` participate; an explicit
   `--mathlib-review=false` (or `--no-mathlib-review=false`) equals omission. If
   **both** `--mathlib-review` and `--no-mathlib-review` resolve to `true`,
   refuse to start (one startup validation error) — do not silently pick one.
2. **Explicit `true` flag wins — skip the helper.** If `--mathlib-review`
   resolves to `true`, use full strictness; if `--no-mathlib-review` resolves to
   `true`, use advisory. Do **not** consult project-context in either case.
3. **Otherwise acquire project context.** Run
   `lean4-skills-project-context --from "<target>"` (the target file/dir if one
   was given, else `$PWD`) and validate the record exactly as `/lean4:checkpoint`
   does: `schema` = `project-context/v1`; `facts.repository_kind` a string in
   `mathlib | other-lean | not-lean | unknown`; `intent.contributing_upstream` a
   string in `yes | no | unknown`; `intent.source` a string in
   `env-override | invalid-env-override | remote-heuristic | default`. A nonzero
   exit, unparseable output, or any missing / non-string / out-of-domain field is
   **malformed helper output**.
4. **Then precedence** on the validated record:

| Condition (in order) | Layer-2 behavior | Source |
|----------------------|------------------|--------|
| `--no-mathlib-review` true | advisory | `flag` |
| `--mathlib-review` true | full strictness | `flag` |
| `facts.repository_kind == mathlib` | full strictness | `repository_kind` |
| `intent.contributing_upstream == yes` | full strictness | `contributing_upstream` |
| any other resolved context (`other-lean`/`not-lean`/`unknown`, `no`/`unknown` intent) | advisory | `intent.source` |
| helper nonzero / unparseable / malformed record | advisory | `helper-failure` |

`facts.repository_kind` (what the repo *is*) and `intent.contributing_upstream`
(intent) are distinct signals; either independently activates full strictness,
and an explicit flag overrides both. The fail direction is toward **advisory** —
the opposite of the checkpoint gate's fail-closed — because a review consumer
must never impose mathlib blockers when the context is uncertain. Report the
resolved mode **and its source** in the **Resolved Inputs** block.

### Output labeling (normative)

Advisory Layer-2 findings must be **structurally separable** from Layer-1
blockers. In human-readable output, render them under a distinct heading
(e.g. `### Advisory (mathlib-style)`) or label them explicitly as advisory. In
`lean4-review-output/v2`, encode them with `severity: advisory` (the schema
carries severity, not a section heading). Intermixing advisory and blocking
findings in one undifferentiated list is insufficient.

**Mode × layer:**

- `batch` × mathlib-targeted: all four Layer-2 sections emit as first-class findings alongside Layer-1.
- `batch` × non-mathlib: Layer-2 emits under a separate "Advisory (mathlib-style)" section.
- `stuck` × mathlib-targeted: bias toward blockers; allow one Layer-2 blocker when it is the main reason the patch won't survive mathlib review.
- `stuck` × non-mathlib: Layer-1 blockers only; Layer-2 stays advisory and may be omitted.

## Output

```markdown
## Lean4 Review Report
**Scope:** Core.lean:89 (single sorry)

### Build Status
✓ Project compiles

### Sorry Audit (N remaining)
| File | Line | Theorem | Suggestion |
|------|------|---------|------------|
| ... | ... | ... | ... |

### Axiom Status
✓ Standard axioms only

### Style Notes
- [file:line] - [suggestion]

### Golfing Opportunities
- [pattern] → [optimization]

### Recommendations
1. [action item]
```

## External Hooks

Custom hooks receive structured JSON on stdin with file information, sorries, axioms, and build status. They return a complete `lean4-review-output/v2` object containing a `suggestions` array.

**Validate before merging.** Every hook or Codex `output/v2` object is validated
before its findings are incorporated — pipe it through
`lean4-skills-validate-review-output` (reads the object on stdin):

- exit `0` — valid; merge the findings.
- exit `3` — validation failure (`error_code` `schema-invalid` or
  `semantic-invalid` on stdout). **Exclude** these findings and report the
  failure; never normalize or repair the output.
- exit `2` — empty input or malformed JSON (treat as a hook that produced no
  usable result); exit `4` — the shipped schema is unreadable (operational).

The validator enforces the shipped schema plus the cross-field invariants JSON
Schema cannot express: `total_suggestions == len(suggestions)`, the
`by_severity` histogram agrees with the suggestions, and a non-null `error`
implies empty `suggestions`.

See [review-hook-schema.md](../skills/lean4/references/review-hook-schema.md) for full input/output schemas, examples, and performance tips for rate-limited APIs.

## External Review Handoff

When `--codex` is specified, display context for external review:

```
─────────────────────────────────────────────────────────
CODEX REVIEW — {scope description}
─────────────────────────────────────────────────────────

[Context based on scope:]
- sorry: ±50 lines around the target sorry
- deps: Target sorry + referenced helpers/lemmas
- file: Full file content
- changed: All modified files (git diff)
- project: Full project (requires confirmation)

If no sorries in scope:
- file: Include top-level definitions + relevant sections
- changed: Include diff + changed file list

To review in Codex CLI:
1. Run `codex` in project directory
2. Type `/review` → select "Review uncommitted changes"
3. Or paste the above context and ask for review

Return one complete `lean4-review-output/v2` object conforming to the shipped
[`lean4-review-schema.json`](../skills/lean4/references/lean4-review-schema.json):
every suggestion carries all eight fields (using `null` where unavailable), and
the root also includes `version`, `summary`, and `error`. See
[review-hook-schema.md](../skills/lean4/references/review-hook-schema.md) for a
worked example.
─────────────────────────────────────────────────────────
```

## Post-Review Actions

After review completes (internal or external), prompt:

```
## Review Complete

Would you like me to create an action plan from the review findings?
- [yes] — Enter plan mode with 3-6 step implementation plan
- [no] — End review, return to conversation
```

If "yes":
1. Enter plan mode
2. Create plan with one task per high-priority suggestion
3. Get user approval before execution
4. Route to the appropriate command (review itself remains read-only):
   - Missing proofs / build blockers → `/lean4:prove`
   - Strategy simplification opportunities → `/lean4:refactor`
   - Tactic-level brevity cleanup → `/lean4:golf`

**Note:** When `--mode=stuck` is triggered by prove/autoprove, skip this prompt—the proving command handles the follow-up with its own "Apply this plan? [yes/no]" prompt.

## Built-in `--json` report schema (`lean4-review-report/v1`)

This legacy report format is **distinct** from the hook/Codex
`lean4-review-output/v2` interchange contract above ([`lean4-review-schema.json`](../skills/lean4/references/lean4-review-schema.json)):
it is the built-in command's own human-oriented `--json` dump, unchanged by
#115. When using `--json`, output follows this structure:

```json
{
  "version": "1.0",
  "build_status": "passing" | "failing",
  "sorries": [
    {"file": "Core.lean", "line": 89, "theorem": "convergence_main", "goal": "..."}
  ],
  "axioms": {
    "standard": ["propext", "Classical.choice", "Quot.sound"],
    "custom": []
  },
  "style_notes": [
    {"file": "Core.lean", "line": 42, "message": "Consider using field syntax"}
  ],
  "golfing_opportunities": [
    {"file": "Core.lean", "line": 78, "pattern": "have chain", "suggestion": "Inline or extract"}
  ],
  "summary": {
    "total_sorries": 3,
    "total_custom_axioms": 0,
    "style_issues": 2,
    "golf_opportunities": 5
  }
}
```

**Stuck mode only:** The `summary` object includes `"next_action": "continue"` (or other value) when `--mode=stuck`. Absent in batch mode.

## Codex Integration

**Note:** Codex CLI's `/review` command is interactive-only. There's no `codex review <sha>` CLI command for automation. Two approaches are available:

### Option A: Interactive Handoff (Recommended)

1. Run `codex` in the project directory
2. Type `/review` and select:
   - "Review uncommitted changes" — for working tree
   - "Review a commit" — select SHA from list
   - "Review against a base branch" — for PR-style diff
3. Copy suggestions back to this session

**Tip:** Use `/diff` after `/review` to see exact file changes.

### Option B: Non-interactive CLI automation (`codex exec`)

For CI or scripted reviews, use `codex exec` with a review prompt:

```bash
codex exec "Review this Lean 4 proof for correctness, focusing on:
1. Incomplete sorries and proof gaps
2. Type mismatches or missing instances
3. Non-standard axiom usage

$(cat Core.lean)
" --output-schema "$LEAN4_REFS/lean4-review-schema.json" -o review-output.json
```

The `--output-schema` argument points at the **shipped, normative** contract
[`lean4-review-schema.json`](../skills/lean4/references/lean4-review-schema.json)
(`$LEAN4_REFS` is the installed references directory). It is the single source
of truth for the category/severity enums — this command does not restate the
full schema. External Codex reviews emit `fix: null` and set `rule_id` only
for a specific rule (e.g. `vacuous-api` under `api`). A minimal conforming
suggestion:

```json
{
  "file": "Core.lean", "line": 89, "column": null,
  "severity": "advisory", "category": "api", "rule_id": "vacuous-api",
  "message": "Public API collapses to True; delete or replace.", "fix": null
}
```

See [review-hook-schema.md](../skills/lean4/references/review-hook-schema.md)
for the field tables and the [Codex SDK Cookbook](https://cookbook.openai.com/examples/codex/build_code_review_with_codex_sdk)
for CI integration patterns.

> **Future autonomous external review:** External review is currently manual-handoff only. Future versions may support autonomous external review via non-interactive CLI execution (e.g., `codex exec`) behind an explicit opt-in flag (`--external-autonomous`). Until then, unattended autoprove runs default to internal review.
>
> Requirements for autonomous external review:
> 1. Stable JSON input/output contract
> 2. Timeout + retry + cost budgets
> 3. Safe fallback to internal review on external failure
> 4. Explicit opt-in flag, not default behavior

## Safety

- Read-only (does not modify files permanently)
- Axiom check temporarily appends `#print axioms`, then restores
- Does not create commits
- Does not apply fixes
- **Docstring policy — Rule B (review).** Review may flag weak or missing docstrings, development-history language (e.g. "sorry-free", "earlier drafts"), and scaffolding comments (`TODO`/`HACK`/`FIXME`), and may **propose replacement wording** in the report. It stays read-only: a docstring finding is a suggestion, never an in-place edit. See [mathlib-style.md § Avoid Development History References](../skills/lean4/references/mathlib-style.md#avoid-development-history-references) for what to flag.

## See Also

- `/lean4:prove` - Guided cycle-by-cycle proving
- `/lean4:autoprove` - Autonomous multi-cycle proving
- `/lean4:disprove` - Guided counterexample search with certified refutation
- `/lean4:golf` - Apply golfing optimizations
- [mathlib-style.md](../skills/lean4/references/mathlib-style.md)
- [mathlib-review-taxonomy.md](../skills/lean4/references/mathlib-review-taxonomy.md) — the vocabulary the [Mathlib Review Layer](#mathlib-review-layer-layer-2) emits. Its buckets become first-class findings when Layer 2 is at full strictness, and advisory findings otherwise.
- [Examples](../skills/lean4/references/command-examples.md#review)

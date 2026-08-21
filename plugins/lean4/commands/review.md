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
```

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
| --debate | No | `ask` (default), `auto`, or `off`. Gate for trigger-detected finding adjudication — see [Finding Adjudication](#finding-adjudication-trigger-gated). Batch mode only. |

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

The **Primary blocker class** value uses the Blocked-Goal Triage vocabulary from [sorry-filling.md](../skills/lean4/references/sorry-filling.md) (definitional equality / missing intro-constructor-cases / missing rewrite / arithmetic / missing library lemma / typeclass-coercion-elaboration / needs helper lemma) and classifies the top blocker — the listed blockers may span classes. The **Evidence** block records the searches attempted, top candidate lemmas returned, and `lean_multi_attempt` outcomes required by the cycle-engine stuck-handoff contract, so a stuck review is a valid handoff record on its own. These fields are part of the human-readable report only — the JSON summary schema is unchanged; machine-readable extension is deferred pending the schema work in #115.

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

## Actions

The agent selects files based on scope, then runs these analyses (per file or directory):

1. **Build Status** - `lake build` (project-wide); for scoped review (`--scope=file`), use `lean_diagnostic_messages(file)` + `lake env lean <path/to/File.lean>` (run from project root) first
2. **Sorry Audit** - `lean4-skills-sorry-analyzer <target> --format=json --report-only`
3. **Axiom Check** - `lean4-skills-check-axioms-inline <target> --report-only`
4. **Style Review** - Check mathlib conventions (naming, structure, tactics, 100-char line width). Flag lines wrapped under 100 chars that fit on one line (common: `mkAppM` calls, short struct literals, single-expression tactic lines).
5. **Golfing Opportunities** - `lean4-skills-find-golfable <target> --filter-false-positives`
6. **Complexity Metrics** - Proof sizes, longest proofs, tactic patterns

**Stuck mode:** Steps 5–6 are skipped; focus is on blockers (steps 1–4) for quick triage.

## Finding Adjudication (trigger-gated)

Review's instance of the shared [debate engine](../skills/lean4/references/debate-engine.md#review-finding-adjudication). After the analyses complete and before the report is written, check each candidate finding for adjudication triggers:

- the evidence is uncertain — no specific rule, lemma, or diagnostic backs the finding
- the severity or category boundary is contested
- the proposed remedy is destructive enough that a false positive would be costly (delete-or-replace class suggestions)

If any finding triggers and `--debate=ask` (the default), show one proposal covering all triggered findings and wait for opt-in — never auto-run. `--debate=auto` runs without prompting; `--debate=off` disables adjudication and its proposals. On opt-in, run one inline round per triggered finding: **Advocate**, **Skeptic**, and **Maintainer** each commit to a position over the collected analysis output (budget: 0 new tool calls). A finding is reported only if the Advocate's case survives the Skeptic's strongest objection; the Maintainer's answer sets severity and placement. Findings that fail adjudication move from Recommendations to a short "Set aside by adjudication" list with one-line reasons.

Boundaries: batch mode only — stuck mode is a fast triage path owned by the proving commands and never runs debates or proposals. Adjudication filters and labels findings the analyses above already produced; it does not create new finding sources (broadening what review emits remains #110's scope). It affects the human-readable report only — the `--json` schema is unchanged (machine-readable adjudication markers are deferred to #115). Review stays read-only throughout.

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

Custom hooks receive structured JSON on stdin with file information, sorries, axioms, and build status. They return JSON with a `suggestions` array.

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

Return suggestions as JSON:
{"suggestions": [{"file": "...", "line": N, "severity": "hint|warning", "message": "..."}]}
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

## JSON Output Schema

When using `--json`, output follows this structure:

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

### Option B: SDK Automation (`codex exec`)

For CI or scripted reviews, use `codex exec` with a review prompt:

```bash
codex exec "Review this Lean 4 proof for correctness, focusing on:
1. Incomplete sorries and proof gaps
2. Type mismatches or missing instances
3. Non-standard axiom usage

$(cat Core.lean)
" --output-schema lean4-review-schema.json -o review-output.json
```

**Schema file (`lean4-review-schema.json`):**
```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "type": "object",
  "properties": {
    "suggestions": {
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "file": {"type": "string"},
          "line": {"type": "integer"},
          "severity": {"enum": ["hint", "warning"]},
          "category": {"enum": ["sorry", "axiom", "style", "structure"]},
          "message": {"type": "string"}
        },
        "required": ["file", "line", "severity", "message"]
      }
    }
  },
  "required": ["suggestions"]
}
```

See [Codex SDK Cookbook](https://cookbook.openai.com/examples/codex/build_code_review_with_codex_sdk) for CI integration patterns.

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
- [debate-engine.md](../skills/lean4/references/debate-engine.md) — shared deliberation module; review's finding-adjudication instance
- [mathlib-style.md](../skills/lean4/references/mathlib-style.md)
- [mathlib-review-taxonomy.md](../skills/lean4/references/mathlib-review-taxonomy.md) — reference for what mathlib reviewers ask for. This is background material only: it does **not** change `/lean4:review`'s current behavior; deciding when these buckets become emitted findings is Issue #110.
- [Examples](../skills/lean4/references/command-examples.md#review)

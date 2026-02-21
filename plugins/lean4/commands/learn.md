---
name: learn
description: Interactive teaching, mathlib exploration, and autoformalization
user_invocable: true
---

# Lean4 Learn

Interactive teaching, mathlib exploration, and autoformalization. Adapts to beginner, intermediate, and expert audiences.

## Usage

```
/lean4:learn                                 # Start conversational discovery
/lean4:learn Finset.sum                      # Auto-detect mode from topic
/lean4:learn --mode=repo                     # Explore current project
/lean4:learn --mode=mathlib topology         # Navigate mathlib for a topic
/lean4:learn --mode=formalize "Every continuous function on a compact set is bounded"
/lean4:learn --mode=formalize --rigor=axiomatic "Zorn's lemma implies AC"
/lean4:learn --style=socratic --interactive  # True Socratic method
/lean4:learn --output=scratch                # Write results to scratch file
```

## Inputs

| Arg | Required | Default | Description |
|-----|----------|---------|-------------|
| topic | no | — | Free-text topic, theorem name, file path, or natural-language claim. If omitted, start conversational discovery; set `--mode` after first user reply. |
| --mode | no | `auto` | `auto` \| `repo` \| `mathlib` \| `formalize` |
| --level | no | `intermediate` | `beginner` \| `intermediate` \| `expert` |
| --scope | no | `auto` | `auto` \| `file` \| `changed` \| `project` \| `topic` |
| --style | no | `tour` | `tour` \| `socratic` \| `exercise` |
| --rigor | no | `checked` | `checked` \| `sketch` \| `axiomatic` |
| --output | no | `chat` | `chat` \| `scratch` \| `file` |
| --out | no | — | Output path. Required when `--output=file`; hard error if missing. |
| --overwrite | no | `false` | Allow overwriting existing files with `--output=file`. Without flag, existing target → hard error. |
| --interactive | no | `false` | True Socratic method (withhold answers, ask questions). Valid only with `--style=socratic`; ignored with warning otherwise. |

### Scope defaults by mode (when `--scope=auto`)

| Mode | Default scope |
|------|--------------|
| `repo` | `file` |
| `mathlib` | `topic` |
| `formalize` | `topic` |

### Scope coercions

- `--mode=formalize` + `--scope=file|changed|project` → warn "formalize mode operates on topics, not file scopes" + coerce to `topic`
- `--mode=mathlib` + `--scope=file|changed|project` → warn + coerce to `topic`, unless topic resolves to a local declaration

### Output validation

- `--output=file` without `--out` → hard error
- `--output=scratch` → scratch dir resolved by fallback: `.claude/scratch/` → `.codex/scratch/` → `/tmp/lean4-learn/`. Use first that exists or can be created. Auto-create dir; warn if scratch dir is inside workspace and not in `.gitignore`. File name: `learn-<timestamp>.lean`.
- `--output=file` with existing target and no `--overwrite` → hard error

## Actions

### 1. Mode Resolution

When `--mode=auto`, resolve by tie-breaking order:

1. If topic resolves to an existing `.lean` file path → `repo`
2. Resolve topic against project-local declarations (via `Grep`/`$LEAN4_SCRIPTS/find_usages.sh`). **Local wins** — if both local and mathlib match, prefer local → `repo`
3. Check mathlib namespace/theorem names (via `lean_local_search`, `lean_leanfinder`/`lean_leansearch`, `lean_loogle`) → `mathlib`
4. If topic is a natural-language mathematical statement → `formalize`
5. If ambiguous → ask the user

When no topic is provided, enter conversational discovery and set `--mode` after the user's first reply.

### 2. Discovery (per mode)

**repo:** `Glob`/`Grep` (file survey) → `Read` (targeted content) → `$LEAN4_SCRIPTS/find_usages.sh` (dependency pass). Build a map: key files, declarations, dependency flow, where proofs live.

**mathlib:** `lean_local_search` → one semantic search (`lean_leanfinder` for goal/proof-state shaped queries, `lean_leansearch` for natural-language concept queries) → `lean_loogle` (type-pattern gaps). Present canonical lemmas, type signatures, minimal usage examples.

**formalize:** Parse natural-language claim → draft theorem skeleton → `lean_goal` + `lean_multi_attempt` loop.

**Fallback rule:** If a tool is unavailable or rate-limited, continue with the next tool in order and note the fallback in output.

### 3. Explanation

Present findings at the user's `--level` in the user's `--style`:

- **tour:** Narrated walkthrough, explains as it goes.
- **socratic:** Guided discovery with prompts. If `--interactive`, withhold answers and ask user questions first — delay direct solutions until user has engaged.
- **exercise:** Present a challenge, let user attempt, then explain. If `--rigor=checked`, always end with a verified reference solution.

### 4. Depth Check

Offer the depth-check menu:

- show source / show proof state / show alternative approach
- go deeper / switch mode / broaden scope
- **save to scratch** / **write to file** (mid-session output actions — `--output` is part of the loop, not just startup config)

### 5. Iterate

Return to step 2 with refined scope based on user's choice. Continue until the user is satisfied or switches mode.

### 6. Formalize: Falsification & Rigor

In formalize mode, before committing to a proof:

**Falsification branch:** If the claim is decidable/finite and a counterexample is found, stop proving. Produce the counterexample and offer salvage: (a) add hypotheses, (b) weaken conclusion, (c) explore why it fails.

**Rigor completion criteria:**

| Rigor | sorry | Diagnostics | Non-standard axiom | Silent global axiom |
|-------|-------|-------------|-------------------|-------------------|
| `checked` | **FAIL** | **FAIL** | **FAIL** | **FAIL** |
| `axiomatic` | **FAIL** | **FAIL** | allowed if in ledger | **FAIL** |
| `sketch` | allowed | allowed | allowed | **FAIL** |

- `sketch`: never fails finalization, but always prints `-- ⚠ NOT VERIFIED — sketch only` banner.
- `axiomatic`: allows explicit assumptions but hard-fails on any silently introduced global axiom not in the ledger.
- All modes hard-fail on silent global axioms — no exceptions.

**If proof blocked** (no counterexample found), offer in order: local assumptions as parameters (preferred) → explicit axiomatic draft with assumption ledger + warning.

## Output

In `chat` mode, output is inline markdown with Lean code blocks. In `scratch` or `file` mode, additionally write a `.lean` file.

### Assumption Ledger (formalize + axiomatic)

```
-- Assumption Ledger
-- ┌──────────────────────────┬────────────────────┬───────────┬─────────────────────┐
-- │ Assumption               │ Justification      │ Scope     │ Introduced by       │
-- ├──────────────────────────┼────────────────────┼───────────┼─────────────────────┤
-- │ h_cont : Continuous f    │ stated in claim    │ parameter │ user-stated         │
-- │ h_bdd : IsBounded S     │ needed for compact │ parameter │ assistant-inferred  │
-- └──────────────────────────┴────────────────────┴───────────┴─────────────────────┘
```

### Standard Axiom Whitelist

`propext`, `Classical.choice`, `Quot.sound` — not flagged. All others reported as non-standard.

Always run `$LEAN4_SCRIPTS/check_axioms_inline.sh` before presenting final formalize results.

## Safety

- **Read-only by default.** `repo` and `mathlib` modes never write files unless `--output` requests it. `formalize` is read-only in `chat` mode.
- **No silent mutations.** Prefer LSP tools (`lean_goal`) over file writes for compilation checks. If LSP unavailable and temp file needed for internal compilation, write only under `/tmp/lean4-learn/`, auto-cleanup after use, warn user before writing.
- **No commits.** `/learn` never commits. `--output=file` writes but does not stage or commit.
- **Path restriction.** User-requested outputs (`--output=file`, `--output=scratch`) restricted to workspace root. Reject path traversal (`../`) or absolute paths outside workspace. Internal temp files may use `/tmp`.
- **Overwrite protection.** `--output=file` with existing target requires `--overwrite`; otherwise hard error.
- **Never add global axioms silently.** Assumptions go as explicit theorem parameters or in `namespace Assumptions`. Always verified with `$LEAN4_SCRIPTS/check_axioms_inline.sh`.
- **Scope guardrails.** `--scope=project` in repo mode with >50 `.lean` files → warn with count, ask to narrow. In non-interactive contexts (e.g., LLM-invoked), default to "no" (do not proceed with large scope).
- **All `guardrails.sh` rules apply.**

## See Also

- [Examples](../skills/lean4/references/command-examples.md#learn)
- [Cycle Engine](../skills/lean4/references/cycle-engine.md) — shared mechanics
- [LSP Tools API](../skills/lean4/references/lean-lsp-tools-api.md) — search tools used in mathlib mode
- [Mathlib Guide](../skills/lean4/references/mathlib-guide.md) — mathlib navigation

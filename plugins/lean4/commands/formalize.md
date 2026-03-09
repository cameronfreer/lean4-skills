---
name: formalize
description: Turn informal math into Lean statements
user_invocable: true
---

# Lean4 Formalize

Turn informal mathematical claims into Lean 4 theorem statements. Drafts skeletons, attempts proofs, verifies axiom hygiene, and produces an assumption ledger for axiomatic drafts.

## Usage

```
/lean4:formalize "Every continuous function on a compact set is bounded"
/lean4:formalize --rigor=axiomatic "Zorn's lemma implies AC"
/lean4:formalize --source ./paper.pdf          # Ingest, pick claims, formalize
/lean4:formalize --source ./paper.pdf "Theorem 3.2"  # Source as context, topic as claim
/lean4:formalize --output=file --out=MyTheorem.lean "..."
```

## Inputs

| Arg | Required | Default | Description |
|-----|----------|---------|-------------|
| topic | no | — | Informal claim to formalize. Optional when `--source` provides it (source-led flow). At least one of `topic` or `--source` must be given; omitting both is a hard error. |
| --rigor | no | `checked` | `checked` \| `sketch` \| `axiomatic` |
| --level | no | `intermediate` | `beginner` \| `intermediate` \| `expert` |
| --output | no | `chat` | `chat` \| `scratch` \| `file` |
| --out | no | — | Output path. Required when `--output=file`; hard error if missing. |
| --overwrite | no | `false` | Allow overwriting existing files with `--output=file`. Without flag, existing target → hard error. |
| --source | no | — | File path, URL, or PDF to seed formalization. See [learn-pathways.md](../skills/lean4/references/learn-pathways.md#source-handling). |
| --intent | no | `math` | `auto` \| `usage` \| `math`. See [learn-pathways.md](../skills/lean4/references/learn-pathways.md#intent-taxonomy). |
| --presentation | no | `auto` | `informal` \| `supporting` \| `formal` \| `auto`. Controls user-facing display, not Lean backing. See [learn-pathways.md](../skills/lean4/references/learn-pathways.md#two-layer-architecture). |
| --verify | no | `best-effort` | `best-effort` \| `strict`. Verification strictness for key claims. See [learn-pathways.md](../skills/lean4/references/learn-pathways.md#verification-status). |

### Output validation

- `--output=file` without `--out` → hard error
- `--output=scratch` → `.scratch/lean4/formalize-<timestamp>.lean` (workspace-local). Auto-create `.scratch/lean4/` if missing; warn if `.scratch/` is not in `.gitignore`.
- `--output=file` with existing target and no `--overwrite` → hard error

### Flag validation

- `--intent`, `--presentation`, or `--verify` with invalid value → hard error.
- `--intent=auto` inference: apply the shared [inference rules](../skills/lean4/references/learn-pathways.md#inference-rules-when---intentauto), then coerce `internals` → `usage` and `authoring` → `usage` (formalize does not define behavior for those intents).
- `--source` + unreadable format → warn + ask for text excerpt.

## Actions

### 0. Intent Intake

Resolve `--intent` and `--presentation`. Defaults: `--intent=math`, `--presentation=auto` (→ `informal` for math intent). Announce resolved values. Explicit flags override inference.

**Two-layer contract:** Lean verification is attempted for all key claims. `--presentation` controls what is shown, not whether Lean runs. Each key-claim step carries a verification label: `[verified]`, `[partially-verified]`, or `[unverified]`. Under `--verify=strict`, never present claims as settled unless verified; on failure after retry, mark blocked and offer: continue conceptually or relax to `best-effort`. See [learn-pathways.md](../skills/lean4/references/learn-pathways.md#two-layer-architecture).

### 1. Claim Acquisition

Two entry points:

- **Direct:** `topic` given → parse the informal claim directly.
- **Source-led:** `--source` given, no `topic` → ingest source (`.lean` → `Read`; PDF → `Read`; `.md`/`.txt` → `Read`; URL → web fetch; other → warn + ask for excerpt). Extract candidate claims, present to user, user picks which to formalize.
- **Both:** `topic` and `--source` given → use topic as the claim and source as supporting context.

### 2. Draft Theorem Skeleton

Parse natural-language claim → draft theorem skeleton with appropriate types, hypotheses, and conclusion. Use mathlib naming conventions and types where possible (`lean_local_search`, `lean_leanfinder`/`lean_leansearch`, `lean_loogle` to find canonical types).

### 3. Proof Attempt

`lean_goal` + `lean_multi_attempt` loop. Search mathlib for existing proofs or applicable lemmas before writing tactics from scratch.

### 4. Falsification & Rigor

Before committing to a proof:

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

### 5. Depth Check

Offer the depth-check menu:

- show source / show proof state
- alternative formalization (e.g., different types or encoding)
- generalize (weaken hypotheses)
- strengthen (add conclusions)
- save to scratch / write to file

## Output

Output format follows `--presentation`: `informal` → prose with math notation (no Lean blocks unless user requests "show Lean backing"); `supporting` → prose with selective Lean snippets; `formal` → Lean code blocks as primary content. In `scratch` or `file` mode, additionally write a `.lean` file regardless of presentation.

### Assumption Ledger (axiomatic rigor)

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

Always run `bash "$LEAN4_SCRIPTS/check_axioms_inline.sh" <target> --report-only` before presenting final results.

## Safety

- **Read-only in chat mode.** Does not write files unless `--output` requests it.
- **No silent mutations.** Prefer LSP tools (`lean_goal`) over file writes for compilation checks. If LSP unavailable and temp file needed for internal compilation, write only under `/tmp/lean4-formalize/`, auto-cleanup after use, warn user before writing.
- **No commits.** `/formalize` never commits. `--output=file` writes but does not stage or commit.
- **Path restriction.** User-requested outputs (`--output=file`, `--output=scratch`) restricted to workspace root (scratch uses `.scratch/lean4/`). Reject path traversal (`../`) or absolute paths outside workspace. Internal temp files may use `/tmp/lean4-formalize/`.
- **Overwrite protection.** `--output=file` with existing target requires `--overwrite`; otherwise hard error.
- **Never add global axioms silently.** Assumptions go as explicit theorem parameters or in `namespace Assumptions`. Always verified with `bash "$LEAN4_SCRIPTS/check_axioms_inline.sh" <target> --report-only`.
- **All `guardrails.sh` rules apply.**

## See Also

- [Examples](../skills/lean4/references/command-examples.md#formalize)
- [LSP Tools API](../skills/lean4/references/lean-lsp-tools-api.md) — search tools used in proof attempts
- [Learning Pathways](../skills/lean4/references/learn-pathways.md) — intent taxonomy, source handling

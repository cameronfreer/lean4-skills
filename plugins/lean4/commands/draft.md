---
name: draft
description: Draft Lean declaration skeletons from informal claims
user_invocable: true
---

# Lean4 Draft

Draft Lean 4 declaration skeletons from informal mathematical claims. Produces sorry-stubbed statements ready for `/lean4:prove` or `/lean4:autoprove`.

## Usage

```
/lean4:draft "Every continuous function on a compact set is bounded"
/lean4:draft --mode=attempt "Zorn's lemma implies AC"
/lean4:draft --source ./paper.pdf          # Ingest, pick claims, draft skeletons
/lean4:draft --source ./paper.pdf "Theorem 3.2"  # Source as context, topic as claim
/lean4:draft --output=file --out=MyTheorem.lean "..."
```

## Inputs

| Arg | Required | Default | Description |
|-----|----------|---------|-------------|
| topic | no | — | Informal claim to draft. Optional when `--source` provides it (source-led flow). At least one of `topic` or `--source` must be given; omitting both is a hard error. |
| --mode | no | `skeleton` | `skeleton` \| `attempt`. `skeleton` produces sorry-stubbed declarations only. `attempt` adds a proof-attempt loop (`lean_multi_attempt`) before finalizing. |
| --elab-check | no | `best-effort` | `best-effort` \| `strict`. Elaboration check strictness for drafted skeletons. |
| --level | no | `intermediate` | `beginner` \| `intermediate` \| `expert` |
| --output | no | `chat` | `chat` \| `scratch` \| `file` |
| --out | no | — | Output path. Required when `--output=file`; hard error if missing. |
| --overwrite | no | `false` | Allow overwriting existing files with `--output=file`. Without flag, existing target → hard error. |
| --source | no | — | File path, URL, or PDF to seed drafting. See [learn-pathways.md](../skills/lean4/references/learn-pathways.md#source-handling). |
| --intent | no | `math` | `auto` \| `usage` \| `math`. See [learn-pathways.md](../skills/lean4/references/learn-pathways.md#intent-taxonomy). |
| --presentation | no | `auto` | `informal` \| `supporting` \| `formal` \| `auto`. Controls user-facing display, not Lean backing. See [learn-pathways.md](../skills/lean4/references/learn-pathways.md#two-layer-architecture). |
| --claim-select | no | — | `first` \| `named:"..."` \| `regex:"..."`. Noninteractive claim selection from `--source`. See below. |

### Output validation

- `--output=file` without `--out` → hard error
- `--output=scratch` → `.scratch/lean4/draft-<timestamp>.lean` (workspace-local). Auto-create `.scratch/lean4/` if missing; warn if `.scratch/` is not in `.gitignore`.
- `--output=file` with existing target and no `--overwrite` → hard error

### Flag validation

- `--intent`, `--presentation`, or `--elab-check` with invalid value → hard error.
- `--intent=auto` inference: apply the shared [inference rules](../skills/lean4/references/learn-pathways.md#inference-rules-when---intentauto), then coerce `internals` → `usage` and `authoring` → `usage` (draft does not define behavior for those intents).
- `--source` + unreadable format → warn + ask for text excerpt.
- `--claim-select` without `--source` → hard error (nothing to select from).

### Noninteractive Claim Selection

| Policy | Behavior |
|--------|----------|
| `first` | Select the first extractable claim from `--source` |
| `named:"..."` | Match claims by title/label substring (e.g. `named:"Theorem 3.2"`) |
| `regex:"..."` | Match claims by regex on extracted claim text |

Standalone draft processes one claim per invocation (batch-size is 1). When called by the synthesis outer loop (`--caller=autoformalize` or `--caller=formalize`), draft receives a single pre-selected claim as its topic. The outer loop owns queue extraction and iteration — see [cycle-engine.md](../skills/lean4/references/cycle-engine.md#claim-queue).

### File Write Contract

Standalone draft writes whole files via `--output=file` + `--out`. When called with `--caller=autoformalize` or `--caller=formalize` (internal-only flag), draft writes declaration-only blocks to `$TMPDIR/lean4-draft/<session-id>/claim-<N>.lean` with `-- needs-import:` comments. The outer loop owns file assembly and commits. See [cycle-engine.md](../skills/lean4/references/cycle-engine.md#file-assembly-contract).

## Actions

### 0. Intent Intake

Resolve `--intent` and `--presentation`. Defaults: `--intent=math`, `--presentation=auto` (→ `informal` for math intent). Announce resolved values. Explicit flags override inference.

### 1. Claim Acquisition

Two entry points:

- **Direct:** `topic` given → parse the informal claim directly.
- **Source-led:** `--source` given, no `topic` → ingest source (`.lean` → `Read`; PDF → `Read`; `.md`/`.txt` → `Read`; URL → web fetch; other → warn + ask for excerpt). Extract candidate claims. If `--claim-select` is present, select noninteractively per policy; otherwise present to user, user picks which to draft.
- **Both:** `topic` and `--source` given → use topic as the claim and source as supporting context.

### 2. Draft Theorem Skeleton

Parse natural-language claim → draft theorem skeleton with appropriate types, hypotheses, and conclusion. Use mathlib naming conventions and types where possible (`lean_local_search`, `lean_leanfinder`/`lean_leansearch`, `lean_loogle` to find canonical types).

### 3. Elaboration Check

Run `lean_diagnostic_messages` on the drafted skeleton. Under `--elab-check=strict`, all diagnostics must be clean (excluding the expected sorry). Under `--elab-check=best-effort`, attempt to fix diagnostics but continue if unfixable.

### 4. Proof Attempt (--mode=attempt only)

When `--mode=attempt`: `lean_goal` + `lean_multi_attempt` loop. Search mathlib for existing proofs or applicable lemmas before writing tactics from scratch. If proof succeeds, include it. If proof fails, leave sorry and note the attempt.

This mode recovers the proof-attempt behavior of the old `/lean4:formalize` command. For full synthesis (including falsification, rigor completion, and assumption ledgers), use `/lean4:formalize`.

### 5. Depth Check

Offer the depth-check menu:

- show source / show proof state
- alternative formalization (e.g., different types or encoding)
- save to scratch / write to file

## Output

Output format follows `--presentation`: `informal` → prose with math notation (no Lean blocks unless user requests "show Lean backing"); `supporting` → prose with selective Lean snippets; `formal` → Lean code blocks as primary content. In `scratch` or `file` mode, additionally write a `.lean` file regardless of presentation.

## Safety

- **Read-only in chat mode.** Does not write files unless `--output` requests it.
- **No silent mutations.** Prefer LSP tools (`lean_goal`) over file writes for compilation checks. If LSP unavailable and temp file needed for internal compilation, write only under `/tmp/lean4-draft/`, auto-cleanup after use, warn user before writing.
- **No commits.** `/draft` never commits. `--output=file` writes but does not stage or commit.
- **Path restriction.** User-requested outputs (`--output=file`, `--output=scratch`) restricted to workspace root (scratch uses `.scratch/lean4/`). Reject path traversal (`../`) or absolute paths outside workspace. Internal temp files may use `/tmp/lean4-draft/`.
- **Overwrite protection.** `--output=file` with existing target requires `--overwrite`; otherwise hard error.
- **Caller integration:** When `--caller=autoformalize` or `--caller=formalize`, file assembly and `draft:` commits are handled by the outer loop, not by draft.
- **All `guardrails.sh` rules apply.**

## See Also

- [Examples](../skills/lean4/references/command-examples.md#draft)
- [LSP Tools API](../skills/lean4/references/lean-lsp-tools-api.md) — search tools used in proof attempts
- [Learning Pathways](../skills/lean4/references/learn-pathways.md) — intent taxonomy, source handling
- `/lean4:formalize` — interactive synthesis (draft + prove)
- `/lean4:autoformalize` — autonomous synthesis (draft + autoprove)

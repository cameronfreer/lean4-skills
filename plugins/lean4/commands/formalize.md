---
name: formalize
description: Interactive formalization — drafting plus guided proving
user_invocable: true
---

# Lean4 Formalize

Interactive formalization: draft Lean skeletons from informal claims, then prove them with guided cycles. Combines `/lean4:draft` and `/lean4:prove` in a single human-in-the-loop workflow.

**Compatibility:** Accepts all flags from old formalize (v4.3.x). Semantics are broader — new formalize runs a full prove cycle after drafting. Users wanting the old lighter-weight "draft + shallow proof attempt" behavior should use `/lean4:draft --mode=attempt`. Users wanting skeletons only should use `/lean4:draft`.

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
| --verify | no | `best-effort` | `best-effort` \| `strict`. Verification strictness for key claims. See [learn-pathways.md](../skills/lean4/references/learn-pathways.md#verification-status). |
| --level | no | `intermediate` | `beginner` \| `intermediate` \| `expert` |
| --output | no | `chat` | `chat` \| `scratch` \| `file` |
| --out | no | — | Output path. Required when `--output=file`; hard error if missing. |
| --overwrite | no | `false` | Allow overwriting existing files with `--output=file`. Without flag, existing target → hard error. |
| --source | no | — | File path, URL, or PDF to seed formalization. See [learn-pathways.md](../skills/lean4/references/learn-pathways.md#source-handling). |
| --intent | no | `math` | `auto` \| `usage` \| `math`. See [learn-pathways.md](../skills/lean4/references/learn-pathways.md#intent-taxonomy). |
| --presentation | no | `auto` | `informal` \| `supporting` \| `formal` \| `auto`. Controls user-facing display, not Lean backing. See [learn-pathways.md](../skills/lean4/references/learn-pathways.md#two-layer-architecture). |
| --claim-select | no | — | `first` \| `named:"..."` \| `regex:"..."`. Noninteractive claim selection from `--source`. |
| --draft-mode | no | `attempt` | `skeleton` \| `attempt`. Mode for the draft phase (default is `attempt` in formalize context). |
| --draft-elab-check | no | `best-effort` | `best-effort` \| `strict`. Elaboration check for the draft phase. |
| --deep | no | never | `never` \| `ask` \| `stuck` \| `always`. Deep mode for prove phase. |
| --deep-sorry-budget | no | 1 | Max sorries per deep invocation |
| --deep-time-budget | no | 10m | Max time per deep invocation |
| --commit | no | ask | `ask` \| `auto` \| `never` |
| --golf | no | prompt | `prompt` \| `auto` \| `never` |

### Output validation

- `--output=file` without `--out` → hard error
- `--output=scratch` → `.scratch/lean4/formalize-<timestamp>.lean` (workspace-local). Auto-create `.scratch/lean4/` if missing; warn if `.scratch/` is not in `.gitignore`.
- `--output=file` with existing target and no `--overwrite` → hard error

### Flag validation

- `--intent`, `--presentation`, or `--verify` with invalid value → hard error.
- `--intent=auto` inference: apply the shared [inference rules](../skills/lean4/references/learn-pathways.md#inference-rules-when---intentauto), then coerce `internals` → `usage` and `authoring` → `usage` (formalize does not define behavior for those intents).
- `--source` + unreadable format → warn + ask for text excerpt.
- `--claim-select` without `--source` → hard error (nothing to select from).

### Noninteractive Claim Selection

| Policy | Behavior |
|--------|----------|
| `first` | Select the first extractable claim from `--source` |
| `named:"..."` | Match claims by title/label substring (e.g. `named:"Theorem 3.2"`) |
| `regex:"..."` | Match claims by regex on extracted claim text |

Standalone formalize processes one claim per invocation (batch-size is 1).

## Actions

### Phase 1: Draft

Invoke draft logic (same algorithm as `/lean4:draft`):

1. **Intent Intake** — resolve `--intent` and `--presentation`.
2. **Claim Acquisition** — parse topic or ingest `--source`.
3. **Draft Theorem Skeleton** — translate claim to sorry-stubbed Lean declaration.
4. **Elaboration Check** — `lean_diagnostic_messages` on skeleton.
5. **Proof Attempt** (when `--draft-mode=attempt`, default) — `lean_goal` + `lean_multi_attempt` loop.

### Phase 2: Prove

Invoke prove logic (same algorithm as `/lean4:prove`):

1. Run guided prove cycle on the drafted declaration.
2. Falsification & rigor checks per `--rigor`.
3. User confirms or adjusts between cycles.

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

### Phase 3: Statement Mismatch Handling

If the prove phase concludes the statement is wrong (deep mode emits `next_action = redraft`), present to user:

1. **Redraft** — return to Phase 1 with revised claim
2. **Salvage sibling** — create `T_salvaged` with weaker statement
3. **Preserve + stop** — keep current statement, mark sorry, stop
4. **Continue** — keep trying with current statement

**Permission boundary:** Formalize owns the right to change declaration headers. The prove phase itself cannot — it recommends redraft, and formalize executes the change with user approval.

### Phase 4: Depth Check

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
- **No commits in standalone mode.** `/formalize` never commits in standalone mode (`--commit` is accepted for prove-phase compatibility but inert — no staging, no committing). `--output=file` writes but does not stage or commit.
- **Path restriction.** User-requested outputs (`--output=file`, `--output=scratch`) restricted to workspace root (scratch uses `.scratch/lean4/`). Reject path traversal (`../`) or absolute paths outside workspace. Internal temp files may use `/tmp/lean4-formalize/`.
- **Overwrite protection.** `--output=file` with existing target requires `--overwrite`; otherwise hard error.
- **Never add global axioms silently.** Assumptions go as explicit theorem parameters or in `namespace Assumptions`. Always verified with `bash "$LEAN4_SCRIPTS/check_axioms_inline.sh" <target> --report-only`.
- **All `guardrails.sh` rules apply.**

## See Also

- [Examples](../skills/lean4/references/command-examples.md#formalize)
- [LSP Tools API](../skills/lean4/references/lean-lsp-tools-api.md) — search tools used in proof attempts
- [Learning Pathways](../skills/lean4/references/learn-pathways.md) — intent taxonomy, source handling
- `/lean4:draft` — skeleton-only drafting (no prove phase)
- `/lean4:autoformalize` — autonomous synthesis (unattended)

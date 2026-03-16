---
name: refactor
description: Leverage mathlib, extract helpers, simplify proof strategies
user_invocable: true
---

# Lean4 Refactor

Strategy-level proof simplification: find better proof approaches, leverage mathlib, and extract reusable helpers. Complements `/lean4:golf` (tactic-level optimization) and `/lean4:review` (read-only audit).

**Mutating command:** Edits files with user approval. Does not change theorem statements, introduce axioms, or create commits.

## Usage

```
/lean4:refactor File.lean                  # Refactor all proofs in file
/lean4:refactor File.lean:149              # Refactor proof at line 149
/lean4:refactor --scope=changed            # Refactor files modified since last commit
/lean4:refactor --scope=changed --dry-run  # Report opportunities without editing
```

## Inputs

| Arg | Required | Description |
|-----|----------|-------------|
| target | No | File or `File.lean:line` |
| --scope | No | `file` (default with target), `changed` (default without target) |
| --dry-run | No | Report only, do not edit |
| --search | No | `quick` (default) or `full` (exhaustive mathlib search) |
| --extract-helpers | No | `on` (default) or `off` (skip helper extraction) |

## Scope Behavior

| Input | Scope |
|-------|-------|
| `File.lean` | All proofs in file |
| `File.lean:149` | Single proof containing line 149 |
| No target | `--scope=changed` (files modified since last commit) |
| `--scope=changed` | Files modified since last commit |

**Line target:** Identifies the enclosing `theorem`/`lemma`/`def` containing the given line and refactors that proof only.

**Large-run confirmation:** When `--scope=changed` touches >5 files or >20 opportunities, confirm before proceeding.

## Preconditions

- Target proofs must compile (no sorries, no build errors in scope)
- Run `/lean4:prove` or `/lean4:autoprove` first if there are open sorries

**Refusal:** If preconditions are not met:
```
⚠️  Cannot refactor: File.lean has 2 sorries and 1 build error.
Run /lean4:prove first, then retry /lean4:refactor.
```

## Actions

1. **Audit** — Read target proofs, identify repeated patterns, long proofs (>30 lines), hand-rolled arguments, case splits replaceable by `congr`/`EqOn`/`EventuallyEq`, thin definition APIs
2. **Search** — For each opportunity, search mathlib via [LSP-first protocol](../skills/lean4/references/cycle-engine.md#lsp-first-protocol). `--search=quick`: up to 2 LSP queries per opportunity. `--search=full`: up to 5 queries with module exploration.
3. **Plan** — Present findings with estimated impact:
   ```markdown
   ## Refactor Plan — File.lean
   ### Strategy Improvements
   1. [proof] (line N): [current] → Use [mathlib lemma] (saves ~N lines)
   ### Helper Extraction
   1. [pattern] — Nx (lines ...) → Extract `helper_name`
   ### Estimated Impact
   - Lines before: N → after: ~N | Helpers: N | New mathlib lemmas: N
   ```
4. **Approval** — Ask before each batch (`--dry-run` stops here). A batch groups opportunities within a single proof or closely related proofs. Prompt: `Apply batch N (M changes)? [yes / skip / stop]` — yes applies, skip moves to next batch, stop ends the session.
5. **Apply** — Edit files, verify with `lean_diagnostic_messages` after each batch; revert batch on any new diagnostic or sorry increase
6. **Verify** — `lake env lean <file>` file gate (run from project root); `lake build` project gate if multi-file. If final gate fails, revert all batches applied in this session.
7. **Report** — Summarize changes applied, helpers extracted, line count delta

See [proof-simplification](../skills/lean4/references/proof-simplification.md) for the strategy guide (congr/EqOn patterns, generalization checklist, file-level audit).

**Helper scope defaults:** Single use inside one proof → local (`have` / local helper). Reused within one file → `private theorem`. Public/non-private → only with explicit user approval or clear existing API reason.

## Safety

- Does not change theorem/lemma statements
- Does not introduce axioms
- Does not create commits
- Asks before each batch of edits
- Reverts batch on per-batch verification failure; reverts all session batches on final gate failure
- Compiled proofs only (refuses files with sorries or build errors)

## See Also

- `/lean4:review` - Read-only quality audit
- `/lean4:golf` - Tactic-level optimization
- `/lean4:prove` - Guided theorem proving
- [proof-simplification.md](../skills/lean4/references/proof-simplification.md)
- [proof-refactoring.md](../skills/lean4/references/proof-refactoring.md)
- [Examples](../skills/lean4/references/command-examples.md#refactor)

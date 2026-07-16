---
name: bump
description: Bump a Lean project to a newer Lean/mathlib version and adopt new library APIs
user_invocable: true
---

# Lean4 Bump

Upgrade an existing Lean project to a newer Lean toolchain and mathlib release: change the version, get it building again, then adopt the theorems and definitions the new release added.

**Mutating command:** Edits `lean-toolchain`, the lakefile, `lake-manifest.json`, and (in the adopt phase) `.lean` files. Commits per `--commit`; never pushes.

## Usage

```
/lean4:bump                      # Bump to the latest stable Lean/mathlib
/lean4:bump v4.32.0              # Bump to a specific version
/lean4:bump --rc=allow          # Take the newest release candidate if past stable
/lean4:bump --adopt=off         # Bump + fix build only; skip API adoption (Phase 2)
/lean4:bump --dry-run           # Resolve versions and show the plan; no edits
```

## Inputs

| Arg | Required | Description |
|-----|----------|-------------|
| target | No | Target version `vX.Y.Z` (or `X.Y.Z`); default: latest stable |
| --rc | No | `ask` (default), `allow` (take newest rc unprompted), `never` (stable only) |
| --adopt | No | `on` (default) or `off` — run Phase 2 (release-note-driven replacement) |
| --commit | No | `ask` (default), `auto`, or `never` |
| --dry-run | No | Report resolved versions + planned edits, do not modify anything |

## Actions

### Phase 0 — Preflight & Resolve

1. **Confirm a Lean project.** Require `lean-toolchain` plus a `lakefile.toml` or `lakefile.lean` at the project root. If absent, refuse (see Safety).
2. **Read the current version** from `lean-toolchain` (e.g. `leanprover/lean4:v4.28.0`) and the pinned mathlib rev from `lake-manifest.json`.
3. **Working tree should be clean.** A bump rewrites the manifest and toolchain; commit or stash first so the change is isolated and revertible. Warn if dirty.
4. **Resolve the target:**
   - `target` given → validate `vX.Y.Z` form and use it.
   - Otherwise list published mathlib tags and pick the highest **stable** one:
     ```bash
     git ls-remote --tags --refs https://github.com/leanprover-community/mathlib4 'v4.*' \
       | awk -F/ '{print $NF}' | sort -V
     ```
     Stable = `vX.Y.Z` with no `-rc`/`-nightly` suffix.
   - **rc handling:** if the project is already at the latest stable and a newer `-rc` exists, `--rc=ask` (default) prompts before adopting it; `allow` takes it; `never` reports "already current" and stops.
5. **Announce resolved inputs** — `current → target`, rc decision, whether Phase 2 will run. `--dry-run` stops here after printing the plan.

### Phase 1 — Bump & Build

1. **Point the mathlib require at the target tag.** In `lakefile.toml`:
   ```toml
   [[require]]
   name = "mathlib"
   git = "https://github.com/leanprover-community/mathlib4"
   rev = "v4.32.0"
   ```
   or in `lakefile.lean`: `require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.32.0"`.
2. **Match the toolchain to the target** — copy the exact `lean-toolchain` that mathlib tag ships, so Lean/mathlib versions can't drift:
   ```bash
   curl -fsSL https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.32.0/lean-toolchain -o lean-toolchain
   ```
3. **Update the manifest:** `lake update mathlib` (re-pins mathlib and its transitive deps; in mathlib projects this also fires the post-update `cache get` hook).
4. **Hydrate the cache and build:**
   ```bash
   lake exe cache get!   # force a fresh olean download after the version change
   lake build
   ```
   Use `lake cache get` on newer Lake where the mathlib cache executable is gone. See [doctor](doctor.md) if `lake`/cache misbehaves.
5. **Branch on the result** — build **succeeds** → Phase 2; **fails** → Phase 1b.

### Phase 1b — Repair build failures

Bumps break for a small set of recurring reasons: a lemma was **renamed or removed**, a **signature/implicit argument** changed, a declaration **moved namespaces**, or `simp`/`grind`/`aesop` now closes goals differently.

- Read the first error via `lean_diagnostic_messages` (LSP) or `lake env lean <File.lean>` (run from project root); consult [compilation-errors](../skills/lean4/references/compilation-errors.md).
- For a renamed/moved lemma, find the replacement **LSP-first** (`lean_leansearch`, `lean_loogle`, `lean_local_search`; `lean4-skills-smart-search` as fallback) and cross-check the target's release notes (Phase 2 source) for the rename.
- Apply the **minimal** fix and rebuild. **Preserve statements, signatures, and docstrings** — adjust only proof internals and updated identifiers. If a fix would require a statement change, stop and ask.
- Loop until `lake build` passes or a blocker is genuinely out of scope; then report where it's stuck.

### Phase 2 — Adopt new library APIs

Skipped when `--adopt=off`.

1. **Read every release between current and target.** For `v4.28.0 → v4.32.0`, read `v4.29.0`, `v4.30.0`, `v4.31.0`, `v4.32.0` at `https://lean-lang.org/doc/reference/latest/releases/vX.Y.Z/` (index: `.../releases/`). Scan each for **added** theorems/definitions/tactics and for **deprecations/renames**.
2. **Harvest deprecation warnings from the build** — the authoritative, mechanical "replace X with Y" signal from Lean and mathlib themselves:
   ```bash
   lake build 2>&1 | tee /tmp/bump-build.log | grep -iE "deprecated|has been renamed"
   ```
   Each `'X' has been deprecated: use 'Y' instead` names an exact replacement.
   > Note: `lean-lang.org` release notes cover Lean core and its standard library; mathlib's own changes surface primarily through these deprecation warnings and its `Mathlib/Deprecated/` history — use both signals together.
3. **Replace where the new API is a clean win** — swap a hand-rolled argument or a deprecated call for the new theorem/definition. Batch related edits, verify each batch with `lean_diagnostic_messages` (or `lake env lean <File.lean>`, run from project root), and revert any batch that adds a diagnostic or a sorry. Keep statements and docstrings intact — this is the same posture as [refactor](refactor.md).

### Phase 3 — Verify & Checkpoint

1. **Final gate:** `lake build` passes.
2. **No regressions:** sorry count did not rise (`lean4-skills-sorry-analyzer . --format=summary`) and a best-effort axiom scan is unchanged (`lean4-skills-check-axioms-inline .`).
3. **Stage only touched files** — `lean-toolchain`, the lakefile, `lake-manifest.json`, and any edited `.lean` files. Print the staged set (`git diff --cached --name-only`); never `git add -A`. Commit per `--commit` (default `ask`). Do **not** push.

## Output

```markdown
## Bump Report

**Version:** v4.28.0 → v4.32.0 (stable)
**Build:** ✓ passing
**Repairs:** 3 renamed lemmas fixed (Phase 1b)
**Adopted:** 5 deprecations resolved, 2 proofs shortened via new mathlib lemmas
**Sorries:** 4 → 4 (unchanged)   **Axioms:** standard only
**Files:** lean-toolchain, lakefile.toml, lake-manifest.json, +3 .lean

**Next steps:**
- Review the diff, then push manually: `git push`
- Deeper mathlib leverage: `/lean4:refactor --scope=changed`
```

## Safety

- **Refuses outside a Lean project** (no `lean-toolchain` + lakefile).
- Preserves theorem/lemma statements, signatures, and docstrings; introduces no axioms; must not add sorries.
- Does **not** push or open PRs — that stays manual after review.
- Recommends a clean working tree (or a pre-bump commit) so the version change is isolated and revertible via `git`.
- Release-candidate versions are adopted only with consent (`--rc`).
- Follows mathlib 100-char line width on any edited `.lean` file.

## See Also

- `/lean4:doctor` - Environment and build diagnostics (run first if `lake`/cache fails)
- `/lean4:refactor` - Leverage mathlib further once the build is green
- `/lean4:review` - Read-only quality check of the bumped code
- `/lean4:checkpoint` - Standalone build-checked save point
- [compilation-errors.md](../skills/lean4/references/compilation-errors.md) - Error-by-error repair guidance
- [Examples](../skills/lean4/references/command-examples.md#bump)

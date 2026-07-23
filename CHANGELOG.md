# Changelog

## v4.5.8 (July 2026)

Native in-place Codex plugin packaging and host adapter (Closes #157; supersedes #89). The canonical `plugins/lean4` tree is installed directly — no mirrored package or generated Codex-specific skills.

### Native Codex plugin

- Adds `.codex-plugin/plugin.json`, a thin `.agents/plugins/marketplace.json` exposing only `lean4`, and a manifest-selected `hooks/codex-hooks.json` for SessionStart, UserPromptSubmit, and advisory Bash PreToolUse handling.
- SessionStart covers `startup`, `resume`, `clear`, and `compact`. It injects the installed root and absolute wrapper paths as context; it does not claim persistent `LEAN4_*` variables or PATH mutation, which Codex does not document.
- Shared bootstrap, preflight, doctor, and prompt validation are host-aware. Claude Code keeps its existing `CLAUDE_ENV_FILE` persistence contract; native Codex uses `lean4-skills-preflight --codex` and literal absolute wrapper paths.
- Codex hooks require explicit first-run review in `/hooks`. Until trusted, the core skill remains discoverable but plugin bootstrap and guardrail behavior are unavailable. PreToolUse interception is advisory, not a security boundary.

### Validation and release hygiene

- New Bash 3.2-compatible adapter tests cover metadata, lifecycle matching, truthful bootstrap context, absolute-path preflight, Codex-shaped UserPromptSubmit payloads, and PreToolUse exit-2 blocking.
- Release-metadata Check 23 now parses and validates both Claude and Codex manifests/marketplaces and fails on Codex version drift.
- Codex Tier-3 installation, trust, verification, update, and fallback behavior are documented without claiming `/lean4:*` slash-command parity.

## v4.5.7 (July 2026)

Wrapper runtime smoke test in CI — the #152 review's explicitly deferred suggestion, converting that PR's one-off manual smoke into a permanent regression gate. The gate caught three real macOS bugs on its very first CI run; their fixes ship here too.

### Fixed (found by the new gate, on macOS runners)

- **`check_axioms_inline.sh` false success on macOS Bash 3.2** — argless runs crashed on the bare `"${POSITIONAL[@]}"` empty-array expansion (a Bash 3.2 + `set -u` quirk fixed in Bash 4.4), and the EXIT trap then overwrote the failure into **exit 0**. Now uses the `"${arr[@]+...}"` guard idiom (already used elsewhere in the same file); the same guard added to the `LEAN_FILES` loop (empty when resolved args contain no `.lean` files). Argless behavior on all platforms is now the intended "No files specified" → exit 1.
- **Disprove scripts: clean Python-version gate (all 5 entry scripts)** — on interpreters older than 3.11 (e.g. macOS's system python3, 3.9), `disprove_method_probe` died with a RuntimeError traceback (the registry gate raised instead of exiting) and `disprove_target_profile`/`_resolve` died with an import-time `TypeError` traceback (PEP 604 runtime union in `command_args/types.py`, which `from __future__ import annotations` cannot defer). Each entry script now gates before any project import: clean actionable stderr message ("set `LEAN4_PYTHON_BIN` to a Python 3.11+ interpreter") and exit 2, `TYPE_CHECKING`-guarded so mypy (`--python-version 3.10`) coverage is unaffected, mirroring `lib/disprove_methods.py`.

### CI

- **New `tests/test_wrapper_runtime.sh`** — executes all 15 `bin/lean4-skills-*` wrappers argless from a non-repository cwd under a scrubbed environment (no `LEAN4_*` vars, minimal PATH), asserting each wrapper's exact expected exit code. Two probes per wrapper: *direct* execution (kernel resolves the shebang; the exec bit is asserted and on the hook) and *bash-compat* (interpreter forced to `$BASH_FOR_COMPAT`, pinning Bash 3.2 coverage). Exit codes alone can false-green (a missing python delegate exits 2, a traceback exits 1 — both "expected" for some wrappers), so outputs matching infrastructure-failure signatures (`Traceback`, `can't open file`, `command not found`, `SyntaxError` — which parse-time errors print *without* a Traceback header — etc.) fail regardless of code. Check 28 (test_contracts.sh) only proves each wrapper's delegation *target exists*; this suite actually runs them. The expected-code table is cross-checked against `bin/` in both directions — adding a wrapper without a table entry (or vice versa) fails the suite.
- Runs on both runners: ubuntu (`wrapper-smoke` job in lint.yml) and macOS Bash 3.2 (bash3-compat.yml step).

## v4.5.6 (July 2026)

Release automation + skill license metadata. Ends the stale-release footgun: GitHub releases were cut by hand and had stalled at v4.4.10 while main shipped v4.5.5, which is why every `gh skill` command in the docs pins `@main`. No runtime changes.

### CI

- **New `release.yml` workflow** — when a version bump lands on main (push trigger scoped to `plugin.json`), creates the `vX.Y.Z` tag + GitHub release with that version's CHANGELOG section as the notes. No versioning logic of its own: the PR-time release-contract gate (below) guarantees plugin.json ↔ marketplace.json ↔ CHANGELOG consistency, so the workflow just reads the version and publishes. Idempotent (already-released versions are successful no-ops), and race-hardened: `concurrency: queue: max` serializes runs without replacing pending ones; existing-tag validation is event-sensitive (`gh release create --target` never retargets an existing tag) — a push run requires the tag to point at its own commit, while dispatch recovery accepts a tag on an earlier main commit iff it's an ancestor of head and that commit's plugin.json carries the exact version, so a correct tag from a failed publish is reusable without retargeting. Release notes are extracted from the CHANGELOG *at the commit the release attaches to* (`target_sha`), not from the checkout — so recovery can't pair an old tag with newer notes — and the release is explicitly marked `--latest`; `workflow_dispatch` covers backfill/recovery (guarded to main); `actions/checkout` is pinned to a full commit SHA with `persist-credentials: false` since the workflow holds `contents: write`.
- **New `release-contract` job in `lint.yml`** — runs the full `lint_docs.sh` and `test_contracts.sh` suites on every PR, plus the `release_notes.sh` regression suite and the release-notes extraction itself. Previously lint_docs was maintainer-run only (CI's bash3 self-tests deliberately ignore its overall exit status), so Check 23's release-metadata sync was convention rather than enforcement — and release.yml depends on it holding for every commit on main. lint.yml also declares explicit `permissions: contents: read`.
- **New `tools/release_notes.sh` + `tests/test_release_notes.sh`** — single source of truth for CHANGELOG section extraction (exactly one exact `## vX.Y.Z` heading, non-empty body), shared by `release.yml`, the release-contract job, and lint_docs Check 23 — whose previous substring grep would have accepted `## v4.5.60` as satisfying 4.5.6, and accepted an empty section. Duplicate headings for the same version are rejected rather than silently concatenated. The fixture-based self-test covers extraction shape, prefix collision, missing/malformed versions, empty sections, and duplicates.

### Skill metadata

- **`license: MIT` in SKILL.md frontmatter** — the one remaining `gh skill publish --dry-run` recommendation (the repo-root LICENSE file already existed; the Agent Skills frontmatter field didn't).

## v4.5.5 (July 2026)

Native Agent Skills metadata and multi-host installation docs (Refs #153). Every major host (Codex, Cursor, Windsurf, OpenCode, Gemini CLI / Antigravity CLI, GitHub Copilot) now discovers Agent Skills natively from `.agents/skills`, so the old per-host adapter instructions (`AGENTS.md`, `GEMINI.md`, `.cursor/rules`, oh-my-opencode) were stale. No runtime changes.

### Installation tiers (INSTALLATION.md restructure)

- **Three named tiers** replace the "Environment Bootstrap (All Hosts)" opening (which wrongly claimed every host needs the env vars): Tier 1 core-skill-only (host-native installers/copies — no helper runtime, commands, hooks, or subagent definitions), Tier 2 portable checkout + helper runtime, Tier 3 native plugin (Claude Code today; native Codex plugin tracked in #153).
- **New "Portable Checkout + Helper Runtime" section** — one clone + one `~/.agents/skills` symlink + the single canonical env block (host sections link to it; no duplicated exports), with POSIX-shell/Windows/GUI-host portability notes and update/uninstall steps.

### Host sections

- **Codex**: `$skill-installer` quick install (run in chat; `$CODEX_HOME/skills` destination caveat), `$lean4` invocation, `AGENTS.md` demoted to an optional one-line pointer, commented `codex skill add` block removed, links updated to live learn.chatgpt.com docs.
- **Gemini CLI**: `gemini skills install --path … --scope user` / `gemini skills link` replace the `GEMINI.md` instructions, with an availability note (consumer access moved to Antigravity CLI on June 18, 2026) and an Antigravity CLI subsection (global skills at `~/.gemini/antigravity-cli/skills/` — outside the portable `~/.agents/skills` link, so it gets its own Tier-2 symlink; Tier-1 via `gh skill install … --agent antigravity-cli --scope user`, gh ≥ 2.96.0).
- **Cursor / Windsurf / OpenCode**: native skills discovery paths and manual invocation (`/lean4`, `@lean4`, `skill` tool) replace project-rules and oh-my-opencode patterns.
- **New GitHub Copilot section**: `gh skill preview/install cameronfreer/lean4-skills lean4@main --agent github-copilot --scope user` (gh ≥ 2.92.0 — first version installing this plugin-directory layout flat; plain `lean4` selector — the namespaced `lean4/lean4` form is preview-only and rejected by `install`; `@main` because installs without it resolve the stale latest GitHub release).
- Root README: Codex quick-install block, portable-checkout lead, per-host one-liners, Copilot compatibility row.

### Skill metadata & standalone integrity

- **New `skills/lean4/agents/openai.yaml`** (generated via skill-creator's `generate_openai_yaml.py`): Codex UI metadata — display name, short description, `$lean4` default prompt. Guarded by new contract Check 29 (key set, quoting, 25–64-char description, `$lean4` in prompt, no redundant `policy:` block).
- **Skill directory is now link-standalone**: all 8 relative Markdown links escaping `skills/lean4/` (command docs, `lib/data/disprove_methods.toml`, lean4-contribute README) converted to canonical repository URLs labeled as live copies; the registry data file is explicitly marked absent from Tier-1 installs. A resolver pass confirms zero remaining relative escapes, so Tier-1 copies ship without broken links.

## v4.5.4 (July 2026)

Completes the wrapper migration that v4.5.3 deferred: `/lean4:disprove` was the last command whose docs invoked scripts via raw `"$LEAN4_SCRIPTS/disprove_*.py"` — the form that expands to `/disprove_*.py` with a confusing root-path error when the bootstrap env is missing (#108's original symptom). Closes #149.

### `bin/` wrappers (disprove runtime)

- 5 new self-locating executables under `plugins/lean4/bin/`, mirroring the existing wrapper template (`PLUGIN_ROOT` via `BASH_SOURCE`, delegate through `${LEAN4_PYTHON_BIN:-python3}`):
  - `lean4-skills-disprove-artifact-txn` (transactional append / drop-role / rollback — the Phase 3 hot path)
  - `lean4-skills-disprove-emit-artifact` (collision-safe non-transactional writer)
  - `lean4-skills-disprove-method-probe`, `lean4-skills-disprove-target-profile`, `lean4-skills-disprove-target-resolve` (Phase 1 profiling/resolution + method applicability)
- The Python 3.11+ requirement is unchanged — wrappers honor `LEAN4_PYTHON_BIN`, and only the registry-loading path (`disprove_method_probe.py` via `lib/disprove_methods.py`) enforces 3.11.

### Docs

- `commands/disprove.md` and `references/disprove-engine.md`: all 9 raw `$LEAN4_SCRIPTS/disprove_*.py` invocations rewritten to bare wrapper names; bare-basename mentions in the Safety sections and the Target Resolution Flow diagram aligned to the wrapper names.
- SKILL.md's curated wrapper list extended with the five disprove wrappers.

### Lint & contracts

- `test_contracts.sh` Check 26 (wrapper→doc coverage) and Check 27 (no stale `$LEAN4_SCRIPTS/<wrapped>` forms) now cover the disprove wrappers automatically — Check 27 derives its wrapper→script mapping from each wrapper's delegation line, so future raw-invocation drift in `disprove` docs fails the suite.

## v4.5.3 (July 2026)

Bootstrap now fails honestly and persists the wrapper `PATH`, plus a shared env-preflight so bootstrap and doctor agree on one recovery message. Also folds in six docs/lint/bugfix PRs that landed on `main` after v4.5.2 without their own version bumps.

### Bootstrap env honesty + shared preflight (primary, closes #108)

- **`hooks/bootstrap.sh` stops reporting false success.** It previously printed `Lean4 v4 ready` and exited 0 *unconditionally* — even when `CLAUDE_ENV_FILE` was empty so `persist_env` silently wrote nothing, so a failed bootstrap masqueraded as a good one. Now it validates its inputs, persists, re-checks that persistence took effect, and prints `ready` only on the genuine happy path; every degraded path prints a canonical recovery block to stderr instead (warn + exit 0, so a broken bootstrap doesn't disrupt session start while still being loud and actionable).
- **Bootstrap now persists `PATH`** (`export PATH="$CLAUDE_PLUGIN_ROOT/bin:$PATH"`, `:$PATH` kept literal, deduped idempotently). This makes reality match `INSTALLATION.md`'s long-standing claim that bootstrap adds `plugins/lean4/bin/` to PATH — the missing PATH export was why the self-locating `lean4-skills-*` wrappers could be off PATH after a partial bootstrap.
- **New `lib/scripts/preflight_env.sh`** — the single source of the env checks and the canonical recovery wording, with `--bootstrap` (validate a SessionStart's inputs) and `--runtime` (diagnose the live session) modes. New `bin/lean4-skills-preflight` wrapper runs it as a manual diagnostic.
- **`/lean4:doctor env`** now runs the preflight for a live diagnosis (resolved without depending on PATH — doctor is exactly where a broken PATH must stay diagnosable) and its troubleshooting rows reproduce the same three canonical recovery steps, so doctor and bootstrap can't drift.
- **Scope note:** the original issue also flagged seven commands doing raw `"$LEAN4_SCRIPTS/foo.py"` invocations; those were already migrated to self-locating wrappers in #117/#130, so this PR narrows to the still-live bootstrap/PATH truthfulness bug. Migrating `disprove.md`'s remaining raw invocations (needs new `disprove_*` wrappers) is a deferred follow-up.
- **Regression coverage:** new `tests/test_bootstrap_env.sh` and `tests/test_preflight_env.sh`, plus the previously-unwired `test_guardrails.sh` and `test_validate_user_prompt.sh` hook suites, are all now run by the `bash3-compat` CI workflow.

### Folded-in PRs (previously merged without version bumps)

Six PRs landed on `main` after the v4.5.2 release without their own CHANGELOG entries (each was scoped "no version bump" at the time). Folded in here so `git log` archeology reads cleanly:

- **#141: `docs(skill): reframe "Never" rules in SKILL.md to lead with imperative + WHY`** — reframed two free-standing `Never X` rules in SKILL.md's Core Principles / File Handling to lead with the imperative and the reasoning, per the `superpowers:writing-skills` guidance, without dropping their operational cues.
- **#142 (closes #61): `docs(insight): module docstrings must come after imports`** — documents that a module docstring (`/-! … -/`) placed before the `import` block yields the misleading `invalid 'import' command` error; adds a `mathlib-style.md § 2 Placement` subheading and a `compilation-errors.md` section + Quick Reference row.
- **#143: `chore(lint-hygiene): renumber duplicate headings, add uniqueness check, clear persistent warnings`** — fixed the pre-existing duplicate `### 9`/`### 10` headings in `compilation-errors.md`, added a `lint_docs.sh` check (8e) for duplicate `### N.` numbering, and cleared the four chronic line-length / host-agnostic lint warnings.
- **#145 (closes #132): `fix(axiom-check): resolve namespaced declarations correctly + refuse zero-coverage green verdict`** — `check_axioms_inline.sh` now walks a namespace/section stack for correct qualified names, recognizes modern Lean 4 `#print axioms` output (incl. primed names and `does not depend on any axioms`), refuses a green verdict on zero/partial coverage, and ships a 30-probe CI'd self-test.
- **#146 (closes #108-adjacent dead-code gaps): `fix(unused-decls): rg mode flagged everything unused; expand decl classes; harden zero-decls paths`** — fixed `unused_declarations.sh`'s rg extraction (a `path:` prefix flagged *every* declaration as unused), expanded the recognized decl keywords, added a zero-coverage heuristic + hard-fail without PCRE grep, and added a 10-probe CI'd self-test.
- **#147: `fix(sorry-analyzer): coverage-aware exit semantics + modifier-aware decl attribution + CI'd Python tests`** — `sorry_analyzer.py` now exits 2 on zero/partial scan coverage (not a silent clean), attributes modifier-prefixed and same-line-`sorry` declarations, and ships a 38-test unit+subprocess suite that (with `test_ordering.py`) is finally run by CI.

## v4.5.2 (June 2026)

Collab-policy redesign so the hook stops fighting Claude Code's native permission UX, plus three folded-in docs/lint hardening PRs that landed on `main` after v4.5.1 without their own version bump.

### `guardrails.sh` collab-policy refactor (primary)

- Adds a new `host` policy mode meaning "exit 0 — defer to Claude Code's native `Bash(...)` permission rule" so ordinary `git push` no longer requires the exit-2 + `LEAN4_GUARDRAILS_BYPASS=1` retry dance.
- Splits the single `LEAN4_GUARDRAILS_COLLAB_POLICY` knob into three per-op env vars: `LEAN4_GUARDRAILS_PUSH_POLICY`, `LEAN4_GUARDRAILS_AMEND_POLICY`, `LEAN4_GUARDRAILS_PR_CREATE_POLICY`. Each accepts `host` | `ask` | `allow` | `block`; default is `host`.
- **Back-compat preserved:** `LEAN4_GUARDRAILS_COLLAB_POLICY` continues to be honored as the fallback for any per-op policy that isn't explicitly set. Users who already configured `COLLAB_POLICY=allow` / `=block` / `=ask` in their settings keep the v4.5.1 semantics on the soft-gate path.
- **Push variants now tier-3 hard-blocked, non-bypassable** (matching `git reset --hard` posture): `--force` / `-f`, `--force-with-lease[=…]`, `--mirror`, `--delete` / `-d`, legacy `<remote> :<ref>` ref-delete syntax. Each emits a distinct BLOCKED message naming the variant. Per-command escape hatch: `LEAN4_GUARDRAILS_DISABLE=1 git push --force …`. `--dry-run` and `git stash push` remain exempted from all push gates.
- Recommended pairing in `.claude/settings.local.json`: `"permissions": { "ask": ["Bash(git push *)", "Bash(gh pr create *)", "Bash(git commit --amend *)"] }` — Claude Code's native "ask once, remember" UI then owns the consent, with the hook only intervening on the dangerous variants.
- See [MIGRATION.md § V4.5.1 → V4.5.2](plugins/lean4/MIGRATION.md#v451--v452) for the migration walkthrough.

### Folded-in PRs (previously merged without version bumps)

Three previously-merged PRs landed on `main` after the v4.5.1 release without their own CHANGELOG entries (each was scoped "no version bump" at the time). They're folded into v4.5.2 here so future archeology against `git log` reads cleanly:

- **#137 (closes #136): `docs(skill): teach the omit [Inst] in ordering rule + lint guard`** — the always-loaded `SKILL.md` Type Class Patterns section now teaches that `omit [Inst] in` must appear **before** the declaration docstring (placing it between docstring and `lemma`/`theorem` is a parse error). Plus a new `lint_docs.sh` Check 8a (`check_skill_omit_rule`) regression guard.
- **#138 (closes #135): `lint(docs): Check 8c — Python helpers must use ${LEAN4_PYTHON_BIN:-python3}`** — new Check 8c in `lint_docs.sh` flags bare `python3 "$LEAN4_SCRIPTS/<script>.py"` invocations and requires the `${LEAN4_PYTHON_BIN:-python3}` prefix so docs respect the operator's Python pin. Fixes 4 stale `compiler-guided-repair.md` invocations and ships `tests/test_lint_docs.sh` (a plant-in-real-tree self-test) wired into the `bash3-compat` CI workflow.
- **#139 (closes #133): `docs(style): mathlib lambda + show conventions checklist + reference sweep`** — `SKILL.md` mathlib style quick-check (use `fun x ↦` for ordinary lambdas, reserve `=>` for `match`/`do` branches and metaprogramming callbacks; prefer `show P by tac` over `show P from by tac`). New `### 9. Style Conventions Generators Often Miss` section in `mathlib-style.md` with concrete ❌/✅ worked examples. ~80-line `fun ... =>` → `↦` sweep across 11 reference files (callback/elaborator contexts intentionally left alone). Plus `lint_docs.sh` Check 8d (`check_mathlib_style_lambda_guidance`) regression guard on the always-loaded checklist surface.

## v4.5.1 (June 2026)

Adds prefixed `bin/` wrappers for model-facing scripts (closes #117). Claude Code's plugin loader appends `plugins/lean4/bin/` to the Bash tool's `PATH`, so wrappers like `lean4-skills-cycle-tracker` resolve as bare commands and become statically allowlistable as `Bash(lean4-skills-cycle-tracker:*)` — eliminating the per-invocation permission prompts that issue #117 reported on every `$LEAN4_SCRIPTS/...` call.

### `bin/` wrappers (model-facing, curated)

- 9 new executables under `plugins/lean4/bin/`, each a thin Bash wrapper resolving `PLUGIN_ROOT` via `BASH_SOURCE` and delegating to `lib/scripts/<script>`:
  - `lean4-skills-cycle-tracker` (autoprove hot path — mandatory)
  - `lean4-skills-sorry-analyzer`, `lean4-skills-find-golfable`, `lean4-skills-find-exact-candidates`, `lean4-skills-analyze-let-usage`
  - `lean4-skills-check-axioms-inline`
  - `lean4-skills-find-usages`, `lean4-skills-search-mathlib`, `lean4-skills-smart-search`
- Bootstrap hook adds `plugins/lean4/bin/` to the Bash tool's `PATH` so wrappers resolve bare; non-Claude hosts can mirror via `export PATH="$LEAN4_BIN:$PATH"` (`INSTALLATION.md` documents both).
- Internal helpers (`parse_command_args.py`, `parse_lean_errors.py`, `solver_cascade.py`, test fixtures, etc.) intentionally stay unwrapped — wrappers are a curated public surface, not a CLI for every script.

### Guardrails & lint

- `hooks/guardrails.sh`'s Lean-script stderr-suppression detector recognizes wrapper invocations in all four call forms (bare, `bin/...`, `./bin/...`, full-path).
- `tools/lint_runtime_portability.sh` Check 10 enforces shape on `bin/` contents: only `lean4-skills-*` regular executables, no symlinks, no non-prefixed files. Checks 1–8 (Bash 3.2 portability, exact shebang) extended to scan the wrappers as runtime targets.
- `tools/test_contracts.sh` Check 26 asserts every wrapper is referenced by at least one model-facing doc surface; Check 27 (new) asserts no stale `$LEAN4_SCRIPTS/<wrapped-script>` examples remain outside marked compatibility-fallback regions.
- `.github/workflows/lint.yml` extends shellcheck scope to `bin/lean4-skills-*`.

### Docs

- Model-facing references (`subagent-workflows`, `axiom-elimination`, `compiler-guided-repair`, `command-examples`, `agent-workflows`) updated to invoke wrappers directly.
- `INSTALLATION.md` rewritten to show wrapper-first usage; legacy `$LEAN4_SCRIPTS/...` form kept only for intentionally-unwrapped scripts.
- `commands/doctor.md` lists the `bin/` directory and recommends `command -v lean4-skills-*` as the wrapper-first check.

## v4.5.0 (June 2026)

Add `/lean4:disprove`, an always-interactive command for **certified counterexample search**. It reports `REFUTED` **only** when Lean typechecks a proof of the negation under `lake env lean` (no `sorry`/`admit`) with its axioms inside an explicit whitelist; otherwise `WITNESS_UNCERTIFIED` (candidate found, gate rejected) or `INCONCLUSIVE` (no candidate within budgets). New command (the 7th parameter-heavy command); existing workflows are unaffected. **Requires Python 3.11+** for the method-registry loader (`tomllib`); the rest of the plugin remains 3.10+.

### Command & engine

- `commands/disprove.md` + `skills/lean4/references/disprove-engine.md` (full engine reference, including an Implementation Status table separating deterministic / model-mediated (LSP) / deferred capabilities)
- Reuses the shared 6-phase cycle, specializing Phase 5 as **Accumulate** and Phase 1 with three dynamic, evidence-seeded menus: Step 0 Knowledge Search, Step 1 Method, Step 2 Config

### Deterministic primitives

- `disprove_target_resolve.py` (target classifier) and `disprove_target_profile.py` (deterministic profile envelope: non-authoritative grep resolution, `path_class`/`writable`, fail-fast on a missing `File.lean:LINE` target, read-only-dependency refusal; LSP/kernel fields left for the cycling LLM)
- `disprove_artifact_txn.py` — transactional append / drop-role / rollback keyed by a txn id (revert a cycle's writes as a unit), alongside the companion collision-safe `disprove_emit_artifact.py`
- `disprove_method_probe.py` — deterministic method applicability/availability filter (registry shape vs profile, prerequisite hints, solver-on-PATH advisory for `external`)
- `disprove_methods.toml` + `disprove_methods.py` registry; `cycle_tracker.sh` gains `kw-search-can` / `kw-search` budget actions

### Parser / host integration

- `command_args/specs/disprove.py` + shared `command_args/target_patterns.py`; registered in `specs/__init__.py` and the host-agnostic `UserPromptSubmit` validation (`_COVERED_COMMANDS`)

### Tests & docs

- New/updated suites for the disprove surface (`test_disprove_{emit_artifact,artifact_txn,target_resolve,target_profile,method_probe,methods,flow}`, parser specs, hook round-trip); chmod-based read-only assertions skip under root
- README (root + plugin), SKILL.md, command-examples.md, and cross-references list `disprove` (six → seven parameter-heavy commands). Validated locally with ruff, ruff format --check, and mypy --strict

## v4.4.11 (May 2026)

Three-tier git-op policy. Path-scoped `git checkout` / `git restore` operations move from absolute hard-block to a new policy-controlled soft-gate; whole-worktree and force-branch-switch destructive ops remain absolute. No new commands or workflow changes; default behavior is backward-compatible.

### Guardrail tiers (`plugins/lean4/hooks/guardrails.sh`)

- Add `LEAN4_GUARDRAILS_DESTRUCTIVE_POLICY` (`ask` default, `allow`, `block`) covering path-scoped `git checkout` / `git restore` forms — independent of the existing `LEAN4_GUARDRAILS_COLLAB_POLICY` (#131)
- `LEAN4_GUARDRAILS_BYPASS=1` one-shot prefix applies to either soft-gate category
- Whole-worktree variants (`git checkout .` / `./` / `:/` / `HEAD -- .`, `git restore .` / `--staged --worktree`, `git reset --hard`, `git clean -f`) stay absolute hard-block; pure unstaging (`git restore --staged <path>`) stays implicit-allow
- Force-branch checkout/switch (`git checkout -f|--force <branch-or-ref>`, `git switch -f|--force|--discard-changes`) hard-block; option ordering and ref shorthand (`@{-1}`, `-`, `@`, `HEAD~3`, `HEAD@{1}`) all covered
- `--pathspec-from-file=…` hard-blocks for both checkout and restore (opaque paths file the guardrail can't inspect); `--staged --pathspec-from-file=…` stays allowed
- Path-scoped soft-gate covers `<tree-ish> <path>`, `--ours` / `--theirs` / `-2` / `-3` / `--merge` / `--conflict=<style>`, `-f <path-like>`, `./<path>` / `:/<path>` / `../<path>` (incl. dotfiles), `--ignore-skip-worktree-bits` / `--no-overlay` / `--overlay` / `--recurse-submodules`, `-p` / `--patch`, all with non-destructive flag prefix/interleaving

### Tests

- `test_guardrails.sh` grows from 75 to 251 probes; new tier-boundary coverage for the forms above, including empirical temp-repo verification of which checkout/switch shapes actually discard a dirty worktree (audit posted as a PR comment)

### Docs

- `plugins/lean4/README.md` and `plugins/lean4/MIGRATION.md` document the three-tier model, the new env var, the bypass token's scope, and the path-scoped vs whole-worktree distinction

## v4.4.10 (May 2026)

Portability hardening, lint/CI infrastructure, and a broad code-quality sweep. No new commands or user-facing behavior changes.

### Portability

- Replace `#!/bin/bash` with `#!/usr/bin/env bash` in runtime scripts so the plugin works on NixOS / minimal containers where `/bin/bash` doesn't exist (#118, FernandoChu)
- Replace hardcoded `/tmp` with `$TMPDIR` in `cycle_tracker.sh` for macOS / sandboxed-runtime correctness (#112)
- Document `bash` on `PATH` as an explicit requirement (#127)

### Lint / CI infrastructure

- Add Bash 3.2 compatibility lint for macOS (#107) — later expanded and renamed to `lint_runtime_portability.sh` (this release)
- Harden shebang policy: exact `#!/usr/bin/env bash` for runtime `.sh`, exact `#!/usr/bin/env python3` for shebanged runtime `.py`, no `plugins/lean4/bin` shortcut bypassing guardrails (#121, #123)
- Parameterize self-test via `BASH_FOR_COMPAT` so it skips gracefully on `/bin/bash`-less hosts (#121)
- Add `lint` workflow with ruff (`E,F,W,B,C4,UP,SIM,I,RUF,N`), `ruff format --check`, mypy `--strict`, and shellcheck (#124, #126)
- Pin tool versions for deterministic CI: ruff 0.15.13, mypy 1.20.2, shellcheck 0.10.0 (#125, #126)
- Bump GitHub Actions to Node 24 (`checkout@v5`, `setup-python@v6`) ahead of the 2026-06-02 default switch (#126)
- Tighten `bash3-compat.yml` to hard-assert `/bin/bash` is exactly Bash 3.2 (#121)
- Rename `lint_bash_compat.sh` → `lint_runtime_portability.sh` to reflect its expanded scope (this release)

### Code cleanup

- Ruff / mypy / shellcheck sweep across `plugins/lean4/` Python and shell — type annotations, modern PEP-585/604 syntax, sorted `__all__`, quoted parameter expansions, dead-store removal, BSD-compatible `find -print0 | xargs -0` (#120, Holger Dell)
- Normalize executable-script module docstrings to BLOCK form (`"""` on its own line) for a single repo convention (#122)
- `print(__doc__)` callers use `.lstrip()` to avoid a leading blank line; `parse_command_args.py --help` now exits 0 to stdout instead of 1 to stderr (#127)
- `lint_docs.sh` always derives `PLUGIN_ROOT` from `BASH_SOURCE` (no longer false-positives a Bash 3.2 failure when the harness cache is stale) (#127)

## v4.4.9 (April 2026)

- Add shared slash-command parser and `UserPromptSubmit` hook for pre-validation of the six parameter-heavy commands (#103, #106) — Phase 3 of the command invocation fix
- Honest invocation contract + `cycle_tracker.sh` session tracker for explicit stop budgets (#105) — Phase 1–2 of the command invocation fix
- Warn about OOM from large dependent type signatures (#104)
- Fix Bash 3.2 compatibility: replace `${suffix,,}` with portable `tr` lowercase in `cycle_tracker.sh` (macOS stock bash)

## v4.4.8 (April 2026)

- Document one-concurrent-editor-per-file rule for proof agents (#64)
- Exclusive file ownership rule in canonical subagent dispatch block
- `isolation: "worktree"` recommended for background file-editing agents
- Relabel axiom checker as best-effort; surface coverage limits and mutation warning (#92)
- Warn that `lake build` progress counter `[N/M]` has a growing denominator (#84)

## v4.4.7 (March 2026)

- Use fully-qualified `mcp__lean-lsp__` tool names in agent frontmatter (#81, TheDarkchip) — may improve MCP availability in subagents on some Claude Code configurations
- Lint now enforces `mcp__lean-lsp__` prefixed MCP tool names in agent `tools:` frontmatter

## v4.4.6 (March 2026)

- Add compiler-internals and FFI-interop reference files from PR #24 content (Alok Singh)
- Subagent no-MCP hygiene: agents no longer invoke MCP tool names via Bash or write scripts/temp files to read source (#39, #90)
- Pre-flight MCP context dispatch: parent thread packs goal, diagnostics, and search results into subagent prompts (#90)
- Update subagent-workflows.md: rewrite MCP integration hierarchy, fix upstream tracking link to anthropics/claude-code#39962
- Add capability checklist and operating profiles (`full`, `mcp_main_only`, `scripts_only`, `review_only`) to SKILL.md (#72)

## v4.4.5 (March 2026)

- Promote 100-char line width rule to SKILL.md active editing contract (#58)
- Add metaprogramming line-width examples to mathlib-style.md (#58)
- Add 100-char constraint to generation/edit commands, proof-editing agents, and sorry-filling reference (#58)
- Teach review to flag unnecessary sub-100-char wrapping (#58)

## v4.4.4 (March 2026)

- Stop recommending `git stash` in guardrails and docs — commit or checkpoint first (#66)
- Add multi-branch worktree workflow guidance to subagent-workflows.md (#66)
- Fix bare-slash-link lint rule so mixed good/bad-link lines are still reported

## v4.4.3 (March 2026)

- Add per-agent MCP availability canary to all proof-editing agents (#39)
- Document upstream MCP-in-subagents limitation (anthropic/claude-code#13605)
- Recommend user-scoped lean-lsp for subagent reliability
- Soften axiom-eliminator "Generalize" → "Refactor to use" to reduce terminology drift
- Fix MCP scope labels and syntax: use `--scope user` for cross-project visibility, `--transport stdio`, `--` separator

## v4.4.2 (March 2026)

- Surface `lean_code_actions` across all skill, command, agent, and reference docs (#70)
- Tighten `lean_multi_attempt` success interpretation: empty goals alone is not proof success
- Budget `lean_run_code` in SKILL.md: isolated probes only, not a substitute for live inspection
- Make `lean_goal` explicit as first step in sorry-filling Core Workflow
- Add `lean_diagnostic_messages` → `lean_code_actions` ladder to LSP-first requirement

## v4.4.1 (March 2026)

- BREAKING: Rename proof-editing agents to drop `lean4-` prefix (#67)
  - `lean4-sorry-filler-deep` → `sorry-filler-deep`
  - `lean4-proof-repair` → `proof-repair`
  - `lean4-proof-golfer` → `proof-golfer`
  - `lean4-axiom-eliminator` → `axiom-eliminator`
  - Dispatch names change from `lean4:lean4-*` to `lean4:*`
- Fix sorry-filler-deep examples that contradicted the header-fence contract
- Add header-fence regression guard to `lint_docs.sh`
- Add agent dispatch name resolution test to `test_contracts.sh`

## v4.4.0 (March 2026)

Separates drafting from proving with a cleaner command surface. Existing invocations
continue to work; see MIGRATION.md for the full compatibility story.

- NEW `/lean4:draft`: skeleton-only drafting (default `--mode=skeleton`); `--mode=attempt` recovers old formalize proof-attempt behavior
- REWRITE `/lean4:formalize`: syntax-compatible with old formalize, but now broader — runs interactive synthesis (draft + prove); users wanting the old lighter drafting path should use `/lean4:draft`
- NEW `/lean4:autoformalize`: autonomous synthesis (draft + autoprove); preferred over `autoprove --formalize=auto`
- TIGHTENED `/lean4:prove` and `/lean4:autoprove`: declaration headers are now immutable (header fence); deep mode emits `next_action = redraft` instead of modifying statements
- DEPRECATED `autoprove --formalize=*` flags: still functional, recommend `/lean4:autoformalize`
- Cycle-engine: "Formalize Outer Loop" → "Synthesis Outer Loop"
- Router action `formalize-restage` → `redraft`; commit prefix `formalize:` → `draft:`

## v4.3.3 (March 2026)
- Align golf scripts and docs with lexicographic scoring policy (directness → inference burden → perf → length)
- `find_golfable.py`: add `benefit` field, reorder patterns to policy order, phase-ordered CLI output
- Golfer agent: fix exact-collapse acceptance rule to reference scoring order
- `proof-golfing-patterns.md`: move conditional patterns (rwa, simpa) out of High-Priority section
- `proof-golfing.md`: reorder Phase 1 search commands to policy order
- Surface `find_exact_candidates.py` as optional companion in golf.md, agent, and scripts README
- `lint_docs.sh`: add drift checks for stale "HIGHEST value" and "net decrease" language; explicit `max_lines` for all commands
- New `tests/test_ordering.py` for deterministic benefit-based sort validation
- Align agent files with official Claude Code conventions (#2f8293f)
- `/lean4:learn`: add pedagogical self-debate step to iterate loop (#43)
- `lint_docs.sh`: expand version lint to full release-metadata consistency check (#50)
- Add cold-start / fresh-worktree build-order guidance (#49)
- Replace deprecated `induction'` with structured induction syntax (#46)
- Normalize WRONG/CORRECT labels in compilation-errors.md

## v4.3.2 (March 2026)
- New [`/lean4:refactor`](plugins/lean4/commands/refactor.md) command: strategy-level proof simplification (mathlib leverage, helper extraction, congr/EqOn patterns)
- New [proof-simplification.md](plugins/lean4/skills/lean4/references/proof-simplification.md) reference guide (congr/EqOn patterns, generalization checklist, file-level audit)
- Expanded [grind-tactic.md](plugins/lean4/skills/lean4/references/grind-tactic.md): `@[grind]` attribute variants, `grind_pattern` constraint syntax, `+suggestions`/`+locals` workflow, interactive debugging loop, simproc escalation, anti-patterns (PR #19)
- Content adapted from PR #27 (Vasily Ilin) refactor command, with reference compression

## v4.3.1 (March 2026)
- New [`json-patterns`](plugins/lean4/skills/lean4/references/json-patterns.md) reference: `json%` elaboration syntax, `ToJson` derivation, `Json.mkObj` for dynamic keys, `Json.mergeObj` for skeleton+dynamic, failure modes
- Write-focused scope (no `FromJson`/parsing); linked from SKILL.md **Custom Syntax** section
- Content adapted from PR #20 (Alok Singh) standalone skill, converted to reference file

## v4.3.0 (March 2026)
- Formalize-aware outer loop for [`/lean4:autoprove`](plugins/lean4/commands/autoprove.md): opt-in `--formalize=auto|restage` wraps the inner cycle with source-backed statement acquisition and review-driven routing
- New flags: `--formalize`, `--source`, `--claim-select`, `--formalize-rigor`, `--statement-policy`, `--formalize-out`
- `--statement-policy` defaults to `rewrite-generated-only` when formalize is active (autonomous restage)
- `/lean4:review --mode=stuck` emits machine-readable `next_action` routing field
- Default behavior (`--formalize=never`) unchanged

## v4.2.0 (March 2026)
- New [`/lean4:formalize`](plugins/lean4/commands/formalize.md) command: turn informal math into Lean statements
- Split from `/lean4:learn --mode=formalize` — formalize is now a standalone command
- `/lean4:learn` refocused on interactive teaching and mathlib exploration
- `learn-pathways.md` updated to be command-agnostic (shared by learn and formalize)

## v4.1.0 (February 2026)
- New [`/lean4:learn`](plugins/lean4/commands/learn.md) command: interactive teaching, mathlib exploration, autoformalization
- Two-layer architecture: Lean-backed verification (always runs) + presentation layer (informal/supporting/formal)
- Intent classification (`--intent`), game-style tracks (`--style=game`), source handling (`--source`)
- Verification status model with `--verify=best-effort|strict`

## v4.0.9 (February 2026)
- Integrated advanced references from PR #10 (Alok Singh): grind tactic, simprocs, metaprogramming, linters, FFI, verso-docs, profiling
- All new content is reference-only, outside default prove/autoprove loop
- Lint guards for scope guards, SKILL.md cross-references, stale plugin paths, and command frontmatter

## v4.0.8 (February 2026)
- Three-tier build verification policy (diagnostics → `lake env lean` → `lake build`)
- Fixed incorrect `lake build FILE.lean` patterns across references
- Lint check prevents `lake build` with file arguments from regressing

## v4.0.7 (February 2026)
- Custom syntax reference: notations, macros, elaborators, DSLs (from PR #5, Alok Singh)
- DSL scaffold template with precedence-correct examples
- Version-compat note for MetaM/TacticM API drift across toolchains

## v4.0.5 (February 2026)
- Split `/lean4:autoprover` into `/lean4:prove` (guided) and `/lean4:autoprove` (autonomous)
- prove: asks before each cycle, startup questionnaire, interactive deep approval
- autoprove: autonomous loop with hard stop rules, structured summary on stop
- Shared cycle engine: plan → work → checkpoint → review → replan → continue/stop
- Stuck definition uses exact signature hashing for precision
- Checkpoint skips commit on empty diff

## v4.0.0 (February 2026)
- Unified into single `lean4` plugin
- New `/lean4:autoprover` - planning-first workflow
- New `/lean4:golf` - standalone proof optimization
- LSP-first approach throughout
- Safety guardrails in Lean projects (blocks push/amend/pr; one-shot bypass for collaboration ops). See [plugin README safety section](plugins/lean4/README.md#safety-guardrails).
- Removed memory integration (didn't work reliably)

## v3.4.2 (January 2026)
- Last version of 3-plugin system
- Available via `@v3.4.2-legacy` tag

## v3.4.1 (January 2026)
- Lean-lsp-mcp docs update for v0.16–v0.19
- README simplification

## v3.4.0 (January 2026)
- `/refactor-have` command for extracting/inlining have-blocks
- Agent streamlining per Anthropic best practices
- Proof golfing patterns from real-world sessions

## v3.3.1 (October 2025)
- Patch bump (`bab6f0f`)

## v3.3.0 (October 2025)
- Integration test suite and parser fixes (`f8a3898`)
- Compiler-guided proof repair (`537b53f`, `e63a5b5`, `e8814f4`)

## v3.2.0 (October 2025)
- Theorem-proving plugin manifest update (`6fcf224`)

## v3.1.0 (October 2025)
- Slash-command release and 3-plugin marketplace restructuring (`836b796`, `a7e94d5`)

## v3.0.0 (October 2025)
- Multi-skill era: lean4-theorem-proving + lean4-memories (`f5e8841`)

## v2.1.1 (October 2025)
- Fixed `check_axioms.sh` limitations, added `check_axioms_inline.sh` (`409aa0f`)

## v2.1.0 (October 2025)
- Automation scripts: `sorry_analyzer.py`, `check_axioms.sh`, `search_mathlib.sh` (`784962e`, `94a494c`)
- Scripts wired into SKILL.md workflow checklist

## v2.0.0 (October 2025)
- Progressive disclosure model: SKILL.md + references/
- Domain-specific pattern libraries (measure theory, geometry, etc.)

## v1.3.1 (October 2025)
- Search/discoverability optimization: explicit "use when…" triggers, keyword coverage, binder-order guidance (`e3dc8e5`)
- Added empirical testing docs (TESTING.md)

## v1.3.0 (October 2025)
- 33% skill compression while preserving content

## v1.2.0 (October 2025)
- Skill optimization for balance and best practices

## v1.1.0 (October 2025)
- Mathlib and local file search capabilities

## v1.0.0 (October 2025)
- Initial release: Lean 4 theorem proving skill

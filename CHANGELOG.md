# Changelog

## v4.5.0 (June 2026)

Add `/lean4:disprove`, an always-interactive command for **certified counterexample search**. It reports `FALSE` **only** when Lean typechecks a proof of the negation under `lake env lean` (no `sorry`/`admit`) with its axioms inside an explicit whitelist; otherwise `WITNESS_UNCERTIFIED` (candidate found, gate rejected) or `INCONCLUSIVE` (no candidate within budgets). New command (the 7th parameter-heavy command); existing workflows are unaffected. **Requires Python 3.11+** for the method-registry loader (`tomllib`); the rest of the plugin remains 3.10+.

### Command & engine

- `commands/disprove.md` + `skills/lean4/references/disprove-engine.md` (full engine reference, including an Implementation Status table separating deterministic / model-mediated (LSP) / deferred capabilities)
- Reuses the shared 6-phase cycle, specializing Phase 5 as **Accumulate** and Phase 1 with three dynamic, evidence-seeded menus: Step 0 Knowledge Search, Step 1 Method, Step 2 Config

### Deterministic primitives

- `disprove_target_resolve.py` (target classifier) and `disprove_target_profile.py` (deterministic profile envelope: non-authoritative grep resolution, `path_class`/`writable`, fail-fast on a missing `File.lean:LINE` target, read-only-dependency refusal; LSP/kernel fields left for the cycling LLM)
- `disprove_artifact_txn.py` — transactional append / drop-role / rollback keyed by a txn id (revert a cycle's writes as a unit), over the collision-safe `disprove_emit_artifact.py`
- `disprove_method_probe.py` — deterministic method applicability/availability filter (registry shape vs profile, prerequisite hints, solver-on-PATH advisory for `external`)
- `disprove_methods.toml` + `disprove_methods.py` registry; `cycle_tracker.sh` gains `kw-search-can` / `kw-search` budget actions

### Parser / host integration

- `command_args/specs/disprove.py` + shared `command_args/target_patterns.py`; registered in `specs/__init__.py` and the host-agnostic `UserPromptSubmit` validation (`_COVERED_COMMANDS`)

### Tests & docs

- New suites for every script (`test_disprove_{emit_artifact,artifact_txn,target_resolve,target_profile,method_probe,methods,flow}`, parser specs, hook round-trip); chmod-based read-only assertions skip under root
- README (root + plugin), SKILL.md, command-examples.md, and cross-references list `disprove` (six → seven parameter-heavy commands). All green at local CI parity (ruff, ruff format --check, mypy --strict)

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

# Changelog

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

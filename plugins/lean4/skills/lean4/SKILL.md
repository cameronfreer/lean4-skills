---
name: lean4
description: "Use when editing .lean files, debugging Lean 4 builds (type mismatch, sorry, failed to synthesize instance, axiom warnings, lake build errors), searching mathlib for lemmas, formalizing mathematics in Lean, or learning Lean 4 concepts. Also trigger when the user asks for help with Lean 4, mathlib, or lakefile. Do NOT trigger for Coq/Rocq, Agda, Isabelle, HOL4, Mizar, Idris, Megalodon, or other non-Lean theorem provers."
---

# Lean 4 Theorem Proving

Use this skill whenever you're editing Lean 4 proofs, debugging Lean builds, formalizing mathematics in Lean, or learning Lean 4 concepts. It prioritizes LSP-based inspection and mathlib search, with scripted primitives for sorry analysis, axiom checking, and error parsing.

## Core Principles

**Search before prove.** Many mathematical facts already exist in mathlib. Search exhaustively before writing tactics.

**Build incrementally.** Lean's type checker is your test suite—if it compiles with no sorries and standard axioms only, the proof is sound.

**Respect scope.** Follow the user's preference: fill one sorry, its transitive dependencies, all sorries in a file, or everything. Ask if unclear.

**Never change statements or add axioms without explicit permission.** Theorem/lemma statements, type signatures, and docstrings are off-limits unless the user requests changes. Inline comments may be adjusted; docstrings may not (they're part of the API). Custom axioms require explicit approval—if a proof seems to need one, stop and discuss.

## Commands

| Command | Purpose |
|---------|---------|
| `/lean4:formalize` | Turn informal math into Lean statements |
| `/lean4:prove` | Guided cycle-by-cycle theorem proving with explicit checkpoints |
| `/lean4:autoprove` | Autonomous multi-cycle theorem proving with hard stop rules |
| `/lean4:checkpoint` | Save progress with a safe commit checkpoint |
| `/lean4:review` | Read-only code review of Lean proofs |
| `/lean4:refactor` | Leverage mathlib, extract helpers, simplify proof strategies |
| `/lean4:golf` | Improve Lean proofs for directness, clarity, performance, and brevity |
| `/lean4:learn` | Interactive teaching and mathlib exploration |
| `/lean4:doctor` | Diagnostics, cleanup, and migration help |

### Which Command?

| Situation | Command |
|-----------|---------|
| Draft a Lean statement from an informal claim | `/lean4:formalize` |
| Filling sorries (interactive) | `/lean4:prove` |
| Filling sorries (unattended) | `/lean4:autoprove` |
| Verified save point | `/lean4:checkpoint` |
| Quality check (read-only) | `/lean4:review` |
| Simplify proof strategies (mathlib leverage, helpers) | `/lean4:refactor` |
| Optimizing compiled proofs | `/lean4:golf` |
| New to this project / exploring | `/lean4:learn --mode=repo` |
| Navigating mathlib for a topic | `/lean4:learn --mode=mathlib` |
| Something not working | `/lean4:doctor` |
| Formalize + prove end-to-end | `/lean4:autoprove --formalize=auto --source=... --claim-select=first --formalize-out=...` |

## Contributing (lean4-contribute plugin)

**If the `lean4-contribute` plugin is installed,** you may **suggest** these commands at natural stopping points. Rules:

- **Suggest first, never invoke unprompted.** Offer a one-line question; do not start the command flow.
- **Only invoke after explicit user opt-in** in the current conversation. Silence, topic change, or implicit frustration do not count as consent.
- **At most once per topic per session** unless the user engages.
- **Never mid-proof.** Wait for a natural stopping point.

| Situation | Suggest |
|-----------|---------|
| Problem appears to be in lean4-skills itself (wrong command behavior, contradictory docs, broken lint, bad guardrail, confusing plugin UX) — not ordinary Lean/mathlib/user-proof problems | "This looks like a lean4-skills bug. Want me to draft a bug report?" → `/lean4-contribute:bug-report` |
| User wants a workflow the plugin doesn't support, says a command should behave differently, or you must recommend awkward manual steps due to a missing feature | "This looks like a plugin workflow gap. Want me to draft a feature request?" → `/lean4-contribute:feature-request` |
| Result seems reusable beyond the current task: tactic-selection heuristic, mathlib search pattern, anti-pattern, documentation gap with a clear lesson — not one-off theorem facts or private repo details | "That seems reusable beyond this task. Want me to draft a shareable insight?" → `/lean4-contribute:share-insight` |

**If the plugin is not installed** and the user clearly hit a lean4-skills bug, workflow gap, or reusable insight (same criteria as above — not ordinary Lean/mathlib issues), you may offer the install hint once:

- At most once per session. Do not repeat if the user declined, ignored it, or moved on.
- Never mid-proof or during an active debugging loop.
- One short line, not a pitch: "If you want, install the `lean4-contribute` plugin and I can draft that report for you here." See the [install instructions](../../../../README.md#installation) for your host.

## Typical Workflow

```
/lean4:formalize           Turn informal math into Lean statements (optional entry)
        ↓
/lean4:prove               Guided cycle-by-cycle proving (asks before each cycle)
/lean4:autoprove           Autonomous multi-cycle proving (runs with stop rules)
        ↓
/lean4:refactor            Leverage mathlib, extract helpers (optional, or --dry-run to preview)
        ↓
/lean4:golf                Improve proofs for directness, clarity, performance, and brevity (optional)
        ↓
/lean4:checkpoint          Create verified save point
```

Use `/lean4:learn` at any point to explore repo structure or navigate mathlib. Use `/lean4:formalize` standalone or via `--formalize=auto` on autoprove for end-to-end source-to-proof.

**Notes:**
- `/lean4:prove` asks before each cycle; `/lean4:autoprove` loops autonomously with hard stop conditions
- Both trigger `/lean4:review` at configured intervals (`--review-every`)
- When reviews run (via `--review-every`), they act as gates: review → replan → continue. In prove, replan requires user approval; in autoprove, replan auto-continues
- Review supports `--mode=batch` (default) or `--mode=stuck` (triage); review is always read-only
- `--formalize=auto` on autoprove wraps formalize+prove in a single command (source → claims → skeletons → proofs)
- If you hit environment issues, run `/lean4:doctor` to diagnose

## LSP Tools (Preferred)

Sub-second feedback and search tools (LeanSearch, Loogle, LeanFinder) via Lean LSP MCP:

```
lean_goal(file, line)                           # See exact goal
lean_hover_info(file, line, col)                # Understand types
lean_local_search("keyword")                    # Fast local + mathlib (unlimited)
lean_leanfinder("goal or query")                # Semantic, goal-aware (10/30s)
lean_leansearch("natural language")             # Semantic search (3/30s)
lean_loogle("?a → ?b → _")                      # Type-pattern (unlimited if local mode)
lean_hammer_premise(file, line, col)            # Premise suggestions for simp/aesop/grind (3/30s)
lean_state_search(file, line, col)              # Goal-conditioned lemma search (3/30s)
lean_multi_attempt(file, line, snippets=[...])  # Test multiple tactics
```

## Core Primitives

| Script | Purpose | Output |
|--------|---------|--------|
| `sorry_analyzer.py` | Find sorries with context | text (default), json, markdown, summary |
| `check_axioms_inline.sh` | Check for non-standard axioms | text |
| `smart_search.sh` | Multi-source mathlib search | text |
| `find_golfable.py` | Detect optimization patterns | JSON |
| `find_usages.sh` | Find declaration usages | text |

**Usage:** Invoked by commands automatically. See [references/](references/) for details.

**Invocation contract:** Never run bare script names. Always use:
- Python: `${LEAN4_PYTHON_BIN:-python3} "$LEAN4_SCRIPTS/script.py" ...`
- Shell: `bash "$LEAN4_SCRIPTS/script.sh" ...`
- Report-only calls: add `--report-only` to `sorry_analyzer.py`, `check_axioms_inline.sh`, `unused_declarations.sh` — suppresses exit 1 on findings; real errors still exit 1. Do not use in gate commands like `/lean4:checkpoint`.
- Keep stderr visible for Lean scripts (no `/dev/null` redirection), so real errors are not hidden.

If `$LEAN4_SCRIPTS` is unset or missing, run `/lean4:doctor` and stay LSP-only until resolved.

## Automation

`/lean4:prove` and `/lean4:autoprove` handle most tasks:
- **prove** — guided, asks before each cycle. Ideal for interactive sessions.
- **autoprove** — autonomous, loops with hard stop rules. Ideal for unattended runs.

Both share the same cycle engine (plan → work → checkpoint → review → replan → continue/stop) and follow the [LSP-first protocol](references/cycle-engine.md#lsp-first-protocol): LSP tools are normative for discovery and search; script fallback only when LSP is unavailable or exhausted. Compiler-guided repair is escalation-only — not the first response to build errors. For complex proofs, they may delegate to internal workflows for deep sorry-filling (with snapshot, rollback, and scope budgets), proof repair, or axiom elimination. You don't invoke these directly.

## Skill-Only Behavior

When editing `.lean` files without invoking a command, the skill runs **one bounded pass**:
- Read the goal or error via `lean_goal`/`lean_diagnostic_messages`
- Search mathlib with up to 2 LSP tools (e.g. `lean_local_search` + `lean_leanfinder`/`lean_leansearch`/`lean_loogle`)
- Try the [Automation Tactics](#automation-tactics) cascade
- Validate with `lean_diagnostic_messages` (no project-gate `lake build` in this mode)
- No looping, no deep escalation, no multi-cycle behavior, no commits
- End with suggestions:
  > Use `/lean4:prove` for guided cycle-by-cycle help.
  > Use `/lean4:autoprove` for autonomous cycles with stop safeguards.

## Quality Gate

A proof is complete when:
- `lake build` passes
- Zero sorries in agreed scope
- Only standard axioms (`propext`, `Classical.choice`, `Quot.sound`)
- No statement changes without permission

Verification ladder: `lean_diagnostic_messages(file)` per-edit → `lake env lean <path/to/File.lean>` file gate (run from project root) → `lake build` project gate only. See [cycle-engine: Build Target Policy](references/cycle-engine.md#build-target-policy).

## Common Fixes

See [compilation-errors](references/compilation-errors.md) for error-by-error guidance (type mismatch, unknown identifier, failed to synthesize, timeout, etc.).

## Type Class Patterns

```lean
-- Local instance for this proof block
haveI : MeasurableSpace Ω := inferInstance
letI : Fintype α := ⟨...⟩

-- Scoped instances (affects current section)
open scoped Topology MeasureTheory
```

Order matters: provide outer structures before inner ones.

## Automation Tactics

Try in order (stop on first success):
`rfl` → `simp` → `ring` → `linarith` → `nlinarith` → `omega` → `exact?` → `apply?` → `grind` → `aesop`

Note: `exact?`/`apply?` query mathlib (slow). `grind` and `aesop` are powerful but may timeout. See [grind-tactic](references/grind-tactic.md) for interactive workflows, annotation strategy, and simproc escalation.

## Troubleshooting

If LSP tools aren't responding, scripts provide fallback for all operations. If environment variables (`LEAN4_SCRIPTS`, `LEAN4_REFS`) are missing, run `/lean4:doctor` to diagnose.

**Script environment check:**
```bash
echo "$LEAN4_SCRIPTS"
ls -l "$LEAN4_SCRIPTS/sorry_analyzer.py"
# One-pass discovery for troubleshooting (human-readable default text):
${LEAN4_PYTHON_BIN:-python3} "$LEAN4_SCRIPTS/sorry_analyzer.py" . --report-only
# Structured output (optional): --format=json
# Counts only (optional): --format=summary
```

**Cold start / fresh worktree:**
- Fresh worktree or after `lake clean`? Prime the cache in that worktree before the first real build.
- Use the project's cache command: `lake cache get` on newer Lake, or `lake exe cache get` where the project still uses the mathlib cache executable.
- If Lean LSP is cold or timing out on first use, run one `lake build` to bootstrap the workspace.
- After bootstrap, return to the normal verification ladder:
  `lean_diagnostic_messages(file)` → `lake env lean <path/to/File.lean>` (from project root) → `lake build` only at checkpoint/final gate.
- Do **not** symlink another worktree's `.lake/build`; use Lake cache/artifact mechanisms instead.

## References

**Cycle Engine:** [cycle-engine](references/cycle-engine.md) — shared prove/autoprove logic (stuck, deep mode, falsification, safety)

**LSP Tools:** [lean-lsp-server](references/lean-lsp-server.md) (quick start), [lean-lsp-tools-api](references/lean-lsp-tools-api.md) (full API — grep `^##` for tool names)

**Search:** [mathlib-guide](references/mathlib-guide.md) (read when searching for existing lemmas), [lean-phrasebook](references/lean-phrasebook.md) (math→Lean translations)

**Errors:** [compilation-errors](references/compilation-errors.md) (read first for any build error), [instance-pollution](references/instance-pollution.md) (typeclass conflicts — grep `## Sub-` for patterns), [compiler-guided-repair](references/compiler-guided-repair.md) (escalation-only repair — not first-pass)

**Tactics:** [tactics-reference](references/tactics-reference.md) (tactic lookup — grep `^### TacticName`), [grind-tactic](references/grind-tactic.md) (SMT-style automation — when simp can't close), [simp-reference](references/simp-reference.md) (simp hygiene + custom simprocs), [tactic-patterns](references/tactic-patterns.md), [calc-patterns](references/calc-patterns.md)

**Proof Development:** [proof-templates](references/proof-templates.md), [proof-refactoring](references/proof-refactoring.md) (28K — grep by topic), [proof-simplification](references/proof-simplification.md) (strategy-level: mathlib search, congr lemmas, helper extraction), [sorry-filling](references/sorry-filling.md)

**Optimization:** [proof-golfing](references/proof-golfing.md) (includes safety rules, bounded LSP lemma replacement, bulk rewrites, anti-patterns; escalates to axiom-eliminator), [proof-golfing-patterns](references/proof-golfing-patterns.md), [performance-optimization](references/performance-optimization.md) (grep by symptom), [profiling-workflows](references/profiling-workflows.md) (diagnose slow builds/proofs)

**Domain:** [domain-patterns](references/domain-patterns.md) (25K — grep `## Area`), [measure-theory](references/measure-theory.md) (28K), [axiom-elimination](references/axiom-elimination.md)

**Style:** [mathlib-style](references/mathlib-style.md), [verso-docs](references/verso-docs.md) (Verso doc comment roles and fixups)

**Custom Syntax:** [lean4-custom-syntax](references/lean4-custom-syntax.md) (read when building notations, macros, elaborators, or DSLs), [metaprogramming-patterns](references/metaprogramming-patterns.md) (MetaM/TacticM API — composable blocks, elaborators), [scaffold-dsl](references/scaffold-dsl.md) (copy-paste DSL template), [json-patterns](references/json-patterns.md) (json% syntax + ToJson)

**Quality:** [linter-authoring](references/linter-authoring.md) (project-specific linter rules), [ffi-patterns](references/ffi-patterns.md) (C/ObjC bindings via Lake)

**Workflows:** [agent-workflows](references/agent-workflows.md), [subagent-workflows](references/subagent-workflows.md), [command-examples](references/command-examples.md), [learn-pathways](references/learn-pathways.md) (intent taxonomy, game tracks, source handling)

**Internals:** [review-hook-schema](references/review-hook-schema.md)

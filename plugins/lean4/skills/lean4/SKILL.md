---
name: lean4
description: "Use when editing .lean files, seeing type mismatch/sorry/failed to synthesize instance/axiom warnings, lake build errors, or searching mathlib for theorem proofs."
---

# Lean 4 Theorem Proving

Use this skill whenever you're editing Lean 4 proofs or debugging Lean builds. It prioritizes LSP-based inspection and mathlib search, with scripted primitives for sorry analysis, axiom checking, and error parsing.

## Core Principles

**Search before prove.** Many mathematical facts already exist in mathlib. Search exhaustively before writing tactics.

**Build incrementally.** Lean's type checker is your test suite—if it compiles with no sorries and standard axioms only, the proof is sound.

**Respect scope.** Follow the user's preference: fill one sorry, its transitive dependencies, all sorries in a file, or everything. Ask if unclear.

**Never change statements or add axioms without explicit permission.** Theorem/lemma statements, type signatures, and docstrings are off-limits unless the user requests changes. Inline comments may be adjusted; docstrings may not (they're part of the API). Custom axioms require explicit approval—if a proof seems to need one, stop and discuss.

## Commands

| Command | Purpose |
|---------|---------|
| `/lean4:prove` | Guided cycle-by-cycle theorem proving |
| `/lean4:autoprove` | Autonomous multi-cycle proving with stop rules |
| `/lean4:checkpoint` | Verified save point (build + axiom check + commit) |
| `/lean4:review` | Quality audit (`--mode=batch` or `--mode=stuck`) |
| `/lean4:golf` | Optimize proofs for brevity |
| `/lean4:doctor` | Plugin troubleshooting and migration help |

## Typical Workflow

```
/lean4:prove               Guided cycle-by-cycle proving (asks before each cycle)
/lean4:autoprove           Autonomous multi-cycle proving (runs with stop rules)
        ↓
/lean4:golf                Optimize proofs (optional, prompted at end)
        ↓
/lean4:checkpoint          Create verified save point
```

**Notes:**
- `/lean4:prove` asks before each cycle; `/lean4:autoprove` loops autonomously with hard stop conditions
- Both trigger `/lean4:review` at configured intervals (`--review-every`)
- When reviews run (via `--review-every`), they act as gates: review → replan → approval → continue
- Review supports `--mode=batch` (default) or `--mode=stuck` (triage)
- If you hit environment issues, run `/lean4:doctor` to diagnose

## LSP Tools (Preferred)

Sub-second feedback and search tools (LeanSearch, Loogle, LeanFinder) via Lean LSP MCP:

```
lean_goal(file, line)                           # See exact goal
lean_hover_info(file, line, col)                # Understand types
lean_local_search("keyword")                    # Fast local + mathlib (unlimited)
lean_leanfinder("goal or query")                # Semantic, goal-aware (rate-limited)
lean_leansearch("natural language")             # Semantic search (rate-limited)
lean_loogle("?a → ?b → _")                      # Type-pattern (rate-limited)
lean_multi_attempt(file, line, snippets=[...])  # Test multiple tactics
```

## Core Primitives

| Script | Purpose | Output |
|--------|---------|--------|
| `sorry_analyzer.py` | Find sorries with context | JSON/text |
| `check_axioms_inline.sh` | Check for non-standard axioms | text |
| `smart_search.sh` | Multi-source mathlib search | text |
| `find_golfable.py` | Detect optimization patterns | JSON |
| `find_usages.sh` | Find declaration usages | text |

**Usage:** Invoked by commands automatically. See [references/](references/) for details.

**Invocation contract:** Never run bare script names. Always use:
- Python: `${LEAN4_PYTHON_BIN:-python3} "$LEAN4_SCRIPTS/script.py" ...`
- Shell: `bash "$LEAN4_SCRIPTS/script.sh" ...`
- Report-only calls: add `--report-only` to `sorry_analyzer.py`, `check_axioms_inline.sh`, `unused_declarations.sh` — suppresses exit 1 on findings; real errors still exit 1. Do not use in gate commands like `/lean4:checkpoint`.

If `$LEAN4_SCRIPTS` is unset or missing, run `/lean4:doctor` and stay LSP-only until resolved.

## Automation

`/lean4:prove` and `/lean4:autoprove` handle most tasks:
- **prove** — guided, asks before each cycle. Ideal for interactive sessions.
- **autoprove** — autonomous, loops with hard stop rules. Ideal for unattended runs.

Both share the same cycle engine (plan → work → checkpoint → review → replan → continue/stop) and follow the [LSP-first protocol](references/cycle-engine.md#lsp-first-protocol): LSP tools are normative for discovery and search; script fallback only when LSP is unavailable or exhausted. Compiler-guided repair is escalation-only — not the first response to build errors. For complex proofs, they may delegate to internal workflows for deep sorry-filling (with snapshot, rollback, and scope budgets), proof repair, or axiom elimination. You don't invoke these directly.

## Skill-Only Behavior

When editing `.lean` files without invoking a command, the skill runs **one bounded pass**:
- Attempt to fix the immediate issue (build error, single sorry)
- No looping, no deep escalation, no multi-cycle behavior
- End with suggestions:
  > Use `/lean4:prove` for guided cycle-by-cycle help.
  > Use `/lean4:autoprove` for autonomous cycles with stop safeguards.

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

Note: `exact?`/`apply?` query mathlib (slow). `grind` and `aesop` are powerful but may timeout.

## Troubleshooting

If LSP tools aren't responding, scripts provide fallback for all operations. If environment variables (`LEAN4_SCRIPTS`, `LEAN4_REFS`) are missing, run `/lean4:doctor` to diagnose.

**Script environment check:**
```bash
echo "$LEAN4_SCRIPTS"
ls -l "$LEAN4_SCRIPTS/sorry_analyzer.py"
${LEAN4_PYTHON_BIN:-python3} "$LEAN4_SCRIPTS/sorry_analyzer.py" . --format=summary --report-only
```

## Quality Gate

A proof is complete when:
- `lake build` passes
- Zero sorries in agreed scope
- Only standard axioms (`propext`, `Classical.choice`, `Quot.sound`)
- No statement changes without permission

Verification ladder: `lean_diagnostic_messages(file)` per-edit → `lake env lean <path/to/File.lean>` file gate (run from project root) → `lake build` project gate only. See [cycle-engine: Build Target Policy](references/cycle-engine.md#build-target-policy).

## References

**Cycle Engine:** [cycle-engine](references/cycle-engine.md) — shared prove/autoprove logic (stuck, deep mode, falsification, safety)

**LSP Tools:** [lean-lsp-server](references/lean-lsp-server.md) (quick start), [lean-lsp-tools-api](references/lean-lsp-tools-api.md) (full API — grep `^##` for tool names)

**Search:** [mathlib-guide](references/mathlib-guide.md) (read when searching for existing lemmas), [lean-phrasebook](references/lean-phrasebook.md) (math→Lean translations)

**Errors:** [compilation-errors](references/compilation-errors.md) (read first for any build error), [instance-pollution](references/instance-pollution.md) (typeclass conflicts — grep `## Sub-` for patterns), [compiler-guided-repair](references/compiler-guided-repair.md) (escalation-only repair — not first-pass)

**Tactics:** [tactics-reference](references/tactics-reference.md) (tactic lookup — grep `^### TacticName`), [grind-tactic](references/grind-tactic.md) (SMT-style automation — when simp can't close), [simproc-patterns](references/simproc-patterns.md) (custom deterministic rewrites for simp), [tactic-patterns](references/tactic-patterns.md), [calc-patterns](references/calc-patterns.md), [simp-hygiene](references/simp-hygiene.md)

**Proof Development:** [proof-templates](references/proof-templates.md), [proof-refactoring](references/proof-refactoring.md) (28K — grep by topic), [sorry-filling](references/sorry-filling.md)

**Optimization:** [proof-golfing](references/proof-golfing.md) (includes bounded LSP lemma replacement; bulk rewrites are context-filtered and regression-reverting; escalates to axiom-eliminator), [proof-golfing-patterns](references/proof-golfing-patterns.md), [proof-golfing-safety](references/proof-golfing-safety.md), [performance-optimization](references/performance-optimization.md) (grep by symptom)

**Domain:** [domain-patterns](references/domain-patterns.md) (25K — grep `## Area`), [measure-theory](references/measure-theory.md) (28K), [axiom-elimination](references/axiom-elimination.md)

**Style:** [mathlib-style](references/mathlib-style.md)

**Custom Syntax:** [lean4-custom-syntax](references/lean4-custom-syntax.md) (read when building notations, macros, elaborators, or DSLs), [scaffold-dsl](references/scaffold-dsl.md) (copy-paste DSL template)

**Workflows:** [agent-workflows](references/agent-workflows.md), [subagent-workflows](references/subagent-workflows.md), [command-examples](references/command-examples.md)

**Internals:** [review-hook-schema](references/review-hook-schema.md)

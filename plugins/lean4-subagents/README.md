# lean4-subagents (EXPERIMENTAL)

Specialized agents for batch Lean 4 proof development tasks.

## Agents

| Agent | Purpose | When to Use |
|-------|---------|-------------|
| **lean4-proof-repair** | Compiler-guided iterative proof repair | Error-driven fixing with model escalation (Haiku → Opus) |
| **lean4-sorry-filler** | Fast local sorry filling using mathlib patterns | Quick first pass on incomplete proofs |
| **lean4-sorry-filler-deep** | Strategic sorry resolution with refactoring | Complex proofs where fast pass fails |
| **lean4-axiom-eliminator** | Remove nonconstructive axioms | After checking axiom hygiene |
| **lean4-proof-golfer** | Optimize proof length/runtime | After proofs compile (30-40% reduction) |

## Requirements

- **lean4-theorem-proving plugin** (provides core workflows)
- **Optional:** lean-lsp-mcp server for parallel testing

## Usage

Agents are available via the Task tool when lean4-subagents is installed.

**Example dispatches:**
```
Dispatch lean4-proof-repair to fix errors in Probability/CondExp.lean
Dispatch lean4-sorry-filler to fill sorries in ViaL2.lean
Dispatch lean4-proof-golfer to optimize all proofs in src/
```

## Interactive vs Autonomous

**Interactive (slash commands):** Use for 1-2 proofs. Guided workflow with user decisions.

**Autonomous (agents):** Use for 10+ items. Background execution with final report.

## License

MIT License - see [LICENSE](../../LICENSE)

---

Part of [lean4-skills](../../README.md)

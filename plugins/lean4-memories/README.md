# lean4-memories (EXPERIMENTAL)

Persistent learning across Lean 4 formalization sessions.

## What You Get

Memory types that persist across sessions:
- **ProofPattern** - Successful proof strategies with tactics and confidence
- **FailedApproach** - Known dead-ends to avoid (infinite loops, timeouts)
- **ProjectConvention** - Naming conventions, proof structure preferences
- **TheoremDependency** - Helper lemmas for specific goals

All memories are automatically scoped by project path.

## Requirements

- **MCP memory server** (see setup below)
- **lean4-theorem-proving plugin** (core dependency)

## Setup

**Option A: Claude Code CLI (simplest)**
```bash
claude mcp add --transport stdio --scope user memory -- npx -y @modelcontextprotocol/server-memory
```

**Option B: Config file**

Add to `~/Library/Application Support/Claude/claude_desktop_config.json` (macOS):
```json
{
  "mcpServers": {
    "memory": {
      "command": "npx",
      "args": ["-y", "@modelcontextprotocol/server-memory"]
    }
  }
}
```

Restart Claude after configuration.

## How It Works

**Before proofs:** Queries for similar goal patterns and surfaces successful tactics

**During proofs:** Checks for known failures before major tactics

**After proofs:** Stores successful patterns (if non-trivial)

### Example

**Session 1:** Prove `measure_eq_of_fin_marginals_eq` using pi-system uniqueness (30 min exploration)
- Stores: "pi_system_uniqueness pattern works for measure equality" (confidence: 0.9)

**Session 2:** Similar goal weeks later
- Retrieves: "Try isPiSystem approach (confidence: 0.9)"
- Success in 5 minutes using remembered pattern

## Memory Helper CLI

```bash
# List all memories for current project
./scripts/memory_helper.py list

# Store a successful pattern
./scripts/memory_helper.py store-pattern \
  --goal "measure equality via finite marginals" \
  --tactics "isPiSystem,generateFrom_eq" \
  --confidence 0.9

# Store a failed approach
./scripts/memory_helper.py store-failure \
  --tactic "simp only [condExp_indicator, mul_comm]" \
  --error "infinite loop"
```

## When to Use

- Multi-session projects spanning days/weeks/months
- Repeated proof patterns requiring similar approaches
- Team projects sharing knowledge
- Avoiding previously failed approaches

## Integration

This skill complements lean4-theorem-proving:
- lean4-theorem-proving provides general workflows
- lean4-memories adds project-specific learned patterns

## License

MIT License - see [LICENSE](../../LICENSE)

---

Part of [lean4-skills](../../README.md)

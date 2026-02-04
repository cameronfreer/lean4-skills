---
name: golf
description: Optimize Lean proofs for brevity and clarity
user_invocable: true
---

# Lean4 Golf

Optimize Lean proofs that already compile. Reduce tactic count, shorten proofs, improve readability.

**Prerequisite:** Code must compile. Run `lake build` first.

## Usage

```
/lean4:golf                     # Golf entire project
/lean4:golf File.lean           # Golf specific file
/lean4:golf File.lean:42        # Golf proof at specific line
/lean4:golf --dry-run           # Show opportunities without applying
```

## Inputs

| Arg | Required | Description |
|-----|----------|-------------|
| target | No | File or file:line to golf |
| --dry-run | No | Preview only, no changes |

## Actions

1. **Verify Build** - Ensure code compiles before optimizing
2. **Find Patterns** - Detect golfable patterns:
   ```bash
   ${LEAN4_PYTHON_BIN:-python3} $LEAN4_SCRIPTS/find_golfable.py [file] --filter-false-positives
   ```
3. **Verify Safety** - Check usage before inlining:
   ```bash
   ${LEAN4_PYTHON_BIN:-python3} $LEAN4_SCRIPTS/analyze_let_usage.py [file] --line [line]
   ```
4. **Apply** - Make changes with `lake build` verification after each
5. **Report** - Show savings and saturation status

## Golfing Patterns

### Instant Wins (Always Apply)

| Before | After |
|--------|-------|
| `rw [h]; exact trivial` | `rwa [h]` |
| `ext x; rfl` | `rfl` |
| `simp; rfl` | `simp` |
| `constructor; exact h1; exact h2` | `exact ⟨h1, h2⟩` |

### Safe with Verification

| Pattern | Condition |
|---------|-----------|
| Inline let | Used ≤2 times |
| Inline have | Used once, ≤1 line |

### Skip (False Positive Risk)

- Let bindings used 3+ times
- Complex have blocks
- Named hypotheses in error messages

## Output

```markdown
## Golf Results

**Optimizations applied:** 5
**Skipped:** 2 (safety)
**Total savings:** 8 lines (~12%)
**Build status:** ✓ passing
```

## Saturation

Stop when success rate < 20% or last 3 attempts failed.

## Safety

- Requires passing build to start
- Reverts immediately on build failure
- Does not create commits (use `/lean4:checkpoint`)

## See Also

- `/lean4:review` - See opportunities (read-only)
- `/lean4:checkpoint` - Save after golfing
- [proof-golfing.md](../skills/lean4/references/proof-golfing.md)
- [Examples](../skills/lean4/references/command-examples.md#golf)

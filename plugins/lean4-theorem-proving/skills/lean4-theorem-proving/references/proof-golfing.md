# Proof Golfing: Simplifying Proofs After Compilation

**Core principle:** First make it compile, then make it clean.

**When to use:** After `lake build` succeeds on stable files. Expected 30-40% reduction with proper safety filtering.

**When NOT to use:** Active development, already-optimized code (mathlib-quality), or missing verification tools (93% false positive rate without them).

**Critical:** MUST verify let binding usage before inlining. Bindings used ≥3 times should NOT be inlined (would increase code size).

## Quick Reference Table

| Pattern | Savings | Risk | Priority | Benefit |
|---------|---------|------|----------|---------|
| Linter-guided simp cleanup | 2 lines | Zero | ⭐⭐⭐⭐⭐ | Performance |
| `by rfl` → `rfl` | 1 line | Zero | ⭐⭐⭐⭐⭐ | Directness |
| `rw; simp_rw` → `rw; simpa` | 1 line | Zero | ⭐⭐⭐⭐⭐ | Simplicity |
| Eta-reduction `fun x => f x` → `f` | Tokens | Zero | ⭐⭐⭐⭐⭐ | Simplicity |
| `.mpr` over `rwa` for trivial | 1 line | Zero | ⭐⭐⭐⭐⭐ | Directness |
| `rw; exact` → `rwa` | 50% | Zero | ⭐⭐⭐⭐⭐ | Directness |
| `ext + rfl` → `rfl` | 67% | Low | ⭐⭐⭐⭐⭐ | Directness |
| intro-dsimp-exact → lambda | 75% | Low | ⭐⭐⭐⭐⭐ | Directness |
| Extract repeated patterns to helpers | 40% | Low | ⭐⭐⭐⭐⭐ | Reusability |
| let+have+exact inline | 60-80% | HIGH | ⭐⭐⭐⭐⭐ | Conciseness |
| `by exact` → term mode | 1 line | Zero | ⭐⭐⭐⭐⭐ | Directness |
| Dot notation `.rfl`/`.symm` | Tokens | Zero | ⭐⭐⭐⭐⭐ | Conciseness |
| Inline `show` in `rw` | 50-70% | Zero | ⭐⭐⭐⭐⭐ | Conciseness |
| Transport ▸ for rewrites | 1-2 lines | Zero | ⭐⭐⭐⭐⭐ | Conciseness |
| calc → .trans chains | 2-3 lines | Low | ⭐⭐⭐⭐ | Conciseness |
| Single-use `have` inline | 30-50% | Low | ⭐⭐⭐⭐ | Clarity |
| Redundant `ext` before `simp` | 50% | Medium | ⭐⭐⭐⭐ | Simplicity |
| `congr; ext; rw` → `simp only` | 67% | Medium | ⭐⭐⭐⭐ | Simplicity |
| Multi-pattern match | 7 lines | Low | ⭐⭐⭐ | Simplicity |
| Successor pattern (n+k) | 25 lines | Low | ⭐⭐⭐ | Clarity |
| Symmetric cases with `<;>` | 11 lines | Low | ⭐⭐⭐ | Conciseness |

**ROI Strategy:** Do ⭐⭐⭐⭐⭐ first (instant wins), then ⭐⭐⭐⭐ (quick with testing), skip ⭐-⭐⭐ if time-limited.

## Essential Safety Rules

**The 93% False Positive Problem:**
- Bindings used 1-2 times: Safe to inline
- Bindings used 3-4 times: Check carefully (40% worth optimizing)
- Bindings used 5+ times: NEVER inline (would increase size 2-4×)

**Stop when:**
- ✋ Success rate < 20%
- ✋ Time per optimization > 15 minutes
- ✋ Mostly false positives

## Quick Workflow

1. **Audit:** Remove dead commented-out code (NOT helpful comments), fix linter warnings, run `lake build`
2. **Discover:** Use grep patterns to find targets (see [safety guide](proof-golfing-safety.md#phase-1-pattern-discovery-5-min))
3. **Verify:** Count binding usages before inlining
4. **Apply:** Make change → `lake build` → revert if fails
5. **Stop:** When success rate < 20% or time > 15 min per optimization

**Comments & Docstrings:**
- ✅ Remove gratuitous comments (`-- done`, `-- apply lemma`)
- ⚠️ Keep comments explaining *why* (non-obvious reasoning)
- 🚫 **NEVER modify docstrings** without explicit user approval

## Detailed References

**Pattern details:** [proof-golfing-patterns.md](proof-golfing-patterns.md) - Full explanations with examples for all patterns

**Safety & workflow:** [proof-golfing-safety.md](proof-golfing-safety.md) - False positive problem, systematic workflow, anti-patterns, benchmarks

## Related

- [tactics-reference.md](tactics-reference.md) - Tactic catalog
- [domain-patterns.md](domain-patterns.md) - Domain-specific patterns
- [mathlib-style.md](mathlib-style.md) - Style conventions

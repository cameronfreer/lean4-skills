# Proof Golfing: Simplifying Proofs After Compilation

**Core principle:** First make it compile, then make it clean.

**When to use:** After `lake build` succeeds on stable files. Expected 30-40% reduction with proper safety filtering.

**When NOT to use:** Active development, already-optimized code (mathlib-quality), or missing verification tools (93% false positive rate without them).

**Critical:** MUST verify let binding usage before inlining. Bindings used ≥3 times should NOT be inlined (would increase code size).

## Quick Reference Table

### Tier 1 — Performance (always apply)

| Pattern | Savings | Risk |
|---------|---------|------|
| Linter-guided simp cleanup | 2 lines | Zero |
| `simp` → `simp only` (non-terminal) | Perf | Zero |
| Direct lemma over automation in coercion-heavy goals | Perf | Zero |

**Terminal `simp only` caveat:** Do not narrow terminal `simp` → `simp only` or introduce new terminal `simp only` without user confirmation — some projects prefer terminal `simp` for resilience to simp-set changes (the converse of the [FlexibleLinter](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Linter/FlexibleLinter.html) concern, which flags non-`only` simp in non-terminal positions). In non-interactive mode, skip terminal `simp only` changes unless project style already uses it nearby.

### Tier 2 — Directness (always apply)

| Pattern | Savings | Risk |
|---------|---------|------|
| `by exact t` → `t` | 1 line | Zero |
| `by rfl` → `rfl` | 1 line | Zero |
| Eta-reduction `fun x => f x` → `f` | Tokens | Zero |
| `.mpr`/`.mp` over `rwa` for trivial | 1 line | Zero |
| Dot notation `.rfl`/`.symm` | Tokens | Zero |
| `apply f; exact h` → `exact f h` | 1 line | Zero |
| `ext x; rfl` → `rfl` | 67% | Low |
| `constructor; exact; exact` → `exact ⟨_, _⟩` | 2 lines | Zero |
| `simpa using h` → `exact h` when no simplification occurs | Clarity | Zero |

### Tier 3 — Structural simplification (with verification)

| Pattern | Savings | Risk |
|---------|---------|------|
| Single-use `have` inline (term < 40 chars) | 30-50% | Low |
| let+have+exact inline | 60-80% | HIGH |
| intro-dsimp-exact → lambda | 75% | Low |
| Inline `show` in `rw` | 50-70% | Zero |

### Tier 4 — Conditional (only when net score improves)

| Pattern | Savings | Risk | Condition |
|---------|---------|------|-----------|
| `rw; exact` → `rwa` | 50% | Zero | Only when `rwa` genuinely deletes boilerplate, not as default |
| `rw; simp_rw` → `rw; simpa` | 1 line | Zero | Only when it deletes surrounding boilerplate; never to replace a working `exact` |
| apply/exact chain → `exact` | 30-60% | Low | Reject if >80 chars, >2 dot-chain depth, or removes meaningful names |
| Transport ▸ for rewrites | 1-2 lines | Zero | |
| calc → .trans chains | 2-3 lines | Low | |
| Symmetric `<;>` | Lines | Low | Only for single identical tactic on literally identical goals |

**Scoring order:** Among correct candidates, prefer: (1) more direct proof shape, (2) lower inference/search burden, (3) better perf/determinism, (4) shorter code. Inference and perf are judged heuristically by the tactic complexity ladder, not by measurement. Length is still a core goal — but a tiebreaker among acceptable proofs.

**ROI Strategy:** Tier 1 and 2 first (always safe), Tier 3 with verification, Tier 4 only when the scoring order clearly favors the replacement.

**Not golf** (use `/lean4:refactor` instead): extracting repeated patterns to helpers, consolidating duplicate proof structure, API surface redesign.

## Critical Safety Warnings

### The 93% False Positive Problem

**Key finding:** Without proper analysis, 93% of "optimization opportunities" are false positives that make code WORSE.

**The Multiple-Use Heuristic:**
- Bindings used 1-2 times: Safe to inline
- Bindings used 3-4 times: 40% worth optimizing (check carefully)
- Bindings used 5+ times: NEVER inline (would increase size 2-4×)

**Example - DON'T optimize:**
```lean
let μ_map := Measure.map (fun ω i => X (k i) ω) μ  -- 20 tokens
-- Used 7 times in proof
-- Current: 20 + (2 × 7) = 34 tokens
-- Inlined: 20 × 7 = 140 tokens (4× WORSE!)
```

### When NOT to Optimize

**Skip if ANY of these:**
- ❌ Let binding used ≥3 times
- ❌ Complex proof with case analysis
- ❌ Semantic naming aids understanding
- ❌ Would create deeply nested lambdas (>2 levels)
- ❌ Readability Cost = (nesting depth) × (complexity) × (repetition) > 5

### Saturation Indicators

**Stop when:**
- ✋ Optimization success rate < 20%
- ✋ Time per optimization > 15 minutes
- ✋ Most patterns are false positives
- ✋ Debating whether 2-token savings is worth it

**Benchmark:** Well-maintained codebases reach saturation after ~20-25 optimizations.

## Systematic Workflow

### Phase 0: Pre-Optimization Audit (2 min)

Before applying patterns:
1. Remove commented code and unused lemmas
2. Fix linter warnings
3. Run `lake build` for clean baseline

This cleanup often accounts for 60%+ of available savings.

### Phase 1: Pattern Discovery (5 min)

Use systematic search, not sequential reading:

```bash
# 1. Find by-exact wrappers (directness)
grep -B 1 "exact" file.lean | grep "by$"

# 2. Find apply-exact chains (directness)
grep -A 1 "apply " file.lean | grep "exact"

# 3. Find let+have+exact (structural — verify binding usage)
grep -A 10 "let .*:=" file.lean | grep -B 8 "exact"

# 4. Find rw+exact (conditional — see rwa direction rule)
grep -A 1 "rw \[" file.lean | grep "exact"
```

**Expected:** 10-15 targets per file

### Phase 2: Safety Verification (CRITICAL)

For each let+have+exact pattern:

1. Count let binding uses (or use `$LEAN4_SCRIPTS/analyze_let_usage.py`)
2. If used ≥3 times → SKIP (false positive)
3. If used ≤2 times → Proceed with optimization

**Other patterns:** Verify compilation test will catch issues.

### Phase 2.5: Lemma Replacement Safety

When search mode is enabled, replacement candidates follow the same safety rules:
- Only accept if `lean_multi_attempt` passes
- Only accept if the replacement scores better by the lexicographic order (directness → inference burden → perf → length)
- Max one new import per replacement
- If replacement type-mismatches or needs statement changes → skip (hand off to axiom-eliminator)

### Phase 2.6: Bulk Rewrite Context Safety

**Non-equivalent contexts:** Term-wrapper rewrites (`:= by exact t` → `:= t`) are not universally equivalent in all elaboration contexts. The `by` keyword switches to tactic mode; removing it changes how Lean elaborates the term. All rewrites are still validated against baseline diagnostics and auto-reverted on regression.

**Disallowed bulk contexts:**
- `calc` blocks — step terms have specialized elaboration
- Tactic blocks — `by exact t` inside a `by` block is not the same as `t`
- Ambiguous context — when surrounding syntax makes equivalence uncertain, skip

**Nested tactic-mode boundary:** Skip candidate when the replacement TERM introduces a nested `by` (tactic-mode boundary at non-top-level position). This is a syntax/context check — the surrounding AST structure determines whether the `by` is top-level (safe to remove) or nested (unsafe). A plain regex on `by` would produce false skips on identifiers like `standby` or comments.

### Phase 3: Apply with Testing (5 min per pattern)

1. Apply optimization
2. Run `lean_diagnostic_messages(file)` (per change); `lake build` for final verification only
3. If fails: revert immediately, move to next
4. If succeeds: continue

**Strategy:** Apply 3-5 optimizations, then batch test.

### Phase 3.5: Batch Rollback Protocol

For bulk rewrites (activates automatically when ≥4 whitelisted candidates found; user confirms preview):

1. **Pre-batch snapshot** — capture file content before each batch
2. **Apply batch** — effective per-run limit: min(10 replacements/file, 3 hunks × 60 lines); overflow recomputed on next invocation — no persistent queue
3. **Validate** — run `lean_diagnostic_messages(file)` and compare: new diagnostics vs pre-batch baseline + sorry-count delta
4. **Revert on regression** — if sorry count increases or new diagnostics appear, restore from pre-batch file snapshot immediately (full batch revert, not partial)

### Phase 4: Check Saturation

After 5-10 optimizations, check indicators:
- Success rate < 20% → Stop
- Time per optimization > 15 min → Stop
- Mostly false positives → Stop

**Recommendation:** Declare victory at saturation.

## Lemma Replacement

When `--search` is enabled, the golfer performs a bounded LSP search pass before syntactic golfing:

1. Search for mathlib equivalents of custom helpers/axioms
2. Test replacements with `lean_multi_attempt`
3. Accept only if: replacement passes, scores better by the lexicographic order, and at most one new import needed

**Budgets:** `quick` = 1 search, ≤2 candidates; `full` = 2 searches, ≤3 candidates. Max 3 search calls total, ≤60s.

**Handoff:** If replacement needs statement changes or multi-file refactor → hand off to axiom-eliminator.

## Bulk Rewrite Rules

Bulk mode activates automatically when ≥4 whitelisted candidates are found in a file; the preview step is the user confirmation gate:

| Context | Allowed | Notes |
|---------|---------|-------|
| Declaration RHS (`:= by exact t`) | Yes | Whitelisted; validated with baseline + revert |
| `have` / `let` body | Yes | Same wrapper position; validated with baseline + revert |
| Inside `calc` block | No | Specialized step elaboration |
| Inside tactic block | No | `by exact t` ≠ `t` in tactic mode |
| TERM has nested tactic-mode `by` | No | Ambiguous elaboration boundary |

**Pre-apply checklist:**
1. Context check — declaration RHS, `have`, or `let` body only
2. Nested-by check — skip if TERM introduces a nested tactic-mode boundary (syntax/context check, not raw substring)
3. Symbol/signature check — verify symbol resolves in current imports, argument order matches

**Post-apply checklist:**
1. Diagnostics delta — compare vs pre-batch baseline
2. Sorry delta — no new sorries
3. Optional `lake build` — when import-sensitive edits occur (e.g., lemma replacement added an import)

## Anti-Patterns

### Semicolon Policy

Never introduce naked `;` as a golfing transform. `<;>` may be introduced only when applying a single identical tactic to literally identical goals (its intended purpose — e.g., `constructor <;> simp`); do not use it to compress non-identical branches.

When counting line savings, each `;`-separated tactic counts as its own line — semicolons do not reduce line count. If existing code uses `;` or `<;>`, do not count those lines as savings and do not target rewrites that preserve or expand semicolon usage.

```lean
-- ❌ Never introduce as a golfing transform
intro x; exact proof

-- ❌ Don't compress non-identical branches
cases h <;> (first_tactic; second_different_tactic)

-- ✅ Allowed: single identical tactic on literally identical goals
constructor <;> simp
constructor <;> rfl
```

### Don't Over-Inline

If inlining creates unreadable proof, keep intermediate steps:

```lean
-- ❌ Bad - unreadable
exact combine (obscure nested lambdas spanning 100+ chars)

-- ✅ Good - clear intent
have h1 : A := ...
have h2 : B := ...
exact combine h1 h2
```

### Don't Remove Helpful Names

```lean
-- ❌ Bad
have : ... := by ...  -- 10 lines
have : ... := by ...  -- uses first anonymous have

-- ✅ Good
have h_key_property : ... := by ...
have h_conclusion : ... := by ...  -- uses h_key_property
```

## Failed Optimizations (Learning)

### Not All `ext` Calls Are Redundant

```lean
-- Original (works)
ext x; simp [prefixCylinder]

-- Attempted (FAILS!)
simp [prefixCylinder]  -- simp alone didn't make progress
```

**Lesson:** Sometimes simp needs goal decomposed first. Always test.

### omega with Fin Coercions

```lean
-- Attempted (FAILS with counterexample!)
by omega

-- Correct (works)
Nat.add_lt_add_left hij k
```

**Lesson:** omega struggles with Fin coercions. Direct lemmas more reliable.

## Appendix

### Token Counting Quick Reference

```text
~1 token each:   let, have, exact, intro, by, fun
~2 tokens each:  :=, =>, (fun x => ...), StrictMono
~5-10 tokens:    let x : Type := definition
                 have h : Property := by proof
```

**Rule of thumb:**
- Each line ≈ 8-12 tokens
- Each have + proof ≈ 15-20 tokens
- Each inline lambda ≈ 5-8 tokens

### Saturation Metrics

**Session-by-session data:**
- Session 1-2: 60% of patterns worth optimizing
- Session 3: 20% worth optimizing
- Session 4: 6% worth optimizing (diminishing returns)

**Time efficiency:**
- First 15 optimizations: ~2 min each
- Next 7 optimizations: ~5 min each
- Last 3 optimizations: ~18 min each

**Point of diminishing returns:** Success rate < 20% and time > 15 min per optimization.

### Real-World Benchmarks

**Cumulative across sessions:**
- 23 proofs optimized
- ~108 lines removed
- ~34% token reduction average
- ~68% reduction per optimized proof
- 100% compilation success (with multi-candidate approach)

**Technique effectiveness:**
1. let+have+exact: 50% of all savings, 60-80% per instance
2. Smart ext: 50% reduction, no clarity loss
3. ext-simp chains: Saves ≥2 lines when natural
4. rwa: Conditional (only when it deletes boilerplate, not as default compression)
5. ext+rfl → rfl: High value when works

## Detailed References

**Pattern details:** [proof-golfing-patterns.md](proof-golfing-patterns.md) - Full explanations with examples for all patterns

## Related

- [tactics-reference.md](tactics-reference.md) - Tactic catalog
- [domain-patterns.md](domain-patterns.md) - Domain-specific patterns
- [mathlib-style.md](mathlib-style.md) - Style conventions

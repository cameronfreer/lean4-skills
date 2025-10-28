# Compiler-Guided Proof Repair - Quick Reference

**Core insight:** Use Lean's compiler feedback to drive iterative repair with small, budgeted LLM calls instead of blind best-of-N sampling.

**Key principle:** Generate → Compile → Diagnose → Fix → Verify (tight loop, K=1)

**Inspired by:** APOLLO (https://arxiv.org/abs/2505.05758)

---

## Quick Start

**Repair entire file:**
```
/lean4-theorem-proving:repair-file MyProof.lean
```

**Repair specific goal:**
```
/lean4-theorem-proving:repair-goal MyProof.lean 42
```

**Interactive with confirmations:**
```
/lean4-theorem-proving:repair-interactive MyProof.lean
```

---

## Core Workflow

### 1. Compile → Extract Error
```bash
lake build FILE.lean 2> errors.txt
python3 scripts/parseLeanErrors.py errors.txt > context.json
```

Extracts: error type, location, goal state, local context, code snippet

### 2. Try Solver Cascade (many simple cases, free!)
```bash
python3 scripts/solverCascade.py context.json FILE.lean
```

Tries in order: `rfl → simp → ring → linarith → nlinarith → omega → exact? → apply? → aesop`

If any succeeds → apply diff, recompile

### 3. Agent Repair (if cascade fails)

**Stage 1 (Haiku, fast):** First 6 attempts
- Model: `haiku-4.5`, thinking OFF
- Temperature: 0.2, K=1
- Budget: ~2s per attempt
- Strategy: Quick, obvious fixes

**Stage 2 (Sonnet, precise):** After Stage 1 exhausted or complex errors
- Model: `sonnet-4.5`, thinking ON
- Temperature: 0.1, K=1
- Budget: ~10s per attempt
- Strategy: Strategic thinking, global context

**Escalation triggers:**
- Same error 3 times in Stage 1
- Error types: `synth_instance`, `recursion_depth`, `timeout`
- Stage 1 attempts exhausted

### 4. Apply Patch → Recompile

```bash
git apply patch.diff
lake build FILE.lean
```

If success → done! If fail → next iteration (max 24 attempts)

---

## Repair Strategies by Error Type

### type_mismatch

**Strategies:**
1. `convert _ using N` (N = unification depth 1-3)
2. Explicit type annotation: `(expr : TargetType)`
3. `refine` with placeholders
4. `rw` to align types
5. Intermediate `have` with correct type

**Example:**
```diff
-  exact h
+  convert continuous_of_measurable h using 2
+  simp
```

### unsolved_goals

**Strategies:**
1. Try automation: `simp?`, `apply?`, `exact?`, `aesop`
2. By goal shape:
   - Equality → `rfl`, `ring`, `linarith`
   - ∀ → `intro`
   - ∃ → `use` or `refine ⟨_, _⟩`
   - → → `intro` then conclusion
3. Search mathlib for lemma
4. Break down: `constructor`, `cases`, `induction`

**Example:**
```diff
-  sorry
+  intro x
+  apply lemma_from_mathlib
+  exact h
```

### unknown_ident

**Strategies:**
1. Search mathlib: `bash .claude/tools/lean4/search_mathlib.sh "ident" name`
2. Add namespace: `open Foo` or `open scoped Bar`
3. Add import: `import Mathlib.Foo.Bar`
4. Check for typo

**Example:**
```diff
+import Mathlib.Topology.Instances.Real
 ...
-  continuous_real
+  Real.continuous
```

### synth_implicit / synth_instance

**Strategies:**
1. Provide instance: `haveI : Instance := ...`
2. Local instance: `letI : Instance := ...`
3. Open scope: `open scoped Topology`
4. Reorder arguments (instances before regular params)

**Example:**
```diff
+  haveI : MeasurableSpace β := inferInstance
   apply theorem_needing_instance
```

### sorry_present

**Strategies:**
1. Search mathlib (many already exist)
2. Automated solvers (cascade handles this)
3. Compositional proof from mathlib lemmas
4. Break into subgoals

### timeout / recursion_depth

**Strategies:**
1. Narrow `simp`: `simp only [lem1, lem2]` not `simp [*]`
2. Clear unused: `clear h1 h2`
3. Replace `decide` with `native_decide`
4. Provide instances explicitly
5. Revert then re-intro in better order

**Example:**
```diff
-  simp [*]
+  simp only [foo_lemma, bar_lemma]
```

---

## Key Success Factors

### Low Sampling Budgets
- K=1 per attempt (not K=100)
- Strong compiler feedback guides next attempt
- Efficient iteration to success

### Solver-First Strategy
- Many errors solved by automation
- Zero LLM cost for simple cases
- Only escalate to agent when needed

### Multi-Stage Escalation
- Fast model (Haiku) for most cases
- Strong model (Sonnet) only when needed
- Cost-effective repair process

### Early Stopping
- Bail after 3 identical errors
- Prevents runaway costs
- Max 24 attempts total

### Structured Logging
- Every attempt logged to `.repair/attempts.ndjson`
- Track: error hash, stage, solver success, elapsed time
- Learn successful patterns over time

---

## Expected Outcomes

Success improves over time as structured logging enables learning from repair attempts.

**Efficiency benefits:**
- Solver cascade handles many simple cases mechanically (zero LLM cost)
- Multi-stage escalation: fast model first, strong model only when needed
- Early stopping prevents runaway attempts on intractable errors
- Low sampling budget (K=1) with strong compiler feedback

**Cost optimization:**
- Solver cascade: Free (automated tactics)
- Stage 1 (Haiku): Low cost, handles most common cases
- Stage 2 (Sonnet): Higher cost, reserved for complex cases
- Much more cost-effective than blind best-of-N sampling

---

## Tools Reference

**Error parsing:**
```bash
python3 scripts/parseLeanErrors.py errors.txt
```

**Solver cascade:**
```bash
python3 scripts/solverCascade.py context.json FILE.lean
```

**Repair loop orchestrator:**
```bash
scripts/repairLoop.sh FILE.lean [max-attempts] [stage2-threshold]
```

**Slash commands:**
- `/lean4-theorem-proving:repair-file FILE.lean` - Full file repair
- `/lean4-theorem-proving:repair-goal FILE.lean LINE` - Specific goal
- `/lean4-theorem-proving:repair-interactive FILE.lean` - With confirmations

**Mathlib search:**
```bash
bash .claude/tools/lean4/search_mathlib.sh "query" [name|content]
bash .claude/tools/lean4/smart_search.sh "query" --source=all
```

---

## Common Patterns

### Pattern 1: Type Mismatch with convert

**Before:**
```lean
theorem foo (h : Measurable f) : Continuous f := by
  exact h  -- ❌ type mismatch
```

**After:**
```lean
theorem foo (h : Measurable f) : Continuous f := by
  convert continuous_of_measurable h using 2
  simp
```

### Pattern 2: Missing Instance with haveI

**Before:**
```lean
theorem bar : Property := by
  apply lemma  -- ❌ failed to synthesize instance
```

**After:**
```lean
theorem bar : Property := by
  haveI : MeasurableSpace α := inferInstance
  apply lemma
```

### Pattern 3: Unknown Identifier → Import

**Before:**
```lean
theorem baz : Result := by
  exact Continuous.comp  -- ❌ unknown identifier
```

**After:**
```lean
import Mathlib.Topology.Basic

theorem baz : Result := by
  exact Continuous.comp
```

### Pattern 4: Unsolved Goal → Automation

**Before:**
```lean
theorem qux : a + b = b + a := by
  sorry  -- ❌
```

**After:**
```lean
theorem qux : a + b = b + a := by
  ring  -- ✓ (found by solver cascade)
```

---

## Best Practices

### 1. Start with Solver Cascade
Always try automated solvers before LLM. Many cases succeed with zero cost.

### 2. Search Mathlib First
Many proofs already exist. Use search tools before generating novel proofs.

### 3. Minimal Diffs
Change only 1-5 lines. Preserve existing proof structure and style.

### 4. Trust the Loop
Don't overthink individual attempts. The loop will iterate. Fast attempts beat perfect attempts.

### 5. Learn from Logs
Review `.repair/attempts.ndjson` to see what strategies worked. Build intuition over time.

---

## Integration with lean4-memories

Repair attempts can feed into memory system:

**Store successful patterns:**
```
errorType: type_mismatch
goal: Continuous f
solution: convert continuous_of_measurable _ using 2
success: true
```

**Retrieve similar cases:**
```
When I see "Continuous" goal with "Measurable" hypothesis,
try: convert continuous_of_measurable
```

**Learn project-specific patterns:**
Track which error types are common in your codebase and which fixes work best.

---

## Troubleshooting

**Repair loop stuck on same error:**
- Check if error is truly at fault line
- Try `/repair-interactive` to see what's being attempted
- Review `.repair/attempts.ndjson` for patterns
- May need manual intervention

**Agent generates wrong fixes:**
- Stage 1 optimizes for speed → may miss context
- Escalate to Stage 2 for better understanding
- Or use `/repair-interactive` to guide manually

**Solver cascade too aggressive:**
- Some proofs need structure, not automation
- Use `/repair-goal` for focused attention
- Or fix manually and continue

**Cost concerns:**
- Solver cascade is free (use it!)
- Stage 1 (Haiku) very low cost
- Early stopping prevents runaway costs
- Much more cost-effective than blind sampling

---

*Compiler-guided repair inspired by APOLLO (https://arxiv.org/abs/2505.05758)*
*Word count: ~1100*

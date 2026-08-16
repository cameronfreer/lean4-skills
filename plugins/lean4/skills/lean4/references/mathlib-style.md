# Mathlib Style Guide for Lean 4

Quick reference for mathlib style conventions when writing Lean 4 proofs.

**Official documentation:**
- [Library Style Guidelines](https://leanprover-community.github.io/contribute/style.html)
- [Naming Conventions](https://leanprover-community.github.io/contribute/naming.html)

## Essential Rules

### 1. File Header: Copyright, `module`, Imports (CRITICAL)

Every `.lean` file starts with a copyright header, then the `module` keyword,
then grouped imports, then the module docstring, then a `public section`
opening the file's exported scope. Since mathlib's switch to the Lean module
system (2025-11-19), this is the canonical header shape:

```lean
/-
Copyright (c) YYYY Author Name. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Author Name
-/
module

public import Mathlib.Foo
public import Mathlib.Bar

import Mathlib.Baz

/-!
# Module docstring
-/

public section
```

**Key points:**
- Copyright block goes at the very top (first line)
- `module` immediately after the copyright block (no blank line), then a blank line
- Authors line has no period at the end
- Use `Authors:` even for single author
- `public import` for dependencies the file's public API needs — statements
  and type signatures are the central case, but exported instances, notation,
  syntax, and metaprogramming can also require public visibility; Lean's own
  public/private checking is authoritative over this heuristic. Plain `import`
  for implementation/proof-only dependencies. Group `public import` lines
  first, then plain `import` lines, alphabetized within each group, with a
  blank line between the two nonempty groups (omit a group rather than leave
  it empty).
- Blank line between imports and module docstring
- **Declarations in a `module` are private by default.** `public import` only
  re-exports the imported module's public scope — it does not make this file's
  declarations public. Open a `public section` after the module docstring (or
  mark individual declarations `public`) so the file actually exports its API.
  Use `@[expose] public section` only when downstream definitional unfolding
  is intentionally part of the API; plain `public section` exports signatures
  while keeping implementations opaque.

**Repo-sensitive rule:** In mathlib repos, new files use `module`, grouped
`public import` / `import`, and a module docstring. After adding or renaming
files, update generated root-import files with `lake exe mk_all`.

### 2. Module Docstrings (REQUIRED)

Every file must have a module docstring with `/-!` delimiter:

```lean
/-!
# Title of Module

Brief description of what this file does.

## Main results

- `theorem_name`: Description of what it proves
- `another_theorem`: More description

## Notation

- `|_|`: Custom notation (if any)

## References

- [Author2000] Full citation
-/
```

#### Placement

When a file has imports, the module docstring must come **after** all import lines. Plain comments such as the copyright header may precede imports, but a module docstring (`/-! ... -/`) before imports is parsed as file content, and Lean then reports the later imports as invalid. Files with no imports (rare) can place the module docstring anywhere.

```lean
-- ✗ Fails — "invalid 'import' command, it must be used in the beginning of the file":
/-! # My Module -/
import Mathlib.Data.Real.Basic

-- ✓ Works:
import Mathlib.Data.Real.Basic
/-! # My Module -/
```

The error message names `import`, not the docstring — the docstring's position is the cause. In module-system files the same ordering holds with `module` first: `module`, then the import block, then the docstring.

### 3. Naming Conventions

**Case conventions:**
- `snake_case`: Theorems, lemmas, proofs (anything returning `Prop`)
- `UpperCamelCase`: Types, structures, classes, inductive types
- `lowerCamelCase`: Functions returning non-Prop types, definitions

**When UpperCamelCase appears in snake_case names, use lowerCamelCase:**
```lean
-- ✅ GOOD
def iidProjectiveFamily    -- IID becomes iid
theorem conditionallyIID_of_exchangeable  -- IID becomes iid in snake_case

-- ❌ BAD
def IIDProjectiveFamily    -- Don't use uppercase in function names
```

**Prop-valued classes:**
- If the class is a noun: `IsProbabilityMeasure`, `IsNormal`
- If it's an adjective: `Normal` (no Is prefix needed)

**Inequality naming:**
- Use `le`/`lt` (not `ge`/`gt`) for first occurrence of ≤/<
- Use `ge`/`gt` to indicate arguments are swapped

### 4. Line Length

**Rule:** Lines should not exceed 100 characters

**Breaking strategies:**
```lean
-- Break after function parameters (before :)
theorem foo {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    [StandardBorelSpace (Ω[α])] :
    Statement := by

-- Break after :=
def longDefinition :=
    complex_expression_here

-- Break in calc chains after relation symbols
calc a = b := by proof1
  _ = c := by proof2
  _ = d := by proof3

-- Indent continuation lines by 4 spaces (or 2 for certain contexts)
```

**Metaprogramming (MetaM/TacticM) — same 100-char rule:**
```lean
-- ✓ Fits on one line (< 100 chars) — do not wrap
proof ← mkAppM ``Filter.Tendsto.prodMk_nhds #[atoms[i]!.hyp, proof]
let ty ← inferType e >>= whnf

-- ✓ Struct literals — one line when they fit
return { toExpr := e, proof? := some proof, fvarId := fvar.fvarId! }

-- ✗ Do not wrap just to reach 80 chars
proof ← mkAppM ``Filter.Tendsto.prodMk_nhds
  #[atoms[i]!.hyp, proof]  -- unnecessary break

-- ✓ Break when line truly exceeds 100 chars
let result ← withLocalDeclD `h expectedType fun fvar =>
  mkLambdaFVars #[fvar] (← mkAppM ``Eq.mpr #[proof, fvar])
```

**Check for violations:**
```bash
awk 'length > 100 {print FILENAME ":" NR ": " length($0) " chars"}' **/*.lean
```

### 5. File Names

**Rule:** Use `UpperCamelCase.lean` for all files

```lean
-- ✅ GOOD
Core.lean
DeFinetti.lean
ConditionallyIID.lean
ViaKoopman.lean

-- ❌ BAD
core.lean
de_finetti.lean
```

**Exception:** Very rare cases like `lp.lean` for ℓ^p spaces (not typical)

### 6. Tactic Mode Formatting

**Key rules:**
```lean
-- ✅ GOOD: by at end of previous line
theorem foo : Statement := by
  intro x
  cases x
  · exact h1  -- First case (focused with ·)
  · exact h2  -- Second case

-- ❌ BAD: by on its own line
theorem foo : Statement :=
  by
  intro x

-- ✅ GOOD: Focusing dot for subgoals
by
  constructor
  · -- First goal
    sorry
  · -- Second goal
    sorry

-- ⚠️ DISCOURAGED: Semicolons (prefer newlines)
by simp; ring  -- Okay but not preferred
```

**Prefer term mode for simple proofs:**
```lean
-- ✅ GOOD
theorem foo : P := proof_term

-- ⚠️ LESS GOOD
theorem foo : P := by exact proof_term
```

### 7. Calculation Proofs (calc)

**Pattern:**
```lean
calc expression
    = step1 := by justification1
  _ = step2 := by justification2
  _ ≤ step3 := by justification3
```

**Key points:**
- Align relation symbols (=, ≤, <)
- Justify each step
- Can use `by` for rewrites or direct proof terms

### 8. Implicit Parameters

**Use `{param : Type}` when:**
- Type is inferrable from other parameters
- Parameter appears in types but not needed at call site

**Use `(param : Type)` when:**
- Primary data arguments
- Parameter used in function body, not in types
- Named hypotheses/proofs
- Parameters in return types

**Example:**
```lean
-- ✅ GOOD: n inferrable from c
lemma foo {n : ℕ} {c : Fin n → ℝ} : Statement

-- ✅ GOOD: μ and X are primary subjects
theorem bar {μ : Measure Ω} (X : ℕ → Ω → α) : Statement

-- ✅ GOOD: n used in body
def baz (n : ℕ) (F : Ω[α] → ℝ) : Ω[α] → ℝ :=
  fun ω ↦ F ((shift^[n]) ω)
```

See [domain-patterns.md](domain-patterns.md) for detailed implicit parameter conversion patterns.

### 9. Style Conventions Generators Often Miss

- **Lambdas:** use `fun x ↦ ...` (`\mapsto`), not `fun x => ...`.
  Use `=>` for `match`/`do` branches and metaprogramming callback idioms.
- **Short lambdas:** consider placeholder notation (`·`) when it is clearer.
- **`show`:** prefer `show P by tac` for tactic proofs. Use
  `show P from term` only when giving a proof term — `from` in front
  of a tactic block is redundant. Examples:
  - ❌ `show P from by simp`     — anti-pattern; `from` is redundant
  - ✅ `show P by simp`           — tactic proof
  - ✅ `show P from h.symm`       — term proof (`from` introduces the term)

## Documentation Content Guidelines

### Avoid Development History References

**Don't reference "earlier drafts", "previous versions", or development history:**

```lean
-- ❌ BAD
/-- In earlier drafts, this used axioms, but now it doesn't. -/
/-- Originally defined differently, but we changed the approach. -/
/-- This replaces the old broken implementation. -/
/-- The canonical Karp theorem (sorry-free). -/
/-- Sorry-free variant of `exists_complete_stabilization`. -/

-- ✅ GOOD
/-- Uses mathlib's standard measure theory infrastructure. -/
/-- Constructs via the Koopman representation. -/
```

**"sorry-free" / "no sorry" is the most common instance of this anti-pattern.** A proof gets filled, the author annotates the docstring to celebrate, and the annotation never gets removed. Treat it like "axiom-free": timeless docs describe what a declaration *is*, not that it no longer has sorries.

**Section headers (`/-! ... -/`) get the same treatment** — they're documentation too and accumulate the same development-history language:

```lean
-- ❌ BAD
/-! ### Karp's Theorem at universe w (sorry-free)
    Both directions are now fully proved (no sorry). -/

-- ✅ GOOD
/-! ### Karp's theorem at universe `w` -/
```

**Inline comments — review triggers, not automatic-deletion rules.** During review (Rule B), *flag* development-scaffolding comments and propose replacements; do not silently delete them. Common triggers: `-- TODO`, `-- HACK`, `-- FIXME`, `-- XXX`, `-- this is temporary`, `-- old approach, keeping for reference`. A finding is advisory — the review reports it, the author decides.

**Blueprint documentation surfaces get the same Rule B treatment.** LeanArchitect `@[blueprint]` annotations carry documentation-bearing `title` / `statement` / `proof` fields (TeX), and `blueprint/src/content.tex` is a parallel documentation layer; both accumulate the same development-history language as docstrings.

```lean
-- ❌ BAD: development history in a @[blueprint] field
@[blueprint "thm:karp"
  (statement := /-- Sorry-free version of Theorem 1.2.1 of \cite{KK04}. -/)]

-- ✅ GOOD: timeless statement
@[blueprint "thm:karp"
  (statement := /-- Theorem 1.2.1 of \cite{KK04}: ... -/)]
```

During review, flag development-history wording in `@[blueprint]` fields and in `blueprint/src/content.tex` and propose timeless replacements — never auto-edit them (Rule B is read-only, in blueprint TeX exactly as in Lean docstrings).

**Document the result, not routine proof mechanics.** A declaration docstring should summarize the result-level API contract — what the statement provides to a caller. Routine tactic or proof-strategy narration belongs in inline proof comments (freely editable), not the docstring. A short proof *sketch* is appropriate when it materially helps explain a genuinely intricate argument. Avoid PR-relative history and trivially derivable specializations ("the special case `r := m + 1` gives…") that a caller can obtain directly.

**Rationale:** Comments should be timeless documentation of current state. History belongs in git commits.

### Avoid Discussing Lean `axiom` Declarations (After Proved)

Once a theorem has been proved (removing the `axiom` keyword), don't highlight that it no longer uses axioms:

```lean
-- ❌ BAD (after development complete)
/-- This construction is completely **axiom-free** and uses only standard mathlib. -/

-- ✅ GOOD
/-- This construction uses mathlib's standard measure theory infrastructure. -/
```

**Exception:** During development, documenting axiom placeholders is appropriate:
```lean
-- ✅ GOOD (during development)
/-- Key lemma for the martingale proof. For now, accepting as axiom. -/
axiom conditionallyIID_of_exchangeable : ...
```

**Note:** Discussion of *mathematical* axioms (Choice, etc.) is perfectly acceptable when mathematically relevant.

## Code Quality Checks

### Before Committing

**1. Check copyright headers:**
```bash
head -5 **/*.lean | grep -A 5 "Copyright"
```

**2. Check line lengths:**
```bash
awk 'length > 100 {print FILENAME ":" NR}' **/*.lean
```

**3. Check naming violations:**
```bash
grep -n "^theorem [A-Z]" **/*.lean  # Should be empty (use snake_case)
grep -n "^def [a-z_].*: Prop" **/*.lean  # Should be empty (Prop = theorem)
```

**4. Count sorries (should decrease over time):**
```bash
grep -c "sorry" **/*.lean
```

**5. Check for disallowed syntax:**
```bash
grep -n "\\$" **/*.lean  # Should use <|
grep -n "\\lambda" **/*.lean  # Should use fun
```

### Verify No Custom Axioms

```lean
#print axioms YourModule.main_theorem
```

Should show only standard mathlib axioms:
- `Classical.choice`
- `propext`
- `Quot.sound`

## Quick Checklist for New Files

- [ ] Copyright header at top
- [ ] `module` immediately after copyright (no blank line)
- [ ] Grouped imports after `module`: `public import` block, blank line, then plain `import` block, alphabetized
- [ ] Module docstring with `/-!` delimiter
- [ ] `public section` after the module docstring (declarations in a `module` are private by default)
- [ ] Ran `lake exe mk_all` after adding or renaming files (mathlib repos)
- [ ] Naming: `snake_case` theorems, `UpperCamelCase` types, `lowerCamelCase` functions
- [ ] Lines ≤ 100 chars
- [ ] `by` at end of line (not alone)
- [ ] Docstrings on main declarations
- [ ] No development history references
- [ ] No sorries in committed code (unless explicitly documented WIP)

## Common Formatting Examples

### Good File Structure

```lean
/-
Copyright (c) YYYY Your Name. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Your Name
-/
module

public import Mathlib.Foo

import Mathlib.Bar

/-!
# Module Title

Description of module.

## Main results

- `main_theorem`: What it proves
-/

public section

noncomputable section

open Set Function

variable {α : Type*} [MeasurableSpace α]

/-! ### Helper lemmas -/

lemma helper1 : ... := by
  ...

lemma helper2 : ... := by
  ...

/-! ### Main theorems -/

/-- Main theorem proving X. -/
theorem main_theorem : ... := by
  ...
```

## Resources

- **Official Style Guide:** https://leanprover-community.github.io/contribute/style.html
- **Naming Conventions:** https://leanprover-community.github.io/contribute/naming.html
- **How to Contribute:** https://leanprover-community.github.io/contribute/index.html
- **Mathlib Zulip:** https://leanprover.zulipchat.com/ (#mathlib4 channel)

## Related References

- [domain-patterns.md](domain-patterns.md) - Implicit parameter conversion patterns
- [proof-golfing.md](proof-golfing.md) - Simplifying proofs after compilation
- [compilation-errors.md](compilation-errors.md) - Debugging common errors

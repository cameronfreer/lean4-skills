# Compiler Internals Reference

> **Scope:** Not part of the prove/autoprove default loop. Consulted when debugging compiler behavior, tuning performance attributes, or working with compiler passes.

> **Version metadata:**
> - **Verified on:** Lean reference + release notes through `v4.27.0`
> - **Last validated:** 2026-03-28
> - **Confidence:** medium (content derived from PR #24, vetted against current docs)

## Compiler Attributes

### Decision Table

| Attribute | Use when | Safety |
|-----------|----------|--------|
| `@[csimp]` | You can prove `@f = @g` and want a compiler-only replacement | Safe (proof-backed) |
| `@[implemented_by impl]` | You need an unsafe or non-definitional implementation | **Unsafe** — no equivalence check |
| `@[inline]` | Profiling shows a hot call site benefits from inlining | Safe |
| `@[macro_inline]` | Non-recursive def needs inlining at compilation start | Safe (non-recursive only) |
| `@[noinline]` | Code-size or compile-time blowup from inlining | Safe |
| `@[never_extract]` | Closed-term extraction or CSE would suppress intended effects | Safe |

**Escalation order:** Prefer algorithmic optimization first, then inlining knobs, then `@[csimp]` with proof, and `@[implemented_by]` only as a last resort.

### `@[csimp]`

Registers a constant-replacement theorem applied during compilation:

```lean
@[csimp] theorem f_eq_g : @f = @g := by
  -- proof
```

Constraints:
- Theorem must have no parameters
- Statement must be constant replacement (`@f = @g`)
- Scoped/local registration is useful for experimentation before globalizing

### `@[implemented_by]`

Replaces a declaration's compiled implementation:

```lean
@[implemented_by fastImpl]
def slowButCorrect (n : Nat) : Nat := n * n  -- correct but slow

unsafe def fastImpl (n : Nat) : Nat := n * n  -- optimized version
```

**The compiler does not check that the implementation is equivalent to the original.** This is a trusted code boundary. Use only when `@[csimp]` cannot work (e.g., the replacement is `unsafe` or non-definitional). Keep usage rare and tested.

Constraints:
- Implementation cannot be the declaration itself
- Add runtime checks for wrapper behavior in intended call paths

### Inlining Variants

- `@[inline]` — inline when the compiler judges it worthwhile
- `@[inline_if_reduce]` — inline only if the result can be reduced further
- `@[always_inline]` — unconditional inlining
- `@[noinline]` — prevent inlining (useful for code-size or compile-time control)
- `@[macro_inline]` — inline at compilation start; **non-recursive functions only**

Start with default behavior. Add attributes only after finding measurable hot call sites. Re-check with focused tests rather than broad assumptions.

### `@[never_extract]`

Prevents closed-term extraction and common subexpression elimination. Use for declarations where extraction would suppress intended repeated effects. Keep usage narrow and document why.

## Specialization

### When to Use

- `@[specialize]` — mark declarations for specialization at call sites, useful for higher-order or instance-heavy parameters
- `@[nospecialize]` — block specialization where it causes code-size or compile-time blowup

Start without attributes unless profiling or traces justify changes.

### Parameter Targeting

Target specific parameters by name or 1-indexed position:

```lean
@[specialize f g]    -- specialize on parameters f and g
@[specialize 1 3]    -- specialize on 1st and 3rd parameters
```

Without arguments, `@[specialize]` requests default behavior (specializing `fixedHO` and `fixedInst` parameters).

### Parameter Classification

The LCNF specializer classifies parameters as:
- `fixedInst` — instance-like
- `fixedHO` — higher-order function-like
- `fixedNeutral` — computationally neutral with forward dependencies
- `user` — explicitly requested via `@[specialize ...]`
- `other` — not specialized

### Diagnostics

Enable traces to see specializer decisions:

```lean
set_option trace.Compiler.specialize.info true
set_option trace.Compiler.specialize.step true
set_option trace.Compiler.specialize.candidate true
```

Control recursion limit:

```lean
set_option compiler.maxRecSpecialize 64  -- default varies by version
```

### Common Errors

- Invalid indices (0 is invalid — indices are 1-based)
- Out-of-range or duplicated indices/names are rejected
- Recursive blowups when the specializer exceeds `compiler.maxRecSpecialize`

## Compiler Pipeline

> This section covers compiler internals useful for debugging. Most users will not need it.

### LCNF Phases

LCNF runs in three phases: `base`, `mono`, and `impure`. Use phase boundaries to localize regressions.

### Compiler Options

Confirmed options:
- `compiler.checkTypes` — type compatibility checking after each pass
- `compiler.extract_closed` — cache closed terms, evaluate at init time
- `compiler.maxRecInline` — recursion limit for `@[inline]` definitions
- `compiler.maxRecInlineIfReduce` — recursion limit for `@[inline_if_reduce]`
- `compiler.maxRecSpecialize` — recursion limit for `@[specialize]`

Adjust one option at a time and compare traces.

### Trace Classes

```lean
set_option trace.Compiler true           -- all compiler output
set_option trace.Compiler.result true    -- final LCNF results
set_option trace.compiler.ir.result true -- final IR results
```

### PassInstaller (`cpass`)

Custom compiler passes are installed via `@[cpass]` on a `PassInstaller` declaration:

```lean
@[cpass] meta def myInstaller : PassInstaller :=
  PassInstaller.installAfter .mono `simp (fun p =>
    { p with name := `myWrappedPass })
```

Available methods: `installBefore`, `installAfter`, `replacePass`, `replaceEachOccurrence`, `installAtEnd`, `installBeforeEachOccurrence`, `installAfterEach`.

Use pass `occurrence` explicitly when a target pass appears multiple times.

**Safe workflow:**
1. Capture baseline trace with no pass changes
2. Add one installer around one target pass occurrence
3. Re-run with `compiler.checkTypes` and relevant traces
4. Confirm phase invariants and pass ordering
5. Only then expand scope

## Common Failure Signatures

| Symptom | Likely cause |
|---------|-------------|
| "types do not match" on `@[implemented_by]` | Type mismatch between wrapper and implementation |
| "invalid 'csimp' theorem" | Theorem has parameters or is not constant replacement |
| Invalid `@[specialize ...]` | Index out of range, duplicated, or 0-based (must be 1-based) |
| Pipeline panic after pass change | Incorrect phase assumption in installer |
| No effect from `cpass` installer | Declaration not `meta`, attribute not global, or wrong pass name |

## See Also

- [Lean 4 Reference: Compiler](https://lean-lang.org/doc/reference/latest/) — official documentation
- [performance-optimization](performance-optimization.md) — general performance tuning

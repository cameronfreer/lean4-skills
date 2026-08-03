# Simp Reference

> **Scope:** Debugging `simp`, curating `@[simp]` lemmas, and authoring `simproc`/`dsimproc` rewrites. Not part of the prove/autoprove default loop — consulted when the simplifier is close to the proof but normalization or a reusable computed rewrite is missing.

> **Grounding:** Distilled from the Lean community posts [Simp made simple](https://leanprover-community.github.io/blog/posts/simp-made-simple/), [Fantastic Simprocs and How to Write Them](https://leanprover-community.github.io/blog/posts/simprocs-tutorial/), and [Simprocs for the Working Mathematician](https://leanprover-community.github.io/blog/posts/simprocs-for-the-working-mathematician/), plus the [Lean reference on simp normal forms](https://lean-lang.org/doc/reference/latest/The-Simplifier/Simp-Normal-Forms/).

> **Version metadata:**
> - **Verified on:** Lean `v4.32.0`
> - **Last validated:** 2026-08-03
> - **Confidence:** high (both simproc examples batch-compiled on `v4.32.0`)

Contents: [Choose the Mechanism](#choose-the-mechanism) · [Simp Normal Forms and Rewrite Policy](#simp-normal-forms-and-rewrite-policy) · [Simp Lemma Hygiene](#simp-lemma-hygiene) · [Simproc Authoring](#simproc-authoring) · [After Normalization](#after-normalization)

## Choose the Mechanism

| Situation | Mechanism |
|---|---|
| One-off directed rewrite, no normalization intent | `rw [lemma]` |
| Stable local normalization inside one proof | `simp only [...]` |
| Local rewrite where the default simp set is intentionally part of terminal closure | `simp [lemma]` |
| Default-set membership scoped to a section/file | `attribute [local simp] lemma_name` |
| Reusable named simp policy outside the default set | custom simp set via `register_simp_attr` |
| Globally preferred, stable orientation | `@[simp]` lemma |
| Canonical rewrite whose replacement is definitionally equal (commonly computed from explicit data) | `dsimproc` |
| Computed rewrite requiring proof construction or side-condition discharge beyond conditional lemmas | `simproc` |
| Symbolic term with no canonical result | leave it unchanged |
| Expression normalized but goal still open | `grind`, `omega`, `linarith`, or another domain solver — see [After Normalization](#after-normalization) |

Local-first bias: for **non-terminal** normalization, start with `simp only [...]` and promote to global `@[simp]` only after repeated successful use. Terminal `simp` calls (where closure via the default set is the intent) are less fragile and may use the full set directly.

## Simp Normal Forms and Rewrite Policy

### Two meanings of "normal form"

- A library's **global simp normal form** is determined by the **default simp set**: the shape terms settle into when `simp` runs with default lemmas and configuration.
- A particular **invocation's normal form** is relative to its explicit lemma set and configuration — `simp only [...]` defines its own, smaller notion.

In both cases, an expression is in simp normal form when the **active simplifier context** would stop rewriting it. That context is more than the lemma list: it includes active simprocs, configuration flags, congruence behavior, local hypotheses, and the discharger. "Normal form" always means "the form this setup chooses," never "the one mathematically natural form."

**Operational test:** simplify the proposed LHS using the intended set/configuration, *excluding the proposed lemma itself*. If it rewrites, the LHS is not in normal form. Then check the RHS: it must itself reach the intended normal form — "RHS is simpler" alone is not sufficient.

### Canonical versus locally useful rewrites

A rewrite is **canonical** when it moves expressions toward the representative the project wants globally: one direction clearly preferred, RHS stable under further simplification, same orientation sensible across many proofs. Typical: `x + 0 → x`, `id x → x`, expanding an abbreviation to its chosen base form.

A rewrite is **non-canonical** when it is true and locally useful but points at no globally preferred representative: both directions look equally natural, it rearranges rather than simplifies, or different proofs would want different orientations. Typical: commutativity, ad hoc reassociation, partial unfolding of a recursive definition on symbolic input.

Non-canonical rewrites belong in local `simp only [...]` calls or `rw`, not in global `@[simp]`.

### Explicit data versus symbolic inputs

A rewrite may be canonical on **explicit** inputs and non-canonical on **symbolic** ones: concrete numerals usually have a clear computed normal form; symbolic expressions often do not. The `revRange` warning from the community posts is the model case — unfolding on symbolic input produces a *true* equation that is still the *wrong* normal form.

**Evaluator-style simprocs should normally require explicit data and decline symbolic inputs** (return `.continue`). **Symbolic simprocs remain appropriate** when they implement a canonical, proof-producing structural transformation — symbolic input does not universally mean "do nothing."

### Relationship to `simpNF`

The `simpNF` lint mechanizes the **LHS half** of this discipline: it flags a proposed simp lemma whose LHS other simp lemmas can already simplify (the lemma would rarely fire, or is redundant). It does not certify the RHS — choosing the RHS as the intended destination remains design judgment, per the operational test above. A lemma that fails the lint may still be a fine **local** rewrite — it just should not usually be a global simp lemma. `@[simp, nolint simpNF]` is for the rare case where a non-normal-form orientation is deliberate and documented.

## Simp Lemma Hygiene

### First question: should this be a simp lemma?

Use a global `@[simp]` lemma only if all of the following hold:
- the rewrite is canonical, not merely convenient for one proof
- the direction is obvious and stable across the codebase
- the RHS reaches the intended normal form
- the lemma will help many proofs, not just the current one

If any fail, prefer `simp only [lemma]` locally, `simp [lemma]` in one proof, or a simproc when the rewrite depends on computation over explicit syntax.

### Common issues

**1. LHS not in normal form** — the central `simpNF` rule: do not ask the simplifier to orient terms toward a form some other simp lemma will immediately change again.

```lean
-- Bad: the default set rewrites the subterm first — `add_zero` turns
-- `f (x + 0)` into `f x` before this LHS ever gets a chance to match,
-- so the lemma rarely (if ever) fires
@[simp] lemma bad_form : f (x + 0) = g x := sorry
-- Good: state the lemma against the already-normalized LHS
@[simp] lemma good_form : f x = g x := sorry
```

**2. Potential loops** — the RHS should be in, or make progress toward, the chosen simp normal form and must not recreate an applicable cycle. This is not a literal syntax-size requirement: if the LHS reappears on the RHS (`f x = g (f x)`), simp may loop. Test in isolation: `example : f x = expected := by simp only [may_loop]` must terminate instantly.

**3. Conflicting lemmas** — two global lemmas rewriting the same LHS differently. Resolve by removing one, keeping both as ordinary lemmas chosen locally with `simp only`, or rethinking the canonical form.

### Direction and locality

Good `@[simp]` lemmas erase administrative structure — definition expansion, identity/neutral elimination, cancellation:

```lean
@[simp] lemma my_def_simp : myDef x = underlyingDef x := rfl
@[simp] lemma add_zero : x + 0 = x := sorry
```

Bad candidates introduce symmetry without a preferred orientation (commutativity; reassociation absent a deliberate normal-form policy).

When multiple simp lemmas apply, Lean selects by priority and then, at equal priority, registration recency. Overlapping specific and general rules can therefore shadow one another; inspect the active simp set rather than relying on an informal "more specific first" ordering. Before promoting to `@[simp]`, ask whether local use is enough.

### Debugging workflow

1. **`simp?`** — ask simp for its intended rewrite set. Fastest way to learn whether the problem is "missing lemma," "wrong orientation," or "too many lemmas."
2. **Minimize the active set** — `simp only [lemma1, lemma2]`, or `simp [-bad_lemma]` to exclude a suspect. If a tiny `simp only` works and default `simp` does not, the issue is almost always hygiene, not proof search.
3. **Trace** — `set_option trace.Meta.Tactic.simp true in` — only after `simp?` and `simp only` have narrowed the problem; raw traces are noisy.

### When to escalate beyond `@[simp]`

Do not fight the simplifier with dozens of narrowly targeted lemmas. Escalate to a simproc when:
- the rewrite depends on explicit computation over syntax
- you would need infinitely many numeral-specific lemmas
- the rewrite should happen only before or after children are simplified
- the required computation or proof construction cannot be expressed cleanly through ordinary **conditional simp lemmas** and the existing discharger (side conditions alone do not require a simproc)

Those are simproc problems, not more-lemma problems.

### Attributes

- `@[simp]` — standard; broad, canonical rewrites.
- `@[simp, nolint simpNF]` — suppress the normal-form lint; only when deliberate and documented.
- `@[simp high]` / `@[simp low]` — priority control; higher fires earlier.

(`simp?` is a tactic, not an attribute — see [Debugging workflow](#debugging-workflow).)

### Testing checklist

Before adding `@[simp]`:
- [ ] LHS is in simp normal form (operational test above, excluding the lemma itself)
- [ ] RHS reaches the intended normal form
- [ ] No conflicting lemma already owns this pattern
- [ ] `simp only [lemma]` terminates immediately
- [ ] The rewrite helps more than one proof
- [ ] A local `simp only [...]` call would not be enough

## Simproc Authoring

Simprocs are not "extra tactics after simp" — they participate in the simplifier's traversal. Exhaust the simpler options first: a plain `@[simp]` lemma, a local `simp only`, a conditional simp lemma with the discharger, or recognizing that the remaining work is closure (a solver's job, not a rewrite).

Good use cases from the community examples: evaluating arithmetic on explicit numerals; proving divisibility or membership facts after extracting concrete data; collapsing `ite`-shaped terms before descending into branches; replacing an infinite family of numeral-indexed lemmas with one computed rewrite.

### `dsimproc` versus `simproc`

Use `dsimproc` when the replacement is **definitionally equal** to the original — no proof term needed. Explicit-data evaluators are the common pattern, but symbolic `dsimproc`s (e.g. `whnf`-based unfolding) are valid whenever the definitional obligation holds. Use `simproc` when the replacement needs a proof witness, the simplifier's discharger for side conditions, or proposition-level reasoning. If in doubt, start with `simproc`; switch to `dsimproc` only when the definitional story is clear.

### Pre versus post procedures

Simprocs are **post-order by default**: children are simplified first, then the parent. Pre/post placement belongs to **registration or invocation** — mark a procedure as pre with `↓` (e.g. `simp only [↓myProc]`) — rather than being inherent to a bare `simproc_decl`. Use a pre-procedure when the outer form determines the rewrite and descending first would waste work: the `reduceIte` case from the community posts, where collapsing the conditional first avoids simplifying a branch about to be discarded. Where the procedure runs in the pipeline can matter as much as the rewrite itself.

### Result semantics

Returned from *inside* a procedure (these are control results, not mechanisms):
- **no match** → `.continue`
- **successful replacement that still needs simplification** → `.visit`
- **successful replacement that must not be revisited** → `.done` — a control-flow promise ("stop visiting this result"), **not** a claim that the result is in some absolute normal form
- after a successful rewrite, **if uncertain between `.visit` and `.done`, prefer `.visit`** — slower, easier to trust

Behavior differs between pre- and post-procedures: a pre-procedure's `.visit` sends the replacement through the full traversal (children included); a post-procedure's `.visit` re-simplifies the replacement after children were already processed.

### Verified examples

Both compiled on Lean v4.32.0. Explicit-data `dsimproc` (with `↓` pre-activation and symbolic decline):

```lean
import Lean
open Lean Meta Simp

def double (n : Nat) : Nat := n * 2

/-- Evaluator-style dsimproc: definitional computation on explicit data.
Declines symbolic inputs by returning `.continue`. -/
dsimproc [simp] reduceDouble (double _) := fun e => do
  let_expr double arg := e | return .continue
  let some n ← Nat.fromExpr? arg | return .continue
  return .done (mkNatLit (n * 2))

example : double 21 = 42 := by simp

-- Pre-procedure activation at the call site with ↓
example : double 21 = 42 := by simp only [↓reduceDouble]

-- Symbolic input: the simproc declines; simp needs the definition instead
example (n : Nat) : double n = n * 2 := by simp [double]
```

Proof-producing `simproc` (extracts explicit data, builds a `decide`-backed witness):

```lean
import Lean
open Lean Meta Simp

def isSmall (n : Nat) : Prop := n < 100

instance (n : Nat) : Decidable (isSmall n) :=
  inferInstanceAs (Decidable (n < 100))

/-- Proof-producing simproc: extracts explicit data, then builds a
`decide`-backed proof witness for the rewrite to `True`. -/
simproc [simp] reduceIsSmall (isSmall _) := fun e => do
  let_expr isSmall arg := e | return .continue
  let some n ← Nat.fromExpr? arg | return .continue
  unless n < 100 do return .continue
  let pf ← mkDecideProof e
  return .done { expr := mkConst ``True, proof? := ← mkEqTrue pf }

-- simp only [reduceIsSmall]: the named simproc itself must close the goal
example : isSmall 42 := by
  simp only [reduceIsSmall]

-- Symbolic input: declines, so the definition is still needed
example (n : Nat) (h : n < 100) : isSmall n := by simpa [isSmall] using h
```

Building blocks: destructure with narrow `let_expr` patterns rather than broad expression surgery; extract data with `Expr.nat?`, `Nat.fromExpr?`, `Qq`, or `Lean.toExpr`; discharge side conditions through the simplifier's discharger rather than embedding brittle proof search.

### Performance discipline

- Avoid expensive work on non-matching terms; guard on head/arity early.
- No **unbounded or general-purpose proof search** inside the body — deterministic domain computation is legitimate; hidden proof search is the long-term failure mode. Keep simprocs deterministic, boring, and cheap.
- Keep numeral-only procedures numeral-only.
- For performance-motivated or hot-path simprocs, benchmark against the lemma-only `simp only [...]` baseline: compare elaboration/build cost and proof size.
- Register locally before adding a simproc to a shared simp set.

### Simproc checklist

- [ ] The rewrite is one-way and terminating
- [ ] Inputs the procedure cannot compute on return `.continue`
- [ ] Explicit-data inputs rewrite correctly
- [ ] `.visit`/`.done` choice matches the intended traversal behavior
- [ ] The example compiles (no placeholder pseudo-Lean in `lean` fences)
- [ ] Enabled only where it helps

## After Normalization

When rewriting and normalization are complete but the goal remains open, the remaining work is closure, not simplification: switch to `grind` or a domain solver (`omega`, `linarith`, `nlinarith`). See [grind-tactic.md](grind-tactic.md) — simprocs and `grind` complement each other and should not do each other's jobs.

## See Also

- [grind-tactic.md](grind-tactic.md) - Closure after normalization; grind-specific simproc escalation conditions
- [tactics-reference.md](tactics-reference.md) - Full tactic docs including the simp deep-dive
- [performance-optimization.md](performance-optimization.md) - `simp only` for speed
- [mathlib-style.md](mathlib-style.md) - Style conventions

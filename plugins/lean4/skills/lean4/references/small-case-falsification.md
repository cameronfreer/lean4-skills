# Small-Case Falsification

> Check a conjectural statement on small instances **before** it becomes a `sorry` target.
> A false `sorry` type-checks, looks plausible and poisons every proof built on it; Lean
> cannot see the error, because there is no proof to check yet. Origin: #87.

**Contents:** [When to Run It](#when-to-run-it) ·
[How](#how) · [Handing a Witness to `/lean4:disprove`](#handing-a-witness-to-lean4disprove) ·
[Boundary](#boundary) · [Worked Cases](#worked-cases)

This is a statement-time check. It complements the preflight falsification of
`/lean4:prove` and `/lean4:autoprove`, which runs `decide` on goals that are already
decidable in Lean: here the statement is usually about objects Lean cannot enumerate
(fields, matrices, lattices, geometric configurations), but whose small instances a short
script can compute.

## When to Run It

Run it when the statement did not come verbatim from a proved source:

- a guessed intermediate lemma, a generalisation, or a local restatement of a known result;
- a claim the source itself only presumes, sketches or states in passing (sources err too:
  all three [worked cases](#worked-cases) are written claims);
- two or more consecutive `sorry` targets whose chain is not yet trusted.

It pays most when the objects are finite or have small finite instances, and when the
statement involves signs, small primes or characteristics, symmetry, counting, or an
"is a Boolean algebra / is distributive / is a group" conclusion.

Skip it for purely structural statements (type-class coherence, definitional unfolding)
and for objects with no finite approximation.

## How

1. **Write the statement as a predicate on finite data.** Separate the hypotheses from
   the conclusion: `hyp(x) -> bool`, `concl(x) -> bool`.
2. **Enumerate the smallest sizes exhaustively, then sample.** `n = 1, 2, 3, …`; primes
   `2, 3, 5`; coefficients in `[-k, k]`. Then random instances of the next sizes.
3. **Count the instances that satisfy the hypotheses.** A search in which no instance
   satisfies them has tested nothing; report the count with the result.
4. **Print each counterexample as `WITNESS: <value>`.** This is the line format the
   `external` family of `/lean4:disprove` parses
   ([disprove-engine § External family](disprove-engine.md#external-family--work-phase-execution)).

```python
import itertools, random

def hyp(x): ...      # the hypotheses, on one finite instance
def concl(x): ...    # the conclusion

def instances(n):    # every instance of size n, or a sample if there are too many
    ...

for n in range(1, 6):
    tested = 0
    for x in instances(n):
        if not hyp(x):
            continue
        tested += 1
        if not concl(x):
            print(f"WITNESS: {x!r}")
            raise SystemExit
    print(f"n={n}: {tested} instances satisfy the hypotheses, no counterexample")
```

When the small instances are expressible in core Lean, the same search can be a `Bool`
function closed by `decide +kernel`, which is already a certificate for the instance
(see the fixture `tests/fixtures/reference_snippets/falsify_first_snippets.lean`):

```lean
def concl (x : Nat) : Bool := ...
example : (List.range 10).all concl = false := by decide +kernel
```

## Handing a Witness to `/lean4:disprove`

A script's witness is a hypothesis until Lean certifies it.

1. Draft the claim as usual (the skeleton with `sorry`), then run
   `/lean4:disprove File.lean:LINE` on it.
2. In the method menu, pick the `external` family and reuse the script, or `[custom]`
   with the witness itself. The witness goes through the Per-Shape Recipes and the
   Checkpoint; `REFUTED` is reported only when the negation type-checks with the allowed
   axioms ([disprove.md § Prime Directive](../../../commands/disprove.md#prime-directive)).
3. Repair the statement (the missing hypothesis, the corrected sign) as `T_salvaged`
   ([cycle-engine § Falsification Artifacts](cycle-engine.md#falsification-artifacts)),
   and run the search again on the repaired statement before proving it.

## Boundary

- **Passing small cases is not a proof.** Record it as evidence ("no counterexample with
  `n ≤ 5`, 1,240 instances"), never as a verified claim or a reason to skip the proof.
- **Small cases can be degenerate.** In characteristic 2, `-1 = 1` and a sign error is
  invisible; a configuration with too few points may satisfy every hypothesis vacuously.
  Start from the smallest case where the suspected degeneracy is gone.
- **The search tests the predicate you wrote.** Check the predicate against one instance
  you know by hand before trusting a "no counterexample" result.

## Worked Cases

Three claims, each refuted by a search of a few seconds. The first two are checked by the
core-Lean fixture `tests/fixtures/reference_snippets/falsify_first_snippets.lean`.

### 1. A sign that `p = 2` hides

**Claim.** The trivialisations of a one-dimensional `𝔽_p`-vector space `M` (its nonzero
vectors) correspond to the `(p − 1)`-th roots of a constant `a₀ ∈ 𝔽_p`, where the
derivation gives `a₀ = ±1` without tracking the sign, and `a₀ = −1` for the simplest `M`.

**Search.** For `p = 3`: `M` has two nonzero vectors, and `y² = −1 = 2` has no solution in
`𝔽₃`. For every odd `p`, `y^{p−1} = 1` for `y ≠ 0`, so `−1` is never a `(p − 1)`-th
root. The corrected statement uses `(−1)ⁿ a₀`. Searching `p = 2` alone finds nothing.

### 2. A classification of line arrangements with a missing type

**Claim.** An arrangement of lines in the projective plane that is not covered by two
pencils (no two intersection points through which every line passes) and has no five
lines in general position is either the complete quadrangle (six lines, four triple
points) or a particular arrangement of seven lines.

**Search.** Lines are integer triples `(u₀, u₁, u₂)`, and three lines are concurrent iff
the 3 × 3 determinant of their triples vanishes, so every hypothesis is a finite
computation. Draw six random lines with coefficients in `[-3, 3]`: in ten seeded runs, the
first draw that satisfies both hypotheses (after 5 to 582 draws) is already a
counterexample, with three triple points. A tidy one: the sides of the triangle
`(0, 0), (1, 0), (0, 1)` and the lines `y = 2x`, `y = 3x − 3`, `y = 5x + 1`, one through each
vertex. It satisfies both hypotheses, and has three triple points and six lines.

### 3. A closure lattice presumed Boolean

**Claim.** For a symmetric relation `⊥` on a finite set `X`, with
`S^⊥ = {x | x ⊥ s for all s ∈ S}`, the sets with `S = S^⊥⊥` form a Boolean algebra.

**Search.** Enumerate the irreflexive symmetric relations on `n ≤ 4` points and test
distributivity of the closed sets (meet `∩`, join `(S ∪ T)^⊥⊥`). Nothing fails for
`n ≤ 3`. For `n = 4` and `0 ⊥ 3`, `1 ⊥ 2`, the closed sets are `∅`, the four singletons
and `X`: `{2} ∧ ({3} ∨ {1}) = {2}`, while `({2} ∧ {3}) ∨ ({2} ∧ {1}) = ∅`. What does hold
in general is weaker: the closed sets form a complete ortholattice. When the relation is
constrained by further structure, the same exhaustive search runs over the structured
objects. In the setting this claim came from, the smallest counterexample had seven points
and a six-element non-distributive lattice.

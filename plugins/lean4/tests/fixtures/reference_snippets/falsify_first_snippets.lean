/-!
Core-Lean evidence (no Mathlib) for worked cases 1 and 2 of
`skills/lean4/references/small-case-falsification.md` (#87). Run by the
`lean-integration` workflow through `run_core_snippets.sh`, with the `lean_file_gate`
fixture's pinned toolchain:

    cd plugins/lean4/tests/fixtures/lean_file_gate
    lean ../reference_snippets/falsify_first_snippets.lean

Each search is a `Bool` function on finite data, closed by `decide +kernel`: the check a
small-case script runs, done by the kernel, so the counterexample is certified.
-/

/-! ### Case 1 — a sign that `p = 2` hides -/

/-- The `(p - 1)`-th roots of `a` modulo `p`, by enumeration. -/
def rootsMod (p a : Nat) : List Nat :=
  (List.range p).filter fun y => y ^ (p - 1) % p == a % p

-- `−1 = 2` has no square root modulo 3 …
example : rootsMod 3 2 = [] := by decide +kernel

-- … while a one-dimensional `𝔽₃`-vector space has two nonzero vectors.
example : ((List.range 3).filter (· != 0)).length = 2 := by decide +kernel

-- In characteristic 2 the sign is invisible: `−1 = 1` is a root.
example : rootsMod 2 1 = [1] := by decide +kernel

/-! ### Case 2 — a classification of line arrangements with a missing type -/

/-- A line `u₀x + u₁y + u₂z = 0` of the projective plane, as its integer triple. -/
abbrev Line := Int × Int × Int

/-- The determinant of three triples: it vanishes iff the three lines are concurrent. -/
def det3 (u v w : Line) : Int :=
  u.1 * (v.2.1 * w.2.2 - v.2.2 * w.2.1) - u.2.1 * (v.1 * w.2.2 - v.2.2 * w.1) +
    u.2.2 * (v.1 * w.2.1 - v.2.1 * w.1)

/-- The sides `AB`, `BC`, `CA` of the triangle `(0, 0)`, `(1, 0)`, `(0, 1)`, and the lines
`y = 2x`, `y = 3x − 3`, `y = 5x + 1`, one through each vertex. -/
def six : List Line :=
  [(0, 1, 0), (1, 1, -1), (1, 0, 0), (2, -1, 0), (3, -1, -3), (5, -1, 1)]

def concurrent (L : List Line) (i j k : Nat) : Bool :=
  det3 (L.getD i (0, 0, 0)) (L.getD j (0, 0, 0)) (L.getD k (0, 0, 0)) == 0

/-- The concurrent triples `i < j < k`: the triple points of the arrangement. -/
def triplePoints (L : List Line) : List (Nat × Nat × Nat) :=
  (List.range L.length).flatMap fun i =>
    (List.range L.length).flatMap fun j =>
      (List.range L.length).filterMap fun k =>
        if decide (i < j) && decide (j < k) && concurrent L i j k then some (i, j, k) else none

/-- The intersection points, as the pairs `i < j` of lines meeting there. -/
def vertices (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun i => (List.range n).filterMap fun j =>
    if i < j then some (i, j) else none

/-- Line `m` passes through the intersection of lines `i` and `j`. -/
def through (L : List Line) (m : Nat) (v : Nat × Nat) : Bool :=
  m == v.1 || m == v.2 || concurrent L m v.1 v.2

/-- Some two intersection points have every line through one of them. -/
def coveredByTwoPencils (L : List Line) : Bool :=
  (vertices L.length).any fun v => (vertices L.length).any fun w =>
    (List.range L.length).all fun m => through L m v || through L m w

/-- For six lines: every five of them (all but `out`) contain a triple point, so no five
lines are in general position. -/
def noFiveInGeneralPosition6 (L : List Line) : Bool :=
  (List.range 6).all fun out =>
    (triplePoints L).any fun t => t.1 != out && t.2.1 != out && t.2.2 != out

-- Both hypotheses hold …
example : coveredByTwoPencils six = false := by decide +kernel
example : noFiveInGeneralPosition6 six = true := by decide +kernel

-- … and the conclusion fails: three triple points (the complete quadrangle has four), and
-- six lines, not seven.
example : triplePoints six = [(0, 1, 4), (0, 2, 3), (1, 2, 5)] := by decide +kernel
example : six.length = 6 := by decide +kernel

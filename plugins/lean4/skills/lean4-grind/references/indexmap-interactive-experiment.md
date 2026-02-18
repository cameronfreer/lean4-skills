# IndexMap Interactive Grind Experiment

Date: 2026-02-18

Environment:
- Reference manual workspace: `/Users/alokbeniwal/reference-manual`
- Module under test: `extended-examples/IndexMapGrind.lean`
- Build target prepared with:
  - `cd /Users/alokbeniwal/reference-manual`
  - `lake build IndexMapGrind`

## Goal

Validate how interactive `grind => ...` behaves on the reference-manual `IndexMap` example, and extract practical guidance for skill users.

## Repro Script

```lean
import IndexMapGrind

open IndexMap

section
variable {α : Type} {β : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]

example (m : IndexMap α β) (a a' : α) (b : β) (h : a' ∈ m.insert a b) :
    (m.insert a b)[a'] = if h' : a' == a then b else m[a'] := by
  grind =>
    show_state
    instantiate
    show_state
    finish

example (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).findIdx a = if h : a ∈ m then m.findIdx a else m.size := by
  grind =>
    show_state
    instantiate
```

Command used:
- from the project root: `cd /Users/alokbeniwal/reference-manual && lake env lean /tmp/indexmap_grind_experiment.lean`

## Key Observations

1. Initial state is sparse and contradiction-shaped.
- Before `instantiate`, the state mainly contains:
  - the goal negation,
  - a few typeclass facts,
  - top-level membership assumptions.

2. `instantiate` injects exactly the bridge facts we need.
- In `getElem_insert`, `instantiate` introduced:
  - `(a' ∈ m.insert a b) = (a' = a ∨ a' ∈ m)`
  - `(m.insert a b)[a'] = if ... then b else m[a']`
  - a `getIdx/findIdx` bridge equality
- After this, the equivalence classes align the target expression with the RHS shape.

3. Some goals are solved during `instantiate`.
- In `findIdx_insert_self`, one `instantiate` step closed the goal.
- Practical implication: do not assume `finish` will always be runnable after `instantiate`.

4. `show_cases` and `show_asserted` are high-signal after one `instantiate`.
- `show_cases` surfaced split candidates matching the expected `if` and disjunction structure.
- `show_asserted` provided an immediate inventory of newly asserted bridge facts.

Additional command trace:
- from the project root: `cd /Users/alokbeniwal/reference-manual && lake env lean /tmp/indexmap_grind_experiment_cases.lean`

## Practical Heuristics Derived

1. Start interactive loops with observability:
```lean
grind =>
  show_state
  instantiate
```

2. If unresolved, inspect structure before expensive branching:
```lean
grind =>
  instantiate
  show_cases
  show_asserted
  finish
```

3. If `instantiate` might solve the goal, use guarded control to avoid no-goal failures:
```lean
grind =>
  show_state
  instantiate
  first
    (finish)
    (skip)
```

4. When expected bridge facts do not appear in `show_asserted`, prioritize annotation fixes (`@[local grind ...]`, `grind_pattern`) over widening brute-force search.

---
name: lean4-grind
description: "Use when Lean 4 goals in .lean files should close after normalization plus logic/arithmetic reasoning, when simp/linarith stall, when grind is slow, or when repeated rewrites suggest adding a simproc."
---

# Lean 4 Grind + Simprocs

Use this skill to close proof goals with `grind` in a disciplined way: simplify first, apply `grind` on a small goal, then minimize and stabilize the invocation.

Grounding for this skill:
- Reference manual: `https://lean-lang.org/doc/reference/latest/The--grind--tactic/`
- Lean 4 source inspected at commit `c4d85b762299f69e337fc5cc3305095296d4ab8d` (`~/lean4` master)
- Key implementation files:
  - `src/Init/Grind/Tactics.lean`
  - `src/Init/Grind/Config.lean`
  - `src/Init/Grind/Attr.lean`
  - `src/Lean/Meta/Tactic/Grind/Attr.lean`
  - `src/Lean/Meta/Tactic/Grind/Parser.lean`

## Entry Points

- Preferred mode: `grind => ...` (interactive). It lets you inspect progress (`show_state`) and steer the search (`instantiate`, `cases`, `have`, `finish`).
- Use `grind` for quick direct closure when you do not need step-by-step control.
- Use `grind?` to minimize theorem arguments and derive a tighter call.
- Use `try?` when stuck; it explores multiple `grind` variants plus other tactics and suggests proof scripts.
- Use `grind only [...]` to lock behavior to explicit local/global theorem parameters.

In practice, treat `grind` as syntactic sugar for an internal `grind => ... finish` flow.

## Mental Model

Treat `grind` as a shared-state solver rather than a single tactic call:
- it maintains a shared "whiteboard" of facts and equivalence classes,
- theorem instantiation, case-splitting, and domain solvers cooperate on that state,
- useful modules include LIA/cutsat, ring/grobner-style algebraic reasoning, linarith-style linear reasoning, and AC reasoning.

When debugging, ask "which component is failing to contribute useful facts?" rather than only "which tactic failed?".

## Workflow Decision Tree

1. Inspect goal shape (`lean_goal`) and identify the real blocker.
2. If the goal contains heavy definitions or `let` scaffolding, normalize first (`simp?`, `simp (config := {zeta := true})`).
3. If the residual goal is propositional/equality/order/arithmetic closure, run an interactive loop via `grind => ...`.
4. If a plain `grind` closes quickly, follow with `grind?` and prefer the smaller suggested form (`grind only [...]`) for stability.
5. If the same rewrite pain appears repeatedly, add automation:
   - First choice: helper lemmas + `simp`.
   - Escalation: simproc for deterministic, recurring rewrites.
6. Validate with diagnostics and build gates.

## Preferred Interactive Loop

1. Inspect:
```lean
-- use lean_goal(file, line) from Lean LSP tooling
```

2. Normalize:
```lean
simp?
simp (config := {zeta := true})
```

3. Run controlled search:
```lean
grind =>
  show_state
  instantiate
  first
    (show_asserted)
    (skip)
  first
    (show_cases)
    (skip)
  first
    (cases_next)
    (skip)
  first
    (finish)
    (skip)
```

4. If unresolved, triage by residue:
   - Arithmetic-heavy: `linarith`, `nlinarith`, or `omega`.
   - Rewrite-heavy: add a tiny helper lemma or `have` fact, then retry `finish`.
   - Branch explosion: lower `splits`, `ematch`, `instances`, or `gen`.

5. After success, minimize to a compact non-interactive call when possible (`grind?` -> `grind only [...]`).

If you need a concrete reference run of this loop on the manual `IndexMap` example, see `references/indexmap-interactive-experiment.md`.

## High-Value `grind` Knobs

Use these first for performance control (defaults from `Init/Grind/Config.lean`):

- `(splits := 9)`: case-split depth budget per branch.
- `(ematch := 5)`: E-matching rounds per split phase.
- `(gen := 8)`: maximum theorem-instantiation generation.
- `(instances := 1000)`: max E-matching instances per branch.
- `-splitIte`, `-splitMatch`, `+splitImp`: case-split policy controls.
- `-lia`, `-linarith`, `-ring`, `-ac`: disable expensive solvers selectively while debugging.
- `+qlia`: faster but incomplete arithmetic mode (rational relaxation).

Good first slowdown pass:

```lean
grind (splits := 4) (ematch := 3) (instances := 300) (gen := 5) -splitIte -splitMatch
```

## Suggestions and Locals Workflow

`grind` supports a premise-selection path via `+suggestions` and local-library harvesting via `+locals`.

Use this staged flow:
1. Prototype with:
```lean
grind +suggestions +locals
```
2. If it works, run `grind?` and prefer a minimized `grind only [...]` call.
3. Promote repeatedly selected theorems to attributes (`@[grind ...]`, sometimes `@[simp]`) instead of repeating long argument lists.
4. Re-test without heavy suggestion dependence when possible.

This matches the intended "virtuous cycle": suggestions discover useful premises, then annotations make future proofs cheaper and more predictable.

In large API files, prefer aggressive local annotations first (`@[local grind ...]`, often with `+locals`) so repetitive theorem arguments disappear. Promote to global annotations only after the local pattern proves stable in multiple proofs.

## Annotation and Pattern Strategy

Use theorem annotations before writing custom automation:

- `@[grind]`: default pattern inference.
- `@[grind =]`, `@[grind =_]`, `@[grind _=_]`: equality-oriented matching.
- `@[grind →]`, `@[grind ←]`: forward/backward oriented matching.
- `@[grind cases]`, `@[grind cases eager]`: split guidance for inductive predicates.
- `@[grind intro]`: use constructors of an inductive predicate as matching rules.
- `@[grind inj]`, `@[grind ext]`, `@[grind funCC]`, `@[grind norm]`, `@[grind unfold]`.
- `@[grind!]`: minimal indexable subexpression pattern selection.

When inference is wrong or too broad, specify patterns explicitly:

```lean
grind_pattern myThm => f x, g y where
  guard x ≤ y
  x =/= y
  depth x < 8
```

Supported constraints include `guard`, `check`, `size`, `depth`, `gen`, `max_insts`, value/ground predicates, and definitional equality/inequality guards.

### Annotation-First Agent Behavior

Prefer improving automation over shipping one-off scripts:
- if theorem `T` is repeatedly passed to `grind`, consider a stable `@[grind ...]` annotation on `T`,
- keep exploratory annotations local first (`@[local grind ...]`),
- promote to global annotations only after repeated wins across files (often using `@[grind]` or `@[grind =]` for public API facts).

For API-heavy libraries, aim for proofs that are mostly:

```lean
by
  grind +locals
```

after local annotation tuning, then selectively globalize proven-good attributes.

## Library Design Pattern (`grind_indexmap*`)

Use the Lean test pair
- `~/lean4/tests/lean/run/grind_indexmap_pre.lean`
- `~/lean4/tests/lean/run/grind_indexmap.lean`

as the model for library-scale grind adoption.

Practical loop:
1. Start with direct definitions/theorems (`_pre`) and let difficult proof obligations surface.
2. Unstick locally in interactive mode (`grind => ...`) using targeted `have` statements.
3. Convert recurring bridges into local attributes (`@[local grind ...]`, `@[local grind =]`) and occasional `grind_pattern`.
4. Rework API theorems toward short proofs (`by grind +locals`).
5. Only then promote broadly useful rules to global `@[grind]` / `@[grind =]`.

This keeps exploration cheap while preventing premature global annotation noise.

## IndexMap Experiment Findings

A direct experiment against the reference-manual module `IndexMapGrind` confirms:
- Initial `show_state` is often sparse; the key bridge facts appear after `instantiate`.
- `instantiate` can fully close some goals (notably `findIdx_insert_self`-style goals), so unguarded trailing commands may fail with "No goals to be solved".
- `show_asserted` and `show_cases` right after `instantiate` give the highest-signal debugging view for this example family.

Use this data-backed control shape when probing:

```lean
grind =>
  show_state
  instantiate
  first
    (show_asserted)
    (skip)
  first
    (show_cases)
    (skip)
  first
    (finish)
    (skip)
```

Full notes and reproducer: `references/indexmap-interactive-experiment.md`.

## Interactive Mode Control

Use `grind => ...` as the default development mode; it is the most observable and steerable path.

Useful tools in interactive mode:
- `finish` / `finish?`
- `instantiate` / `use`
- `cases_next` and `cases?`
- `show_state`, `show_cases`, `show_asserted`, `have`

Typical debugging loop:

```lean
grind =>
  show_state
  instantiate
  first
    (show_asserted)
    (skip)
  first
    (show_cases)
    (skip)
  first
    (cases_next)
    (skip)
  first
    (finish)
    (skip)
```

`have` is valuable for injecting missing intermediate facts; once stable, replace ad-hoc `have` steps with annotations or `grind_pattern` so the proof can collapse toward `grind`/`grind only [...]`.

In practice, `instantiate` frequently does most of the work on well-annotated API lemmas; if your loop often closes there, shift effort from tactic choreography to annotation quality.

## Simproc Escalation Rules

Use a simproc only when ordinary `simp` lemmas are insufficient and the same reduction pattern repeats across multiple goals/files.

Rules:
- Prefer `dsimproc` for pure definitional reduction.
- Guard by expression shape before rewriting.
- Return `.continue` on non-matching forms.
- Keep rewrites terminating and orientation-stable.
- Scope simprocs to the smallest module set that benefits.

Template:

```lean
import Lean
open Lean Meta Simp

dsimproc [simp] reduceFoo (Foo _ _) := fun e => do
  unless e.isAppOfArity ``Foo 2 do
    return .continue
  let e' ← whnf e
  return .done e'
```

## Performance and Safety

- Minimize context before `grind`; large hypothesis sets can cause timeouts.
- Prefer local simplification over broad global simp-set changes.
- If search is too expensive, cap exploration by lowering `splits`, `ematch`, `instances`, and `gen`.
- Use traces while debugging theorem instantiation and splitting:

```lean
set_option trace.grind.ematch.instance true in
set_option trace.grind.split true in
  grind
```

- Keep traces out of final committed proofs unless explicitly needed.
- Never change theorem statements or introduce axioms without explicit user approval.

## Complements: `try?`

When stuck, run `try?` as a broad fallback. It explores multiple tactic families, including different `grind` configurations, and often proposes a workable path quickly.

Operational notes:
- `try?` already uses `grind` variants with suggestion/local-library support in its search path.
- This means `try?` can succeed before you have curated annotations, but you should still add `@[local grind ...]` / `@[simp]` when a premise is repeatedly selected.
- See `~/lean4/tests/lean/run/try_first_par.lean` for representative `try?`/`grind` variant behavior.
- Treat `try?` output as a draft: minimize with `grind?`, then converge to stable annotation-based automation.

Treat incomplete-proof diagnostics that invoke `try?` as input to your annotation pipeline, not as final end-state scripts.

## Validation Gate

Run in order:
1. `lean_diagnostic_messages` on edited files.
2. `lake env lean <path/to/File.lean>` for file-level verification (run from the project root).
3. `lake build` for project-wide verification.

## References

- `references/grind-playbook.md`
- `references/indexmap-interactive-experiment.md`
- `plugins/lean4/skills/lean4/SKILL.md`
- `https://lean-lang.org/doc/reference/latest/The--grind--tactic/`
- `~/lean4/tests/lean/run/grind_interactive.lean`
- `~/lean4/tests/lean/run/grind_interactive_2.lean`
- `~/lean4/tests/lean/run/grind_indexmap_pre.lean`
- `~/lean4/tests/lean/run/grind_indexmap.lean`
- Lean Together 2026 grind notes (Kim Morrison / Lean FRO)

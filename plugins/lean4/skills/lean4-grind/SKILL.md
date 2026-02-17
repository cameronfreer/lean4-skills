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

- Use `grind` for direct closure.
- Use `grind?` first when possible. It suggests a tighter `grind only [...]` call.
- Use `grind only [...]` to lock behavior to explicit local/global theorem parameters.
- Use interactive `grind => ...` only when you need explicit internal steps (`instantiate`, `cases`, `finish`, etc.).

## Workflow Decision Tree

1. Inspect goal shape (`lean_goal`) and identify the real blocker.
2. If the goal contains heavy definitions or `let` scaffolding, normalize first (`simp?`, `simp (config := {zeta := true})`).
3. If the residual goal is propositional/equality/order/arithmetic closure, run `grind` or `grind?`.
4. If `grind` succeeds, prefer the smaller suggested form (`grind only [...]`) for stability.
5. If the same rewrite pain appears repeatedly, add automation:
   - First choice: helper lemmas + `simp`.
   - Escalation: simproc for deterministic, recurring rewrites.
6. Validate with diagnostics and build gates.

## Single-Goal Loop

1. Inspect:
```lean
-- use lean_goal(file, line) from Lean LSP tooling
```

2. Normalize:
```lean
simp?
simp (config := {zeta := true})
```

3. Try closure:
```lean
grind
```

4. If unresolved, triage by residue:
   - Arithmetic-heavy: `linarith`, `nlinarith`, or `omega`.
   - Rewrite-heavy: add a tiny helper lemma, then `simp` and retry `grind`.
   - Branch explosion: lower `splits`, `ematch`, `instances`, or `gen`.

5. Keep the smallest successful tactic sequence; avoid layered "try everything" scripts in committed proofs.

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

## Validation Gate

Run in order:
1. `lean_diagnostic_messages` on edited files.
2. `lake env lean <path/to/File.lean>` for file-level verification.
3. `lake build` for project-wide verification.

## References

- `references/grind-playbook.md`
- `plugins/lean4/skills/lean4/SKILL.md`
- `https://lean-lang.org/doc/reference/latest/The--grind--tactic/`

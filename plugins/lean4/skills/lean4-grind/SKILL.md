---
name: lean4-grind
description: "Use when Lean 4 goals in .lean files should close after normalization plus logic/arithmetic reasoning, when simp/linarith stall, when grind is slow, or when repeated rewrites suggest adding a simproc."
---

# Lean 4 Grind + Simprocs

Use this skill to close proof goals with `grind` in a disciplined way: simplify first, apply `grind` on a small goal, and only escalate to simprocs when rewrite patterns are repeated.

## Workflow Decision Tree

1. Inspect goal shape (`lean_goal`) and identify the real blocker.
2. If the goal contains heavy definitions or `let` scaffolding, normalize first.
3. If the residual goal is propositional/equality/order/arithmetic closure, run `grind`.
4. If the same rewrite pain appears repeatedly, add automation:
   - First choice: helper lemmas + `simp`.
   - Escalation: simproc for deterministic, recurring rewrites.
5. Validate with diagnostics and build gates.

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

4. If unresolved, branch by residue:
   - Arithmetic-heavy: `linarith`, `nlinarith`, or `omega`.
   - Rewrite-heavy: add a tiny helper lemma, then `simp` and retry `grind`.

5. Keep the smallest successful tactic sequence; avoid layered "try everything" scripts in committed proofs.

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
- If search is too expensive, cap steps locally:

```lean
set_option grind.maxSteps 2000 in
  grind
```

- Never change theorem statements or introduce axioms without explicit user approval.

## Validation Gate

Run in order:
1. `lean_diagnostic_messages` on edited files.
2. `lake env lean <path/to/File.lean>` for file-level verification.
3. `lake build` for project-wide verification.

## References

- `references/grind-playbook.md`
- `plugins/lean4/skills/lean4/SKILL.md`

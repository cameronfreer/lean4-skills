# Lean Compiler Pipeline Playbook

## Source Anchors

- LCNF orchestration:
  - `~/lean4/src/Lean/Compiler/LCNF/Main.lean`
  - `~/lean4/src/Lean/Compiler/LCNF/Passes.lean`
  - `~/lean4/src/Lean/Compiler/LCNF/PassManager.lean`
  - `~/lean4/src/Lean/Compiler/LCNF/ConfigOptions.lean`
- IR pipeline:
  - `~/lean4/src/Lean/Compiler/IR.lean`
- Global compiler options:
  - `~/lean4/src/Lean/Compiler/Options.lean`
- Example test toggles:
  - `~/lean4/tests/lean/run/extractClosed.lean`
  - `~/lean4/tests/lean/run/lcnf3.lean`
  - `~/lean4/tests/lean/run/simple_ground_extraction.lean`

## Trace Map

LCNF traces:
- `trace.Compiler`
- `trace.Compiler.result`
- phase-specific classes added in `Passes.lean` (`Compiler.saveBase`, `Compiler.saveMono`, `Compiler.saveImpure`)

IR traces:
- `trace.compiler.ir`
- `trace.compiler.ir.init`
- `trace.compiler.ir.result`
- specialized classes (for example: `trace.compiler.ir.rc`, `trace.compiler.ir.boxing`, `trace.compiler.ir.simple_ground`)

## Option Knobs

- `compiler.check`
- `compiler.checkMeta`
- `compiler.checkTypes`
- `compiler.extract_closed`
- `compiler.reuse`
- inline/specialize limits in `ConfigOptions`

Use controlled toggles:
1. baseline all defaults
2. enable one check/trace
3. compare output
4. adjust one knob

## PassInstaller Template

```lean
import Lean.Compiler.LCNF.Passes

open Lean Compiler LCNF

meta def myInstaller : PassInstaller :=
  PassInstaller.installAfter .mono `simp (fun p =>
    { p with name := `myWrappedPass })

attribute [cpass] myInstaller
```

Notes:
- target pass names and occurrences must exist
- failures such as "not in the pass list" mean name/occurrence mismatch
- phase mismatches are rejected by validation

## Typical Failure Patterns

- no effect after adding installer:
  - installer not global
  - declaration not `meta`
  - wrong pass name/occurrence
- pipeline panic/invariant error:
  - incorrect phase assumptions in pass edits
- behavior changes only when `compiler.extract_closed` toggles:
  - regression likely tied to closed-term extraction path

## Escalation Sequence

1. Trace and option toggles only
2. Narrow installer wrapping one pass occurrence
3. Multi-occurrence installer changes
4. Deeper pass replacement

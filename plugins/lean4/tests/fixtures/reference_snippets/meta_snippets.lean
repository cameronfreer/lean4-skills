import Lean

/-!
Core-Lean evidence (no Mathlib) for `references/metaprogramming-patterns.md`
(#181). Run by the `lean-integration` workflow with the `lean_file_gate`
fixture's pinned toolchain (messages pinned to Lean 4.33.1), via
`run_core_snippets.sh`:

    cd plugins/lean4/tests/fixtures/lean_file_gate
    lean ../reference_snippets/meta_snippets.lean

Every documented block is elaborated as written and exercised; documented
behaviour (error spans, hygiene, pretty-printing, associativity) is pinned with
`#guard`/`#guard_msgs`. The last section also pins the corrections carried into
`lean4-custom-syntax.md` and `scaffold-dsl.md` (trace options, associativity of
a custom category, macro recursion).
-/

/-! ### § Minimal DSL Pattern -/

namespace MinimalDsl

/-- Example DSL front door. -/
syntax "mydsl" "{" term "}" : term

macro_rules
  | `(mydsl{$t}) => `($t)

#guard mydsl{1 + 1} == 2

end MinimalDsl

/-! ### § Validation with Precise Error Spans -/

namespace Validation
open Lean

/-- Validate a literal attribute value. -/
def validateAttr (key value : String) (stx : Syntax) : MacroM Unit := do
  if key == "rank" && value != "same" then
    Macro.throwErrorAt stx s!"invalid rank value: {value}"

syntax "dslattr " ident " := " str : term

macro_rules
  | `(dslattr $k:ident := $v:str) => do
      validateAttr k.getId.toString v.getString v
      `(($(quote k.getId.toString), $v))

#guard dslattr rank := "same" == ("rank", "same")

-- The error is reported on the string literal, not on the whole term.
/-- error: invalid rank value: other -/
#guard_msgs in
example := dslattr rank := "other"

-- The `throwErrorAt stx "…{x}"` form needs `MonadError`, which `MacroM` lacks.
/-- error: failed to synthesize instance -/
#guard_msgs (substring := true) in
def badValidate (value : String) (stx : Syntax) : MacroM Unit := do
  throwErrorAt stx "invalid rank value: {value}"

end Validation

/-! ### § Embedding Terms in DSL Values -/

namespace Values
open Lean

declare_syntax_cat dslValue
syntax str : dslValue
syntax ident : dslValue
syntax "(" term ")" : dslValue

syntax "value[" dslValue "]" : term

macro_rules
  | `(value[$s:str]) => `($s)
  | `(value[$x:ident]) => `($(quote x.getId.toString))
  | `(value[($t)]) => `(toString $t)

#guard value["a"] == "a"
#guard value[abc] == "abc"
#guard value[(1 + 1)] == "2"

end Values

/-! ### § Escalate to Elaborators When Needed -/

namespace Elaborator
open Lean Elab Term Meta

syntax (name := view) "view[" term "]" : term

elab_rules : term
  | `(view[$t]) => do
      let e ← elabTerm t none
      let ty ← inferType e
      logInfo m!"view: {e} : {ty}"
      return e

/-- info: view: 3 : Nat -/
#guard_msgs in
example := view[(3 : Nat)]

end Elaborator

/-! ### § Hygiene and Name Control -/

namespace Hygiene
open Lean

-- A name written inside the quotation is hygienic: the user cannot refer to it.
macro "def_hidden" : command => `(def hidden : Nat := 1)
def_hidden
/-- error: Unknown identifier `hidden` -/
#guard_msgs in
example : Nat := hidden

-- A name built with `mkIdent` carries no macro scopes: the user can refer to it.
macro "def_visible" : command => `(def $(mkIdent `visible) : Nat := 2)
def_visible
#guard visible == 2

-- `set_option hygiene false` turns hygiene off for the macros that follow.
set_option hygiene false in
macro "def_unhygienic" : command => `(def unhygienic : Nat := 3)
def_unhygienic
#guard unhygienic == 3

end Hygiene

/-! ### § Unexpanders and Delaborators -/

namespace Pretty

def My.wrap (x : α) : α := x

syntax "wrap[" term "]" : term
macro_rules
  | `(wrap[$t]) => `(My.wrap $t)

/-- Print `My.wrap` applications as `wrap[...]`. -/
@[app_unexpander My.wrap]
def unexpandWrap : Lean.PrettyPrinter.Unexpander
  | `($_ $t) => `(wrap[$t])
  | _ => throw ()

/-- info: wrap[1] : Nat -/
#guard_msgs in
#check (wrap[1] : Nat)

end Pretty

/-! ### § Debugging Checklist / § Common Gotchas -/

namespace Gotchas

-- Without precedences an infix parses, but associates to the right.
syntax term " +++ " term : term
macro_rules
  | `($a +++ $b) => `($a - $b)

#guard (10 +++ 3 +++ 2 : Nat) == 9

-- Precedences make it left-associative.
syntax:65 term:65 " -+- " term:66 : term
macro_rules
  | `($a -+- $b) => `($a - $b)

#guard (10 -+- 3 -+- 2 : Nat) == 5

-- `getString` is the decoded value; `reprint` is the source text.
open Lean Elab Command in
elab "#str_views " s:str : command => do
  logInfo m!"getString: {s.getString}; reprint: {s.raw.reprint.getD ""}"

/-- info: getString: a"b; reprint: "a\"b" -/
#guard_msgs (whitespace := lax) in
#str_views "a\"b"

end Gotchas

-- The documented options exist ...
set_option trace.Elab.step false in
set_option pp.all false in
example : Nat := 0

-- ... and `trace.Macro.expand` does not.
/-- error: Unknown option `trace.Macro.expand` -/
#guard_msgs (substring := true) in
set_option trace.Macro.expand true in
example : Nat := 0

/-! ### § Trace classes for macro expansion (also `lean4-custom-syntax.md`, `scaffold-dsl.md`) -/

namespace Traces

-- A term macro's expansion is an `Elab.step` node. (Elab.step traces are
-- reported after the inner command, so `set_option` goes outside `#guard_msgs`.)
macro "myTermMacro" : term => `(1 + 1)

set_option trace.Elab.step true in
/-- trace: [Elab.step] ✅️ expected type: Nat, term
    myTermMacro
  [Elab.step] ✅️ expected type: Nat, term
      1 + 1 -/
#guard_msgs (substring := true) in
example : Nat := myTermMacro

-- A command macro's expansion is an `Elab.command` node ...
macro "myCmdMacro" : command => `(def macroOut : Nat := 1)

/-- trace: [Elab.command] ✅️ myCmdMacro -/
#guard_msgs (substring := true) in
set_option trace.Elab.command true in
myCmdMacro

-- ... and `trace.Elab.step` shows only the terms of the expanded `def`.
set_option trace.Elab.step true in
/-- trace: [Elab.step] ✅️ expected type: Type, term
    Nat✝
  [Elab.step.result] Nat
[Elab.step] ✅️ expected type: Nat, term
    1
  [Elab.step.result] 1 -/
#guard_msgs in
myCmdMacro

end Traces

/-! ### § `lean4-custom-syntax.md`: associativity in a custom category, macro recursion -/

namespace CustomCat

declare_syntax_cat arithR
syntax num : arithR
syntax arithR " + " arithR : arithR
syntax "[arithR|" arithR "]" : term
macro_rules
  | `([arithR| $n:num]) => `(($n : Int))
  | `([arithR| $a + $b]) => `([arithR| $a] - [arithR| $b])

-- No precedences: no loop, but right-associative.
#guard [arithR| 10 + 3 + 2] == 9

declare_syntax_cat arithL
syntax num : arithL
syntax:65 arithL:65 " + " arithL:66 : arithL
syntax "[arithL|" arithL "]" : term
macro_rules
  | `([arithL| $n:num]) => `(($n : Int))
  | `([arithL| $a + $b]) => `([arithL| $a] - [arithL| $b])

#guard [arithL| 10 + 3 + 2] == 5

-- `maximum recursion depth` comes from an expansion that reproduces its input.
syntax "loopy" : term
macro_rules
  | `(loopy) => `(loopy)

/-- error: maximum recursion depth has been reached -/
#guard_msgs (substring := true) in
#check loopy

end CustomCat

---
description: Scaffold a new DSL with syntax category, bridge, and elaboration
---

# Scaffold DSL

Generate this template, then customize:

```lean
import Lean
open Lean Elab Meta

namespace MyDSL

-- 1. Syntax categories (hierarchical)
declare_syntax_cat myAtom
declare_syntax_cat myExpr

-- 2. Atoms
syntax ident : myAtom
syntax num : myAtom
syntax str : myAtom
syntax "+" : myAtom    -- operators as atoms

-- 3. Expressions
syntax myAtom : myExpr
syntax "(" myExpr ")" : myExpr
syntax:70 myExpr " * " myExpr:71 : myExpr
syntax:65 myExpr " + " myExpr:71 : myExpr

-- 4. Bridge to term
syntax "[myDSL|" myExpr "]" : term

-- 5. Target AST
inductive Expr where
  | var : String → Expr
  | num : Int → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  deriving Repr

-- 6. Elaboration
macro_rules
  | `([myDSL| $i:ident]) => `(Expr.var $(Lean.quote i.getId.toString))
  | `([myDSL| $n:num]) => `(Expr.num $n)
  | `([myDSL| ($e)]) => `([myDSL| $e])
  | `([myDSL| $a + $b]) => `(Expr.add [myDSL| $a] [myDSL| $b])
  | `([myDSL| $a * $b]) => `(Expr.mul [myDSL| $a] [myDSL| $b])

-- 7. Test
#check [myDSL| x + 1 * 2]
example : [myDSL| 1 + 2] = Expr.add (.num 1) (.num 2) := rfl

end MyDSL
```

## Debug Commands

```lean
set_option pp.notation false in #check [myDSL| ...]  -- see expansion
set_option pp.all true in #check [myDSL| ...]        -- full detail
set_option trace.Macro.expand true in ...            -- trace expansion
```

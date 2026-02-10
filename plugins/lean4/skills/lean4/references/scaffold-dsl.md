# DSL Scaffold Template

Copy-paste starting point for a new embedded DSL. Includes syntax categories, bridge macro, AST, elaboration, and tests.

**How to use:** Copy the template below into a new `.lean` file. Replace `MyDSL`/`myDSL`/`myExpr`/`myAtom` with your DSL's names and `Expr` with your target AST type. Run `lake build` to verify, then inspect expansion with `set_option pp.notation false in #check [myDSL| ...]`. See [lean4-custom-syntax.md](lean4-custom-syntax.md) for the full API reference.

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
-- Add more atoms (e.g., str) with matching macro_rules if needed.

-- 3. Expressions
syntax myAtom : myExpr
syntax "(" myExpr ")" : myExpr
syntax:70 myExpr:70 " * " myExpr:71 : myExpr
syntax:65 myExpr:65 " + " myExpr:66 : myExpr

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
set_option trace.Macro.expand true in #check [myDSL| x + 1 * 2]  -- trace expansion
```

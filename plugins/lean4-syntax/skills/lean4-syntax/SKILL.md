---
name: lean4-syntax
description: Lean 4 custom syntax - DSLs, macros, elaborators. Use when building notation, embedded languages, or tactic extensions.
---

# Lean 4 Custom Syntax

## Decision Tree

| Need | Use | Complexity |
|------|-----|------------|
| Binary/unary operator | `infixl:65 " ⊕ " => f` | Trivial |
| Fixed pattern | `notation "⟨" a "," b "⟩" => Prod.mk a b` | Low |
| Pattern-matching expansion | `syntax` + `macro_rules` | Medium |
| Type info / env access | `elab_rules` | High |
| New grammar (DSL) | `declare_syntax_cat` | High |

## Docstrings = Hover Docs

**Add docstrings to syntax/macro_rules** so hovering shows where syntax comes from:

```lean
/-- Assert that condition is true, panic otherwise. -/
syntax "assert!" term : term

/-- Expands assert! to if-then-panic. -/
macro_rules
  | `(assert! $c) => `(if $c then () else panic! "fail")
```

## Quick Patterns

```lean
-- 1. Operator
infixl:65 " ⊕ " => myAdd

-- 2. Notation
notation "⟨" a ", " b "⟩" => Prod.mk a b

-- 3. Combined macro
macro "dbg!" e:term : term => `(dbg_trace "{$e}"; $e)

-- 4. Full DSL
declare_syntax_cat myDSL
syntax num : myDSL
syntax myDSL "+" myDSL : myDSL
syntax "[dsl|" myDSL "]" : term

macro_rules
  | `([dsl| $n:num]) => `($n)
  | `([dsl| $a + $b]) => `([dsl| $a] + [dsl| $b])
```

## Precedence

```
max=1024  min=10  lead=0
80: * /    65: + -    50: < > =    35: ∧    30: ∨    25: →

Left-assoc:  syntax:65 term " + " term:66   -- right operand higher
Right-assoc: syntax:25 term:26 " → " term   -- left operand higher
Non-assoc:   syntax:50 term:51 " = " term:51
```

## API Cheat Sheet

```lean
-- MacroM
Macro.addMacroScope `name       -- fresh hygienic name
Macro.throwErrorAt stx "msg"    -- positioned error
Macro.hasDecl `name             -- check if exists
withFreshMacroScope do ...      -- avoid name clashes in loops

-- Syntax extraction
stx.reprint                     -- original user text (use this!)
n.getNat                        -- TSyntax `num → Nat
s.getString                     -- TSyntax `str → String
i.getId                         -- TSyntax `ident → Name
xs.getElems                     -- array from $xs,*

-- Elaboration (when macros aren't enough)
elabTerm stx (some expectedTy)  -- elaborate with type hint
goal.withContext do ...         -- REQUIRED for correct lctx in tactics
throwErrorAt stx msg            -- positioned errors
liftMacroM (translateExpr e)    -- lift MacroM into CommandElabM
```

## MetaM Utilities

```lean
-- Expression building (auto-infers implicits/universes)
mkAppM ``List.cons #[x, xs]          -- better than manual Expr.app
mkAppOptM ``f #[some a, none, some c] -- none = create metavar
mkEq a b / mkEqRefl a / mkEqTrans h₁ h₂

-- Type operations
inferType e                     -- get type (fast, doesn't full-check)
whnf e                          -- weak head normal form (call repeatedly for nested)
isDefEq a b                     -- definitional equality with unification
instantiateMVars e              -- MUST call after assigning mvars

-- Binder telescopes (essential pattern)
forallTelescope ty fun xs body => do  -- decompose ∀ x₁...xₙ, B
  let result ← processBody xs body
  mkForallFVars xs result             -- rebuild with modified body

lambdaTelescope e fun xs body => ...  -- same for λ

-- Local context
withLocalDecl `x BinderInfo.default xTy fun x => do
  let body ← elaborate x
  mkLambdaFVars #[x] body

-- Expression transformation
transform e (pre := fun e => match e with
  | .const n _ => .visit (mkConst newN)
  | _ => .continue)
```

## Gotchas

**Hygiene:**
- Macros are hygienic by default (names get scopes like `foo._@.Module._hyg.123`)
- Break hygiene: `let x := Lean.mkIdent `x` (unhygienic ident)
- Fresh unique: `name ← Macro.addMacroScope `tmp`
- Use `withFreshMacroScope` when generating syntax in loops

**Unexpanders:**
- Auto-generated only if: single function app, params appear once, in order
- Manual: `@[app_unexpander myFunc] def unexpand | \`($_ $a $b) => \`(notation $a $b)`

**Precedence:**
- `:66` on RIGHT operand makes left-associative (counterintuitive)
- `:26` on LEFT operand makes right-associative

**TSyntax:**
- Use `.reprint` for user text, not `.getString` (reprint reconstructs from tree)
- Pattern match extracts typed syntax: `| \`([dsl| $n:num]) => ...`

**MetaM:**
- `whnf` only reduces head - call repeatedly for nested structures
- `isAssigned` misses delayed assignments - check both `isAssigned` AND `isDelayedAssigned`
- Always `instantiateMVars` after assigning metavariables
- Use `withTransparency .all` to unfold everything (default skips `@[irreducible]`)

## Patterns

**Hierarchical categories:**
```lean
declare_syntax_cat myId      -- atoms (incl. operators as first-class)
declare_syntax_cat myExpr    -- expressions from atoms
declare_syntax_cat myStmt    -- statements from expressions
```

**Operators as category members:**
```lean
syntax ident : myId
syntax "+" : myId            -- operators ARE valid identifiers
syntax "-" : myId
```

**Sanitize early, use consistently:**
```lean
def getIdStr (stx : Syntax) : String :=
  stx.reprint.getD "" |>.trim  -- .reprint preserves original!

def sanitize (s : String) : Name :=
  s.replace "-" "_" |>.replace "?" "_p" |> Name.mkSimple
```

**Separate value vs code translation:**
```lean
def translateValue (stx) := ...   -- quoted data → AST constructors
def translateCode (stx) := ...    -- executable → function calls
```

**Multi-pass over immutable syntax:**
```lean
let vars ← collectFreeVars body    -- pass 1: analysis
let code ← translateCode body       -- pass 2: synthesis
```

**Builtin detection as first-pass filter:**
```lean
def isBuiltin (s : String) : Bool :=
  ["+", "-", "if", "cons", "car", "cdr"].contains s

-- Skip builtins when collecting free variables
if isBuiltin name then [] else [mkIdent (sanitize name)]
```

## TacticM Utilities

```lean
-- Goal access
getMainGoal                     -- current goal MVarId
getMainTarget                   -- goal type (shortcut)
getGoals / setGoals             -- all goals
replaceMainGoal [g1, g2]        -- replace main with multiple

-- Context
withMainContext do ...          -- REQUIRED for lctx access
getLCtx                         -- local context
lctx.findDeclM? fun d => ...    -- search hypotheses

-- Goal manipulation
closeMainGoal `tac expr         -- close with proof term
mvarId.assign expr              -- assign metavariable
mvarId.define `n ty val         -- add let-binding
mvarId.assert `n ty val         -- add hypothesis

-- Lifting
liftMetaTactic fun g => do      -- run MetaM, return new goals
  let gs ← someMetaOp g
  return gs
liftMetaTactic1 fun g => ...    -- for single goal result

-- Error handling
tryTactic? tac                  -- Option α (no throw)
closeUsingOrAdmit tac           -- try or admit with warning
throwTacticEx `name goal msg    -- formatted tactic error

-- Tactic evaluation
evalTactic (← `(tactic| simp))  -- run tactic syntax
focus do ...                    -- focus on first goal only
```

## Pretty Printing

```lean
-- Delaborator (Expr → Syntax, for #check output)
@[delab app.myFunc]
def delabMyFunc : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' `myFunc 2
  let a ← withAppFn (withAppArg delab)
  let b ← withAppArg delab
  `(myNotation $a $b)
```

See reference.md for unexpanders (Syntax → Syntax).

## Troubleshooting

**Diagnostic workflow:**
```
1. Parse error?     → Syntax rule wrong (check precedence, missing bridge)
2. Macro silent?    → set_option trace.Macro.expand true
3. Wrong output?    → set_option pp.notation false (see actual term)
4. Type error?      → set_option pp.all true (see implicit args)
```

**Common errors:**

| Error | Cause | Fix |
|-------|-------|-----|
| `unknown identifier 'x'` | Hygiene scoped name away | Use `mkIdent \`x` to break hygiene |
| `expected term` | Macro returned wrong syntax kind | Check antiquotation: `$e` vs `$e:term` |
| `ambiguous, possible interpretations` | Overlapping syntax rules | Add precedence or more specific pattern |
| `maximum recursion depth` | Left-recursive without precedence | Add `:N` to break recursion |
| `failed to synthesize instance` | Elaborator needs type hint | Use `elabTerm stx (some expectedType)` |

**When macros aren't enough** (escalate to `elab_rules`):

| Need | Why Macro Can't | Elaborator Solution |
|------|-----------------|---------------------|
| Infer types | No `Expr` access | `let ty ← inferType e` |
| Check env | No `Environment` | `let env ← getEnv` |
| Unification | No metavars | `isDefEq a b` |
| Fresh names | Only `addMacroScope` | `mkFreshId` / `mkFreshExprMVar` |

```lean
-- Escalation example: macro can't inspect types
elab "typeof!" e:term : term => do
  let e ← elabTerm e none
  let ty ← inferType e
  logInfo m!"{ty}"
  return e
```

**Debug commands:**
```lean
set_option trace.Macro.expand true   -- see macro expansion
set_option trace.Elab.step true      -- see elaboration steps
set_option pp.all true               -- see all implicit args
dbg_trace "x = {x}"                  -- runtime printf
logInfo m!"{e}"                      -- permanent, pretty-prints Expr
```

## External

- [Lean 4 Manual: Notations and Macros](https://lean-lang.org/doc/reference/latest/Notations-and-Macros)
- [Metaprogramming in Lean 4](https://leanprover-community.github.io/lean4-metaprogramming-book/)
- [Lean Community Blog](https://leanprover-community.github.io/blog/) - simprocs, search

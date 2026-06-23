# Lean 4 Custom Syntax

> **Version note:** API names in `MetaM`, `TacticM`, and `MacroM` can change across Lean toolchain versions. If a function listed here is not found, check the current Lean 4 source or run `#check @functionName` to verify availability in your toolchain.

## Scope

Reference for Lean 4 syntax extensions: notations, macros, elaborators, and embedded DSLs. Covers the full escalation path from `infixl` to `declare_syntax_cat` + `elab_rules`.

**Read when:** building custom notation, creating embedded DSLs, writing tactic extensions, or debugging macro expansion issues.

**Not part of the prove/autoprove default loop.** This is supplemental reference material for projects that define or modify custom syntax.

## Contents

- [Decision Tree](#decision-tree) — notation vs macro vs elaborator
- [Precedence](#precedence) — associativity and binding power
- [Elaborator Monads](#elaborator-monads) — MacroM, TermElabM, CommandElabM, TacticM
- [API Cheat Sheet](#api-cheat-sheet) — MacroM and syntax extraction
- [MetaM Utilities](#metam-utilities) — expression building, telescopes, transforms
- [TacticM Utilities](#tacticm-utilities) — goals, context, lifting
- [Breaking Hygiene](#breaking-hygiene) — mkIdent, addMacroScope, user names
- [Unexpanders](#unexpanders) — auto-generated vs manual
- [Syntax Categories](#syntax-categories) — declare, bridge, recursion
- [Repetition and Splice Syntax](#repetition-and-splice-syntax) — `*`, `+`, `?`, antiquotation
- [Gotchas](#gotchas) — hygiene, precedence, TSyntax, MetaM pitfalls
- [Patterns](#patterns) — hierarchical categories, sanitization, multi-pass
- [Troubleshooting](#troubleshooting) — diagnostic workflow, error table, escalation

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

Use `@[inherit_doc]` on notation/operators to copy docs from the target declaration.

## Quick Patterns

```lean
-- 1. Operator
infixl:65 " ⊕ " => myAdd

-- 2. Notation
notation "⟨" a ", " b "⟩" => Prod.mk a b

-- 3. Combined macro
macro "dbg!" e:term : term => `(dbg_trace m!"{e}"; $e)

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
max=1024  arg=max-1  lead=arg-1  min=10
70: * /    65: + -    50: < > =    35: ∧    30: ∨    25: →

Left-assoc:  syntax:65 term " + " term:66   -- right operand higher
Right-assoc: syntax:25 term:26 " → " term   -- left operand higher
Non-assoc:   syntax:50 term:51 " = " term:51
```

## Elaborator Monads

| Monad | Purpose | Key Functions |
|-------|---------|---------------|
| `MacroM` | Syntax → Syntax | `addMacroScope`, `throwErrorAt`, `hasDecl` |
| `TermElabM` | Syntax → Expr | `elabTerm`, `inferType`, `synthInstance`, `isDefEq` |
| `CommandElabM` | Top-level commands | `getEnv`, `modifyEnv`, `elabCommand` |
| `TacticM` | Proof tactics | `getMainGoal`, `closeMainGoal`, `getLocalHyps` |

**MacroM limitations** (use elaborator if you need these):
- No IO
- No environment modification
- No local context access
- No unification

**Lifting**: `liftMacroM` to use MacroM inside CommandElabM

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

-- Expression building (literals and constants)
mkNatLit 42                     -- Nat literal
mkStrLit "hello"                -- String literal
.const ``Nat.zero []            -- constant with no levels
Expr.app f x                    -- direct application
mkAppN f #[a, b, c]             -- multi-arg application

-- Expression transformation
transform e (pre := fun e => match e with
  | .const n _ => .visit (mkConst newN)
  | _ => .continue)
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

## Breaking Hygiene

```lean
-- Method 1: mkIdent with raw name (captures user's binding)
let x := Lean.mkIdent `x
`(let $x := 42; $body)  -- 'x' visible in body

-- Method 2: Fresh guaranteed-unique name
let fresh ← Macro.addMacroScope `tmp
`(let $fresh := 42; ...)

-- Method 3: User provides name (naturally in their scope)
macro "bind" x:ident ":=" v:term "in" b:term : term =>
  `(let $x := $v; $b)  -- $x is user's, so visible
```

**Test hygiene:**
```lean
let x := "user"
myMacro x  -- should use user's x, not macro's internal x
```

## Unexpanders

**Auto-generated when:**
- RHS is single function application
- Each param appears exactly once
- Params in same order as notation

```lean
-- Gets auto unexpander:
notation "⟨" a ", " b "⟩" => Prod.mk a b

-- NO auto unexpander (reordered):
notation "swap" a b => Prod.mk b a

-- NO auto unexpander (duplicated):
notation "dup" a => Prod.mk a a
```

**Manual unexpander:**
```lean
@[app_unexpander myFunc]
def unexpandMyFunc : Unexpander
  | `($_ $a $b) => `(myNotation $a $b)
  | _ => throw ()
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

## Syntax Categories

**Declare:**
```lean
declare_syntax_cat myDSL
declare_syntax_cat myDSL (behavior := symbol)  -- treat idents as symbols
```

**Bridge to term (required!):**
```lean
syntax "[myDSL|" myDSL "]" : term
```

**Recursive with precedence (avoid infinite loop):**
```lean
syntax:65 myDSL " + " myDSL:66 : myDSL  -- left-assoc, :66 stops recursion
```

## Indentation-Sensitive Syntax

```lean
syntax withPosition("block" colGt term+) : term
-- terms must be indented past "block"

colGt   -- strictly greater column
colGe   -- greater or equal
colEq   -- exact column
lineEq  -- same line
```

## Repetition and Splice Syntax

```lean
-- Repetition
term*      -- zero or more
term+      -- one or more
term?      -- optional
term,*     -- comma-separated
term,+     -- comma-separated, at least one
term,*,?   -- with optional trailing comma

-- Splices (antiquotation)
`($x)           -- single
`($args*)       -- array as separate args
`([$items,*])   -- array with separator
`($opt?)        -- optional element
`($[: $ty]?)    -- optional with prefix literal

-- Access array in macro:
let elems := xs.getElems
for e in elems do ...
```

## MonadQuotation

```lean
getRef                          -- current syntax reference
withRef stx do ...              -- set reference for errors
getCurrMacroScope               -- current scope number
withFreshMacroScope do ...      -- fresh scope for loops
```

## Message Formatting

```lean
-- Use m!"..." for MessageData (pretty-prints Exprs)
logInfo m!"type is {← inferType e}"
throwError m!"expected {expected}, got {actual}"

-- Use f!"..." only for simple strings
dbg_trace f!"count = {n}"
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
- `whnf` only reduces head — call repeatedly for nested structures
- `isAssigned` misses delayed assignments — check both `isAssigned` AND `isDelayedAssigned`
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

- [metaprogramming-patterns.md](metaprogramming-patterns.md) — MetaM/TacticM API patterns, composable blocks, elaborators
- [Lean 4 Manual: Notations and Macros](https://lean-lang.org/doc/reference/latest/Notations-and-Macros)
- [Metaprogramming in Lean 4](https://leanprover-community.github.io/lean4-metaprogramming-book/)
- [Lean Community Blog](https://leanprover-community.github.io/blog/) — simprocs, search

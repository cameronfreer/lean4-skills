# Lean 4 Syntax Reference

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

## Indentation-Sensitive

```lean
syntax withPosition("block" colGt term+) : term
-- terms must be indented past "block"

colGt   -- strictly greater column
colGe   -- greater or equal
colEq   -- exact column
lineEq  -- same line
```

## Repetition Syntax

```lean
term*      -- zero or more
term+      -- one or more
term?      -- optional
term,*     -- comma-separated
term,+     -- comma-separated, at least one
term,*,?   -- with optional trailing comma
```

## Splice Syntax

```lean
`($x)           -- single
`($args*)       -- array as separate args
`([$items,*])   -- array with separator
`($opt?)        -- optional element
`($[: $ty]?)    -- optional with prefix literal

-- Access array in macro:
let elems := xs.getElems
for e in elems do ...
```

## Expression Building

```lean
mkAppM ``List.cons #[x, xs]     -- auto-infer implicits
mkAppOptM ``f #[some a, none]   -- none = fresh mvar
mkNatLit 42                     -- Nat literal
mkStrLit "hello"                -- String literal
.const ``Nat.zero []            -- constant with no levels
Expr.app f x                    -- direct application
mkAppN f #[a, b, c]             -- multi-arg application
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

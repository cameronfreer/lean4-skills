# Lean 4 Custom Syntax Skill

Focused reference for Lean 4 syntax extensions: DSLs, macros, elaborators.

## Contents

- `SKILL.md` - Decision tree, API cheat sheet, MetaM/TacticM utilities, gotchas, patterns
- `references/reference.md` - Elaborator monads, hygiene, unexpanders, tactic patterns
- `commands/scaffold-dsl.md` - DSL template

## Commands

| Command | Description |
|---------|-------------|
| `/lean4-syntax:scaffold-dsl` | Generate DSL boilerplate |

## Quick Reference

```lean
-- Macro API
Macro.addMacroScope `name    -- fresh hygienic name
stx.reprint                  -- original user text
xs.getElems                  -- array from $xs,*

-- MetaM
mkAppM ``f #[x, y]           -- auto-infers implicits
forallTelescope ty fun xs body => ...

-- Precedence
80: * /    65: + -    50: < > =    35: ∧    30: ∨    25: →
Left-assoc: term:66 on right
```

## License

MIT

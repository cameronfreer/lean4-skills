import LinterRule

/-!
Uses the `linter_rule.lean` linter (see there). Elaborated by
`run_core_snippets.sh` with `-Dweak.linter.myRule=true`, the command-line
form of the lakefile's `weak.linter.myRule` option.
-/

set_option linter.myRule false in
def BadIdent : Nat := 1

-- The linter fires on each offending identifier, with the disable hint.
/--
warning: avoid BadIdent; use GoodIdent

Note: This linter can be disabled with `set_option linter.myRule false`
-/
#guard_msgs in
def useBad : Nat := BadIdent

-- § Local Disable Pattern: honoured because the run function is wrapped in
-- `withSetOptionIn`.
#guard_msgs in
set_option linter.myRule false in
-- justify why the exception is needed
def useBad2 : Nat := BadIdent

-- Fixture (#185 review): a Name literal `` `throwError `` is a value, not
-- the interpolating keyword, so the string after it is ordinary. Its `{`
-- must not open code: `#check live`, `after` and `#check after` survive,
-- and `dead`, referenced only as literal text, is the one finding.
def live : Nat := 1
#check Lean.Name.str `throwError "{"
#check live
def after : Nat := 2
#check after
#check Lean.Name.str `throwError "literal {dead}"
#check Lean.Name.str `s! "literal {dead}"
def dead : Nat := 0

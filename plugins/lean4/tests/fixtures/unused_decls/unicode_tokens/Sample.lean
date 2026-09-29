-- Fixture (#185 review): a literal right after a Unicode delimiter. `⟨`
-- ends a token, so the char literal `'"'` and the raw string are
-- recognised; neither may swallow `live`, `after` or the `#check`.
-- (Unicode-named declarations are checked at the scanner level only: the
-- two search backends extract them differently, a pre-existing gap.)
def live : Nat := 1
example : Char × Nat := ⟨'"', live⟩
def after : Nat := 2
#check after
example : String × Nat := ⟨r#"quoted "dead" text"#, live⟩
def dead : Nat := 0

-- Fixture (#185 review): an escaped identifier «…» is opaque — the `--`
-- and the `"` inside are not a comment or a string, so the references to
-- `live` after them are counted. `dead` is the only finding.
def live : Nat := 1
example : Nat := let «x--» := live; «x--»
example : Nat := let «y"z» := live; «y"z»
def dead : Nat := 0

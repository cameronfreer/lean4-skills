-- Fixture (#185 review): `.ignore` excludes generated/ for ripgrep. The
-- only reference to `dead` lives there, so under the rg backend `dead`
-- must still be flagged — mirroring must not broaden the searched set.
def dead : Nat := 0
def other : Nat := 1
#check other

-- Fixture: the only decl is BOTH indented AND modifier-prefixed. The
-- extraction regex (column-0 only) can't see it; the shape heuristic
-- must still detect it and exit 1. Reviewer-caught: the first-pass
-- heuristic matched indented `def` but not indented `noncomputable def`.
namespace N
  noncomputable def hidden : Nat := 0
end N

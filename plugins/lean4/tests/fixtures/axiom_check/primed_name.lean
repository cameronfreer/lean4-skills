-- Fixture for declaration names ending in apostrophe(s) — common Lean
-- style for "primed" variants (foo', foo''). Real Lean 4 output for a
-- `theorem foo' : ...` inside `namespace Sorry` is:
--   'Sorry.foo'' depends on axioms: [sorryAx]
-- The pre-fix parser used [a-zA-Z0-9_.]+ for the printed name, which
-- excluded apostrophes and misclassified every such decl as unrecognized.
-- Locks in that primed names are captured correctly.
namespace Sorry

theorem primed' : True := trivial

theorem double_primed'' : True := trivial

end Sorry

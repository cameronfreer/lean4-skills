-- Fixture exercising the LEGACY `#print axioms` output format.
-- The shim routes names starting with `Legacy.` to the multi-line output
-- (`X depends on axioms:` header + one axiom per subsequent line, no quotes,
-- no brackets). This locks in that the parser still handles the older
-- Lean output style even after the modern-format update.
namespace Legacy

theorem old_format_ok : True := trivial

end Legacy

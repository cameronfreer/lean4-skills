-- Fixture for the "'X' does not depend on any axioms" output form.
-- Real Lean 4 emits this line for decls whose only dependencies are
-- built-in (e.g. `trivial` proofs of `True`). The parser MUST count
-- these as verified — otherwise mixed accessible+inaccessible runs
-- would misreport clean accessible decls as unverified.
namespace NoAxioms

theorem depends_on_nothing : True := trivial

end NoAxioms

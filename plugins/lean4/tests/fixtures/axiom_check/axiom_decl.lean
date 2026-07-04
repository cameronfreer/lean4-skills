-- Fixture: a top-level `axiom` decl inside a namespace. Pre-fix, the walk
-- only knew `theorem|lemma|def|instance|abbrev|example|structure|class|inductive`
-- as decl keywords, so the file showed "No declarations found" and got a
-- return 0 without being added to UNVERIFIED_FILES. In directory-mode
-- runs alongside a clean file the aggregate could show green.
-- Reviewer-caught silent-green path. Locks in that `axiom` is now
-- extracted and flagged.
namespace Sorry

axiom badAxiom : False

end Sorry

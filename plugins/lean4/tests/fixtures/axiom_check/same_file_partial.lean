-- Fixture: one file, one accessible decl and one unresolved decl.
-- Pre-fix (aef7e5c), the file counted as verified because parse_axioms_output
-- set PARSED_ANY=true for the accessible one — but the Unknown decl was
-- silently dropped, and the aggregate could still show green.
-- Reviewer-caught. Locks in "parsed_count == extracted_count" invariant.
namespace Clean

theorem ok : True := trivial

end Clean

namespace Unknown

theorem lost : True := trivial

end Unknown

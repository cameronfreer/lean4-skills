-- Fixture: axiom names that contain a standard axiom as a substring.
-- Pre-fix, STANDARD_AXIOMS was unanchored + `.` used as literal but
-- interpreted as regex-any: `my.propext.bad` would match the pattern
-- `propext` as a substring, and the axiom would be filtered out as
-- standard even though it's not.
namespace Substring

theorem contains_substring : True := trivial

end Substring

-- Fixture: one file, one decl with sorryAx AND one unresolved decl.
-- Locks in that the RED custom-axiom finding surfaces even when the file
-- itself is marked unverified (a real finding is never suppressed by
-- coverage incompleteness).
namespace Sorry

theorem needs_sorry : True := trivial

end Sorry

namespace Unknown

theorem lost : True := trivial

end Unknown

-- Locks in multiple-sibling-namespace qualification. Pre-fix, `bar` would
-- have wrongly inherited `A.` (the first namespace) and yielded
-- `unknownIdentifier A.bar`. Post-fix, `bar` gets `B.` correctly.
namespace A

theorem foo : True := trivial

end A

namespace B

theorem bar : True := trivial

end B

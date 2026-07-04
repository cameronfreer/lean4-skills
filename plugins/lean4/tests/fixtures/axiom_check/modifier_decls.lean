-- Fixture: declarations prefixed by common modifier keywords. Pre-fix,
-- the walk required the decl keyword at column 0, so `noncomputable def
-- foo` and friends were not extracted — "No declarations found" and
-- silent return 0. Locks in that `noncomputable`, `unsafe`, `partial`,
-- and `nonrec` prefixes are recognized.
namespace Sorry

noncomputable def opaque_def : True := trivial

unsafe def unsafe_def : True := trivial

partial def partial_def : True := trivial

nonrec def nonrec_def : True := trivial

end Sorry

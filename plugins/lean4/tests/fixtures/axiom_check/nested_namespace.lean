-- Locks in nested-namespace qualification: A.B.foo, not A.foo or B.foo.
namespace A

namespace B

theorem foo : True := trivial

end B

end A

-- Locks in bare-`end` popping. `end` (no name) pops the top frame, so
-- `bar` after it is root-scope and stays bare `bar`, NOT `A.bar`.
namespace A

theorem foo : True := trivial

end

theorem bar : True := trivial

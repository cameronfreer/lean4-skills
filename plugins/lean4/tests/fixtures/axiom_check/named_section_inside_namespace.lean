-- Locks in named-section frame handling. `section S` pushes a `sec:S`
-- frame that doesn't contribute to the prefix; `end S` pops it. Both
-- `sec_named` and `after_sec` are qualified `A.`.
namespace A

section S

theorem sec_named : True := trivial

end S

theorem after_sec : True := trivial

end A

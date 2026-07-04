-- Locks in that anonymous sections don't leak into the prefix, and bare
-- `end` pops the section without dropping the outer namespace. Both
-- `sec_inside` and `after_sec` are qualified `A.`, not `A.section.`.
namespace A

section

theorem sec_inside : True := trivial

end

theorem after_sec : True := trivial

end A

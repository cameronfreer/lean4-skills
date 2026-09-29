-- Fixture (#184): private declarations are extracted. `helper` is used
-- within its file; `hidden` is not — it is the highest-value finding the
-- tool can make, since a private decl can only ever be used in this file.
private theorem helper : True := trivial
theorem uses_helper : True := helper
#check uses_helper
private theorem hidden : True := trivial

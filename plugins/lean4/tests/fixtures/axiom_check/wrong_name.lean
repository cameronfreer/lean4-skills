-- Fixture: shim emits a header for a name that WASN'T requested. The
-- expected-name filter in the parser must reject the alien header and
-- keep parsed_count at 0. Coverage invariant then marks the file
-- unverified. Reviewer-caught: previous count-only invariant would have
-- accepted 1 parsed header == 1 extracted decl and silently green'd.
namespace WrongName

theorem lost : True := trivial

end WrongName

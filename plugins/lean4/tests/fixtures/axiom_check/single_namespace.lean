-- Fixture for test_check_axioms_inline.sh — the #132 minimal repro.
-- Shim maps names not starting with Sorry./Unknown. to standard axioms.
namespace Foo

theorem bar : True := trivial

theorem baz : True := trivial

end Foo

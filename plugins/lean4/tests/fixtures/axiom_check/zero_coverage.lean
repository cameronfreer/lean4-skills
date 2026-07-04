-- The shim maps names starting with `Unknown.` to `unknownIdentifier`
-- errors. Every declaration here becomes unresolvable, exercising the
-- not-accessible branch with PARSED_ANY=false. Pre-fix, this passed
-- silently with "✓ All files use only standard axioms" after checking
-- zero declarations — the load-bearing regression case from #132.
namespace Unknown

theorem cant_resolve_a : True := trivial

theorem cant_resolve_b : True := trivial

end Unknown

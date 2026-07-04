-- Fixture: shim exits 0 but emits output the parser doesn't recognize.
-- Simulates a future Lean output-format change that the parser misses.
-- Coverage invariant should catch it: parsed_count=0 < extracted_count=1
-- → file marked unverified, run exits 1, no green verdict.
namespace Silent

theorem parser_misses : True := trivial

end Silent

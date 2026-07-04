-- Fixture: file has only indented decls (not at column 0). Pre-fix the
-- walk required column-0 keywords, so the indented `theorem` was
-- skipped. Post-fix heuristic detects the shape and marks the file
-- UNVERIFIED rather than silently passing.
namespace Nesting
  theorem indented_theorem : True := trivial
end Nesting

-- Fixture: file has ONLY `private` decls at column 0. Pre-fix the walk
-- skipped them entirely (`private` prefix not in the decl-keyword
-- alternation), DECLARATIONS was empty, and the file was silently
-- skipped with "No declarations found" — returned 0, could green
-- through mixed-directory aggregates. Post-fix heuristic detects the
-- decl-shaped `private theorem` line and marks the file UNVERIFIED.
private theorem hidden : True := trivial

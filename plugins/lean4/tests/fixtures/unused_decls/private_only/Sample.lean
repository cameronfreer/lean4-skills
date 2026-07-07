-- Fixture: only a `private` decl. The extraction regex intentionally
-- skips access-modifier decls, so TOTAL_DECLS is 0 — but the tree is
-- NOT declaration-free. The shape heuristic must warn and exit 1
-- rather than report the friendly "No declarations found".
private theorem hidden : True := trivial

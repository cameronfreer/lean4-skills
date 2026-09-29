-- Fixture: the pre-fix rg-mode regression. The first theorem is plainly
-- referenced; pre-fix (missing --no-filename), the extraction produced
-- path-prefixed names so the usage search matched nothing and ALL decls
-- were flagged unused. Post-fix: only the last one is flagged.
-- NOTE (#185): comments never count as usages, so the leaf is referenced
-- by a real command (#check); naming dead_thm here is harmless now.
theorem used_thm : True := trivial
def uses_thm := used_thm
#check uses_thm
theorem dead_thm : True := trivial

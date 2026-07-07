-- Fixture: the pre-fix rg-mode regression. The first theorem is plainly
-- referenced; pre-fix (missing --no-filename), the extraction produced
-- path-prefixed names so the usage search matched nothing and ALL decls
-- were flagged unused. Post-fix: only the last one is flagged.
-- NOTE: comments must never name the dead decl — usages in comments
-- are counted by the grep-based analysis (documented limitation).
theorem used_thm : True := trivial
def uses_thm := used_thm
-- second reference so the def above counts as used: uses_thm
theorem dead_thm : True := trivial

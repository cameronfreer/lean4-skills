-- Fixture (mixed_dir): the dead half. The last theorem below is never
-- referenced anywhere in the directory; the shared theorem from
-- Used.lean IS referenced here (cross-file usage counting).
-- NOTE: comments must never name the dead decl — comment usages count.
def uses_shared := shared_thm
-- second reference so the def above counts as used: uses_shared
theorem local_dead : True := trivial

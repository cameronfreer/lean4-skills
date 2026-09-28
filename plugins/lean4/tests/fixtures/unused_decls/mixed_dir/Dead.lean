-- Fixture (mixed_dir): the dead half. The last theorem below is never
-- referenced anywhere in the directory; the shared theorem from
-- Used.lean IS referenced here (cross-file usage counting).
def uses_shared := shared_thm
#check uses_shared
theorem local_dead : True := trivial

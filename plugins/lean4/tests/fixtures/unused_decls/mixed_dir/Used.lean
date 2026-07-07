-- Fixture (mixed_dir): the used half. Cross-file usage — `shared_thm`
-- is defined here and referenced from Dead.lean, exercising the
-- directory-wide usage search.
theorem shared_thm : True := trivial

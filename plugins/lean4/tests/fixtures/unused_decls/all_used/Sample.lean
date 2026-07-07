-- Fixture: every declaration is referenced at least once beyond its
-- definition line. The leaf (`final_thm`) is referenced in the comment
-- below — usages in comments ARE counted (documented limitation of the
-- grep-based analysis), which conveniently lets an all-used fixture
-- exist at all.
theorem base_thm : True := trivial
def uses_base := base_thm
theorem final_thm : True := uses_base
-- final_thm is the exported result: final_thm

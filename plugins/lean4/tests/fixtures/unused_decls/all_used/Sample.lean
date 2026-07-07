-- Fixture: every declaration is referenced at least once beyond its
-- definition line. The leaf (`final_thm`) is referenced by a real Lean
-- command (#check) rather than a comment, so the green path doesn't
-- depend on the comments-count-as-usage limitation.
theorem base_thm : True := trivial
def uses_base := base_thm
theorem final_thm : True := uses_base
#check final_thm

/-- Docstring mentioning doc_only_thm must not count as a usage. -/
theorem real_thm : True := trivial
-- theorem commented_out : True := trivial
theorem doc_only_thm : True := trivial
/- block comment /- nested mentions nested_only -/ still a comment -/
theorem nested_only : True := trivial
def s : String := "string_only and an \"escaped\" quote"
theorem string_only : True := trivial
def ms : String := "multi
line_only_in_string
end"
theorem line_only_in_string : True := trivial
def uses_real := real_thm -- trailing comment naming doc_only_thm
#check uses_real
#check s
#check ms

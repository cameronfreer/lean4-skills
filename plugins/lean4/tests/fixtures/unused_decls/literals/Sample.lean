-- Fixture (#185 review): valid Lean literals the code view must blank
-- WHOLE, without shifting lines. A char literal holding a double quote
-- must not open a string; a raw string must hide its contents; an escaped
-- newline inside a string must stay a newline (dead3 is on line 14).
def quote : Char := '"'
#check quote
def dead : Nat := 0
def text : String := r#"say " dead2 " end"#
#check text
def dead2 : Nat := 0
def s : String := "line one \
dead3 continued"
#check s
def dead3 : Nat := 0

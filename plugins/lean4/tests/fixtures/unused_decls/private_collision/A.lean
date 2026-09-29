-- Fixture (#184): same private name in two files. This copy IS used
-- (file-local counting); the copy in B.lean is not and must be flagged
-- even though the name appears here.
private def helper : Nat := 1
def useA : Nat := helper
#check useA

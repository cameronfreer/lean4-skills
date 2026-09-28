-- Fixture (#185 review): an interpolation `{…}` inside s!"…" / m!"…" is
-- code, not text. `live` is referenced only from interpolations and must
-- count as used; `ghost` appears only in the literal text and must not.
def live : Nat := 7
def ghost : Nat := 0
def message : String := s!"value: {live}"
def note : String := s!"ghost is only text here, \{ghost} too: {live + 1}"
def nested : String := s!"outer {s!"inner {live}"} done"
#check message
#check note
#check nested

-- #169 negative control. This file MUST FAIL to parse: the docstring precedes
-- `omit [...] in`, and Lean reports `unexpected token 'omit'` at the DOCSTRING
-- position (line 7), not at the `omit` line. `run_core_snippets.sh` asserts both.
section
variable [Inhabited Nat]

/-- Doc comment placed before omit. -/
omit [Inhabited Nat] in
theorem bad : True := trivial

end

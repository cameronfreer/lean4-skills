# Formal Pairs (`formal-pair/v1`)

**Status:** format and auditor only, slice 1 of #88. This reference is the contract for `formal-pair/v1` ([schema](formal-pair-schema.json)) and for the read-only auditor `lean4-skills-pair-audit` (`lib/scripts/pair_audit.py`). No command writes or reads pair files yet: `/lean4:review` integration and `/lean4:formalize --emit-artifacts` are later slices of #88.

**Executable evidence:** `lib/scripts/tests/test_pair_audit.py` (schema, cross-field rules, every finding code, exit codes; no Lean) and `tests/integration/test_pair_audit_lean.py` (the same fixture against a pinned toolchain, in the lean-integration workflow).

## What a pair is

A pair links one informal claim (a theorem of a paper, a statement on a page of notes) to the Lean declarations that formalise it, so that a reviewer can check that the formal theorem says what the informal claim meant, and can tell later whether either side moved. A pair file is plain JSON, one per project or per source document:

```json
{
  "schema": "formal-pair/v1",
  "source": {"citation": "Author, Title (year)", "url": "https://…"},
  "claims": [{
    "id": "thm-3.2",
    "locator": "p. 14, Theorem 3.2",
    "informal": "Every finite integral domain is a field.",
    "formal": {"module": "Proj.Section3", "file": "Proj/Section3.lean",
               "declarations": ["Proj.Finite.isField_of_domain"]},
    "status": "proved",
    "relation": "matches",
    "type_hash": {"Proj.Finite.isField_of_domain": "sha256:…"},
    "terminology": [{"source": "integral domain", "lean": "IsDomain"}],
    "notes": "The paper assumes commutativity implicitly."
  }]
}
```

- `formal.module` is the module to import. It is never derived from `formal.file`: the file is a hint, reported when it no longer exists. Declarations are resolved by **name**, so moving a declaration to another file keeps the pair valid and is reported as `moved`.
- `formal` may be omitted only when `status` is `unformalized`.
- `type_hash` records the SHA-256 of each declaration's elaborated type, written by `--update-hashes`.

## Two fields, two questions

`status` says what Lean shows, and the auditor checks it:

| `status` | Meaning | Checked |
|---|---|---|
| `proved` | every declaration closed, standard axioms only | no `sorryAx`, no other axiom |
| `partial` | some declarations still use `sorry` | warns when none does |
| `axiomatized` | relies on declared axioms on purpose | custom axioms reported as info |
| `refuted` | the declarations prove the negation, or a counterexample | custom axioms are errors |
| `unformalized` | no Lean counterpart yet | info |

`relation` says what a human judged when comparing the two statements, and the auditor never sets it: `matches`, `more-general` (the Lean statement is stronger), `weaker` (it covers part of the claim), `source-false` (the informal claim is false as stated; pair it with the counterexample), `hypothesis-added` (Lean needs a hypothesis the source omits), `unchecked`.

They are separate because they change for different reasons: a golf or a refactor can leave `status` at `proved` while the statement changed, and only a human can say whether the new statement still `matches`.

## Running the auditor

```bash
lean4-skills-pair-audit pairs.json --project .          # text summary
lean4-skills-pair-audit pairs.json --project . --json   # pair-audit/v1 report
lean4-skills-pair-audit pairs.json --project . --update-hashes
```

It writes one probe file under `<project>/.lake/pair_audit/`, elaborates it with ONE `lake lean` process (which builds the imports first, so it never reads stale `.olean` files), and removes it. For each declaration the probe records whether it exists, its module, its axioms (`Lean.collectAxioms`, the data behind `#print axioms`) and its elaborated type. Sources are never modified; `--update-hashes` rewrites only the pair file.

| Code | Severity | Meaning |
|---|---|---|
| `declaration-missing` | error | the name is not in the environment |
| `sorry-in-proved` | error | `status: proved` but `sorryAx` among the axioms |
| `nonstandard-axiom` | error (info if `axiomatized`) | axioms outside `propext`, `Quot.sound`, `Classical.choice` |
| `drift` | warning | the elaborated type no longer matches `type_hash`: re-read the pair, then `--update-hashes` |
| `moved` | warning | defined in another module than `formal.module` |
| `stale-path` | warning | `formal.file` does not exist |
| `partial-without-sorry` | warning | consider promoting the claim to `proved` |
| `hash-missing` | info | no `type_hash` recorded yet |
| `relation-unchecked`, `unformalized` | info | counted, for the reviewer |

Exit codes: `0` no error or warning, `1` findings, `2` usage or malformed JSON, `3` schema or cross-field failure, `4` operational (no `lake`, the probe does not elaborate, a declaration got no record).

## Reading a drift warning

Drift means the statement Lean checks is no longer the one a human compared with the informal claim. It is not an error: generalising a lemma or changing an implicit argument causes it. Compare the informal statement with the new type (the `--json` report carries the record), adjust `relation` if needed, then run `--update-hashes`. The hash is taken on the elaborated type, so a change of notation or pretty-printing options does not trigger it; a renamed bound variable or reordered binder does.

## Limits

- Private declarations and names written with `«»` are not resolved.
- The auditor compares the formal side with what the pair file recorded; it does not judge whether the informal and formal statements match.
- The probe imports every module named in the file, so a module that fails to build makes the whole run exit `4`.

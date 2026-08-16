# Mathlib Review Taxonomy

What mathlib reviewers actually ask for, organized into buckets. This is a
**reference**, not review behavior: it does not decide *when* `/lean4:review`
emits a finding — that is [`/lean4:review`](../../../commands/review.md)'s job
(Issue #110). Consult it any time; commands that want to use it selectively
gate their own consumption.

Modern mathlib review is more than surface style — a large fraction is
**library-integration work**: file placement, import hygiene, duplicate
results, weakest assumptions, `@[simp]` choices, instance design, and
generated-file chores. The buckets below name that vocabulary and cross-link
the existing references instead of duplicating them.

**On the category / rule_id / severity tags below:** conceptual review
buckets and machine-readable categories are **not one-to-one** — one bucket
may map to several schema categories. The tags are
*illustrative candidate mappings*, not a schema; they track the provisional
enum in Issue #115
(`style`, `naming`, `docstring`, `module-doc`, `file-placement`,
`import-hygiene`, `api`, `generalization`, `attribute`, `simp`, `instance`,
`module-system`, `metadata`). Only the vacuous-API rule's full triple is
settled — `category: api`, `rule_id: vacuous-api`, `severity: advisory`.
Issue #115 owns the final enums and severity semantics; nothing here freezes
the review schema.

Each bucket lists what reviewers usually mean, cheap fixes, annoying fixes,
and one example from a recent mathlib PR ([mathlib4#33420](https://github.com/leanprover-community/mathlib4/pull/33420), [mathlib4#33443](https://github.com/leanprover-community/mathlib4/pull/33443), [mathlib4#35906](https://github.com/leanprover-community/mathlib4/pull/35906)).

## 1. Surface style

**Reviewers mean:** line width, whitespace, tactic choices, `↦` vs `=>`.
**Cheap:** reflow to 100 chars, fix spacing. **Annoying:** large tactic-block
rewrites. **Example:** [mathlib4#33443](https://github.com/leanprover-community/mathlib4/pull/33443) (100-char fixes). See
[mathlib-style.md](mathlib-style.md). *Candidate:* `category: style`.

## 2. Naming & namespace

**Reviewers mean:** `snake_case` for lemmas/theorems, `UpperCamelCase` for
types, `lowerCamelCase` for functions; dot-notation friendliness; the right
namespace and depth so callers write `X.foo`, not `Foo.X.baz`. **Cheap:**
rename a private lemma. **Annoying:** re-namespacing a public declaration that
callers already use. **Example:** [mathlib4#35906](https://github.com/leanprover-community/mathlib4/pull/35906) (naming discussion). See
[mathlib-style.md § 3 Naming Conventions](mathlib-style.md#3-naming-conventions).
*Candidate:* `category: naming`.

## 3. Documentation

**Reviewers mean:** module and declaration docstrings on public API, a short
proof sketch for genuinely intricate arguments, cross-references, no
development-history language. **Cheap:** add a missing one-line docstring.
**Annoying:** write a real module docstring for a large file. **Example:**
[mathlib4#33420](https://github.com/leanprover-community/mathlib4/pull/33420) (`Add doc-string and some more typos`). Docstring *editing* is
governed by the workflow-scoped policy (Rule A/B/C) in
[SKILL.md](../SKILL.md); review flags and proposes wording but never mutates
(Rule B). What counts as development-history language lives in
[mathlib-style.md § Avoid Development History References](mathlib-style.md#avoid-development-history-references).
*Candidate:* `category: docstring` / `module-doc`.

## 4. File placement / import hygiene

**Reviewers mean:** does an **equivalent or more-general result already
exist** (search first — see [mathlib-guide.md](mathlib-guide.md))? If not,
does the declaration live in the lowest sensible module, with the lightest
reasonable imports? **Cheap:** drop an unused import. **Annoying:** move a
declaration to a new file and fix downstream imports.
**Example:** [mathlib4#33420](https://github.com/leanprover-community/mathlib4/pull/33420) (`Change mathlib imports from OrderType`; review also found declarations/instances that already existed), [mathlib4#35906](https://github.com/leanprover-community/mathlib4/pull/35906)
(rename the file to match the moved declaration, e.g. `SimpleGraph/Walk/Chord.lean`).
*Candidate:* `category: file-placement` / `import-hygiene`.

## 5. API / generalization

**Reviewers mean:** the weakest reasonable hypotheses; `structure` vs a
conjunction; natural generalizations the current form blocks; and whether a
declaration is substantive at all. **Cheap:** remove an obviously unnecessary
hypothesis, or delete an isolated vacuous placeholder. **Annoying:** generalize
or redesign public API and migrate callers, or replace a depended-on
placeholder with a substantive result.

**Vacuous-API rule (absorbs Issue #60).** Flag a **public declaration that
presents as substantive API but whose conclusion collapses to `True` or is
otherwise vacuous** — e.g. `theorem foo ... : ∃ N, ∀ n ≥ N, True`. doc-gen4
renders it identically to a real result, so it silently erodes the API's
credibility. Scope it **semantically, not lexically**: this is *not* "any use
of `True`/`trivial`" (many legitimate statements use them), and it explicitly
does **not** cover `sorry`-scaffolding — the `sorry` linter already flags that.
The **proposed** remedy is delete-or-replace (track the planned result in a
blueprint or comment). Its settled review semantics are **advisory**: when
emitted (by Issue #110), it is a suggestion, never an automatic edit.

```lean
-- ❌ Vacuous: renders as a real theorem in doc-gen4, proves nothing.
/-- Concentration of homomorphism density in sampled graphs. -/
theorem homDensity_concentration (W : Graphon α μ) (ε : ℝ) (hε : ε > 0) :
    ∃ N : ℕ, ∀ n ≥ N, True := ⟨1, fun _ _ => trivial⟩
```

*Mapping (settled):* `category: api`, `rule_id: vacuous-api`, `severity: advisory`
(the broader bucket also maps to `generalization`).
**Example:** [mathlib4#35906](https://github.com/leanprover-community/mathlib4/pull/35906) — the review separated chordlessness from cyclehood, generalized it beyond closed walks, and weighed a bundled vs unbundled representation (`def` vs `structure`), landing `Walk.IsChordless` in `SimpleGraph/Walk/Chord.lean`.

## 6. Attributes / `simp`

**Reviewers mean:** is `@[simp]` globally canonical — an LHS already in simp
normal form (it does not rewrite under the intended set *excluding the
candidate lemma itself*), an RHS that reaches or approaches the chosen normal
form, and no applicable cycle or conflicting rewrite? Is `@[ext]` needed?
Should this be `@[reducible]`? **Cheap:** drop an unjustified `@[simp]`.
**Annoying:** re-derive a simp normal form. **Example:**
[mathlib4#33420](https://github.com/leanprover-community/mathlib4/pull/33420) (`Remove simp tag`, `Adding simp tag`). See
[simp-reference.md](simp-reference.md). *Candidate:* `category: attribute` / `simp`.

## 7. Instances

**Reviewers mean:** diamonds, instance loops, unification hazards, `Prop` vs
`Type` instances. **Cheap:** add a missing `instance` docstring. **Annoying:**
restructure a diamond. **Example:** [mathlib4#33420](https://github.com/leanprover-community/mathlib4/pull/33420) (`Add docs to instance`). See
[instance-pollution.md](instance-pollution.md). *Candidate:* `category: instance`.

## 8. Generated-file / module-system chores

**Reviewers mean:** stale `Mathlib.lean` after add/rename/delete, a missing
`module` header, wrong `public import` vs `import`. **Cheap:** run
`lake exe mk_all`. **Annoying:** convert a file to the module system.
**Example:** [mathlib4#33420](https://github.com/leanprover-community/mathlib4/pull/33420) (`Run mk_all`, `Fix module error`, `Fix Mathlib.lean`).
Shipped tooling covers this end to end: the canonical header in
[mathlib-style.md § 1](mathlib-style.md#1-file-header-copyright-module-imports-critical),
the checkpoint gate in
[checkpoint.md § Generated Root Files gate](../../../commands/checkpoint.md#generated-root-files-gate),
and error triage in
[compilation-errors.md §16–§19](compilation-errors.md#16-cannot-import-non-module-from-module)
(reachable via [`/lean4:diagnose`](../../../commands/diagnose.md)).
*Candidate:* `category: module-system`.

## 9. Metadata / process

**Reviewers mean:** PR title shape, description, labels, dependency
declaration, and move/deletion metadata. **Out of runtime scope today** —
`/lean4:review` has no GitHub PR context — but named so the vocabulary is
complete for future GitHub-aware work. **Cheap:** repair the PR title,
description, labels, dependency declaration, or omitted move/deletion
metadata. **Annoying:** reconstruct move/deletion provenance after a large
refactor. **Example:** [mathlib4#33420](https://github.com/leanprover-community/mathlib4/pull/33420)'s dependency checkbox and standard `Moves:` / `Deletions:` metadata contract.
*Candidate:* `category: metadata`.

## See Also

- [mathlib-guide.md](mathlib-guide.md) — search-before-prove workflow (the
  companion to this review guide)
- [mathlib-style.md](mathlib-style.md) — formatting, naming, headers
- [`/lean4:review`](../../../commands/review.md) — the review command that
  will consume these buckets (Issue #110)

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

**On the category / rule_id / severity tags below:** these are
*illustrative candidate mappings*, not a schema. They keep this taxonomy
aligned with the eventual machine-readable review output. Only
`api` / `vacuous-api` / `advisory` (bucket 5) is settled.
Issue #115 owns the final enums and severity semantics; nothing here freezes
the review schema.

Each bucket lists what reviewers usually mean, cheap fixes, annoying fixes,
and one example from a recent mathlib PR (#33420, #33443, #35906).

## 1. Surface style

**Reviewers mean:** line width, whitespace, tactic choices, `↦` vs `=>`.
**Cheap:** reflow to 100 chars, fix spacing. **Annoying:** large tactic-block
rewrites. **Example:** PR #33443 (100-char fixes). See
[mathlib-style.md](mathlib-style.md). *Candidate:* `category: style`.

## 2. Naming & namespace

**Reviewers mean:** `snake_case` for lemmas/theorems, `UpperCamelCase` for
types, `lowerCamelCase` for functions; dot-notation friendliness; the right
namespace and depth so callers write `X.foo`, not `Foo.X.baz`. **Cheap:**
rename a private lemma. **Annoying:** re-namespacing a public declaration that
callers already use. **Example:** PR #35906 (naming discussion). See
[mathlib-style.md § 3 Naming Conventions](mathlib-style.md#3-naming-conventions).
*Candidate:* `category: naming`.

## 3. Documentation

**Reviewers mean:** module and declaration docstrings on public API, a short
proof sketch for genuinely intricate arguments, cross-references, no
development-history language. **Cheap:** add a missing one-line docstring.
**Annoying:** write a real module docstring for a large file. **Example:**
PR #33420 (`Add doc-string and some more typos`). Docstring *editing* is
governed by the workflow-scoped policy (Rule A/B/C) in
[SKILL.md](../SKILL.md); review flags and proposes wording but never mutates
(Rule B). What counts as development-history language lives in
[mathlib-style.md § Avoid Development History References](mathlib-style.md#avoid-development-history-references).
*Candidate:* `category: docs`.

## 4. File placement / import hygiene

**Reviewers mean:** does the declaration live in the lowest sensible module?
Are the imports heavier than needed? **Cheap:** drop an unused import.
**Annoying:** move a declaration to a new file and fix downstream imports.
**Example:** PR #33420 (`Change mathlib imports from OrderType`), PR #35906
(`rename the file name`). *Candidate:* `category: placement`.

## 5. API / generalization

**Reviewers mean:** the weakest reasonable hypotheses; `structure` vs a
conjunction; natural generalizations the current form blocks.

**Vacuous-API rule (absorbs Issue #60).** Flag a **public declaration that
presents as substantive API but whose conclusion collapses to `True` or is
otherwise vacuous** — e.g. `theorem foo ... : ∃ N, ∀ n ≥ N, True`. doc-gen4
renders it identically to a real result, so it silently erodes the API's
credibility. Scope it **semantically, not lexically**: this is *not* "any use
of `True`/`trivial`" (many legitimate statements use them), and it explicitly
does **not** cover `sorry`-scaffolding — the `sorry` linter already flags that.
The **proposed** remedy is delete-or-replace (track the planned result in a
blueprint or comment); it is surfaced as an **advisory** finding —
never an automatic edit.

```lean
-- ❌ Vacuous: renders as a real theorem in doc-gen4, proves nothing.
/-- Concentration of homomorphism density in sampled graphs. -/
theorem homDensity_concentration (W : Graphon α μ) (ε : ℝ) (hε : ε > 0) :
    ∃ N : ℕ, ∀ n ≥ N, True := ⟨1, fun _ _ => trivial⟩
```

*Mapping (settled):* `category: api`, `rule_id: vacuous-api`, `severity: advisory`.
**Example:** PR #35906 (`IsChordless` as `def` vs `structure`).

## 6. Attributes / `simp`

**Reviewers mean:** is `@[simp]` justified (confluent, terminating, good LHS)?
Is `@[ext]` needed? Should this be `@[reducible]`? **Cheap:** drop an
unjustified `@[simp]`. **Annoying:** re-derive a simp normal form. **Example:**
PR #33420 (`Remove simp tag`, `Adding simp tag`). See
[simp-reference.md](simp-reference.md). *Candidate:* `category: attribute`.

## 7. Instances

**Reviewers mean:** diamonds, instance loops, unification hazards, `Prop` vs
`Type` instances. **Cheap:** add a missing `instance` docstring. **Annoying:**
restructure a diamond. **Example:** PR #33420 (`Add docs to instance`). See
[instance-pollution.md](instance-pollution.md). *Candidate:* `category: instance`.

## 8. Generated-file / module-system chores

**Reviewers mean:** stale `Mathlib.lean` after add/rename/delete, a missing
`module` header, wrong `public import` vs `import`. **Cheap:** run
`lake exe mk_all`. **Annoying:** convert a file to the module system.
**Example:** PR #33420 (`Run mk_all`, `Fix module error`, `Fix Mathlib.lean`).
Shipped tooling covers this end to end: the canonical header in
[mathlib-style.md § 1](mathlib-style.md#1-file-header-copyright-module-imports-critical),
the checkpoint gate in
[checkpoint.md § Generated Root Files gate](../../../commands/checkpoint.md#generated-root-files-gate),
and error triage in
[compilation-errors.md §16–§19](compilation-errors.md#16-cannot-import-non-module-from-module)
(reachable via [`/lean4:diagnose`](../../../commands/diagnose.md)).
*Candidate:* `category: integration`.

## 9. Metadata / process

**Reviewers mean:** PR title shape, description, labels, move/deletion
metadata. **Out of runtime scope today** — `/lean4:review` has no GitHub PR
context — but named so the vocabulary is complete for future GitHub-aware
work. *Candidate:* `category: process`.

## See Also

- [mathlib-guide.md](mathlib-guide.md) — search-before-prove workflow (the
  companion to this review guide)
- [mathlib-style.md](mathlib-style.md) — formatting, naming, headers
- [`/lean4:review`](../../../commands/review.md) — the review command that
  will consume these buckets (Issue #110)

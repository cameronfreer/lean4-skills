# Learning Pathways Reference

## Intent Taxonomy

| Intent | Description | Default formalization-role | Typical modes | Pedagogy focus |
|--------|-------------|--------------------------|---------------|----------------|
| `usage` | Learning Lean syntax, tactics, idioms | `primary` | `repo`, `formalize` | "How do I write this in Lean?" |
| `internals` | Understanding elaboration, macros, metaprogramming | `primary` | `repo` | "How does Lean do this under the hood?" |
| `authoring` | Mathlib authoring patterns, API conventions | `primary` | `mathlib`, `repo` | "How should I structure this for mathlib?" |
| `math` | Understanding mathematical content | `assistive` | `mathlib`, `formalize` | "What does this theorem really say?" |

## Intent-Behavior Matrix

Intent × mode → explanation focus, tool priorities, formalization-role effect.

| Intent | Mode | Focus | Formalization role |
|--------|------|-------|--------------------|
| `math` | `formalize` | Explain the math first, formalize to make it concrete | `assistive` (default) |
| `math` | `formalize` + `role=none` | Coerce mode to `mathlib`; pure conceptual discussion, Lean code suppressed unless user asks | `none` |
| `math` | `mathlib` | Explain theorems conceptually, show mathlib as reference landscape | `assistive` |
| `usage` | `repo` | Walk through code patterns, explain tactic choices | `primary` |
| `usage` | `formalize` | Build the statement, prove it, explain syntax choices | `primary` |
| `authoring` | `mathlib` | Focus on naming, simp lemmas, instance design, API style | `primary` |
| `authoring` | `repo` | Compare local code against mathlib conventions | `primary` |
| `internals` | `repo` | Dive into elaborator, `Term.Elab`, macro expansion | `primary` |

### Inference Rules (when `--intent=auto`)

1. If `--source` is provided: math paper → `math`; `.lean` file → `usage` or `internals`; mathlib doc → `authoring`.
2. From topic phrasing: Lean syntax/tactic keywords → `usage`; elaborator/macro/metaprogramming → `internals`; `Mathlib.` prefix or API-pattern language → `authoring`; natural-language math statement → `math`.
3. If ambiguous → ask.

### Deriving `--formalization-role` (when `auto`)

- `math` → `assistive`
- `usage` / `internals` / `authoring` → `primary`

User can pass `--formalization-role=none` to skip formalization entirely.

## Game Style

Structured progression inspired by NNG, Set Theory Game, etc.

- Requires `--style=game`; optionally `--track=<name>`.
- If no `--track` given, present track picker with descriptions.
- Level structure: each track is 5–10 exercises, progressive difficulty.
- Exercise loop: present → user attempts → verify via `lean_goal` + `lean_multi_attempt` → on failure: offer hint (up to 3) → on success: advance.
- Completion: congratulate, offer next track or free exploration.
- `--formalization-role=none` + `--style=game` → prompt: "Game style requires Lean code. Switch to role=primary, or switch style to exercise?" (do not silently coerce).

## Track Ladders

### nng-like (Natural Numbers)

Prerequisite: none

1. Zero + n = n (induction intro)
2. Succ (a + b) = a + Succ b
3. Addition is commutative
4. Addition is associative
5. Multiplication: 0 * n = 0
6. Multiplication distributes over addition
7. Multiplication is commutative
8. Power: n^0 = 1

### set-theory-like (Sets)

Prerequisite: nng-like or equivalent

1. x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B
2. Intersection and membership
3. Complement and difference
4. Subset transitivity
5. De Morgan's laws for sets

### analysis-like (Epsilon-Delta)

Prerequisite: set-theory-like or equivalent

1. Constant function is continuous
2. Sum of continuous functions
3. Squeeze theorem
4. Limit uniqueness
5. Composition of continuous functions

### proofs-reintro (Logic & Tactics)

Prerequisite: none

1. Implication: P → Q
2. And: P ∧ Q
3. Or: P ∨ Q
4. Negation and contradiction
5. Exists and forall
6. Classical reasoning

## Source Handling

### Supported source types

- `.lean` file: `Read` directly. Infer `--intent=usage` or `internals`.
- `.pdf` file: `Read` (PDF support). For large PDFs, read abstract/introduction/theorem-statement sections first, then ask user which section to focus on. Infer `--intent=math`.
- URL: use available web fetch tool. If unavailable or content too large, ask user to paste relevant excerpt. Infer intent from content type.
- Unsupported type: warn + ask user for text excerpt.

### Source ingestion flow

1. Read/fetch source content.
2. Extract key definitions, theorem statements, notation.
3. Summarize main results at user's `--level`.
4. Use extracted content as seed for the resolved mode's discovery step.
5. On failure (unreadable, too large, fetch blocked): ask user for relevant excerpt and proceed with that.

## Formalization-Role Semantics

| Role | Behavior | When |
|------|----------|------|
| `none` | No formalization. Suppresses Lean code output by default unless user explicitly asks. If `--mode=formalize`, coerce to `mathlib` with warning. If `--style=game`, prompt user to switch role or style. | User wants concepts only. |
| `assistive` | Formalization supports explanation. Show Lean to make abstract concrete, but prioritize narrative. | `--intent=math` default. |
| `primary` | Formalization IS the objective. Build statement, prove it, explain the proof. | `--intent=usage/internals/authoring` default. |
| `auto` | Infer from intent. Always announce inferred choice. | Default for all intents. |

## Learning Profile

Persisted within the current conversation only (not across new sessions).

- Established at Step 0 of first invocation.
- Reused on subsequent turns within the same conversation.
- Explicit flags on any turn override and update the profile.
- Precedence: explicit flags (this turn) > stored profile (prior turns) > inference.
- New conversation = fresh profile (no cross-session persistence).

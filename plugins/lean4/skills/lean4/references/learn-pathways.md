# Learning Pathways Reference

## Intent Taxonomy

| Intent | Description | Default presentation | Typical modes | Pedagogy focus |
|--------|-------------|---------------------|---------------|----------------|
| `usage` | Learning Lean syntax, tactics, idioms | `formal` | `repo`, `formalize` | "How do I write this in Lean?" |
| `internals` | Understanding elaboration, macros, metaprogramming | `formal` | `repo` | "How does Lean do this under the hood?" |
| `authoring` | Mathlib authoring patterns, API conventions | `formal` | `mathlib`, `repo` | "How should I structure this for mathlib?" |
| `math` | Understanding mathematical content | `informal` | `mathlib`, `formalize` | "What does this theorem really say?" |

## Intent-Behavior Matrix

Intent × mode → explanation focus, tool priorities, presentation effect.

| Intent | Mode | Focus | Presentation |
|--------|------|-------|--------------|
| `math` | `formalize` | Explain the math first, formalize to make it concrete | `informal` (default): Lean runs silently, results shown as prose |
| `math` | `mathlib` | Explain theorems conceptually, show mathlib as reference landscape | `informal` (default) |
| `usage` | `repo` | Walk through code patterns, explain tactic choices | `formal` (default) |
| `usage` | `formalize` | Build the statement, prove it, explain syntax choices | `formal` (default) |
| `authoring` | `mathlib` | Focus on naming, simp lemmas, instance design, API style | `formal` (default) |
| `authoring` | `repo` | Compare local code against mathlib conventions | `formal` (default) |
| `internals` | `repo` | Dive into elaborator, `Term.Elab`, macro expansion | `formal` (default) |

All combinations are valid. No mode/presentation pair requires coercion.

### Inference Rules (when `--intent=auto`)

1. If `--source` is provided: math paper → `math`; `.lean` file → `usage` or `internals`; mathlib doc → `authoring`.
2. From topic phrasing: Lean syntax/tactic keywords → `usage`; elaborator/macro/metaprogramming → `internals`; `Mathlib.` prefix or API-pattern language → `authoring`; natural-language math statement → `math`.
3. If ambiguous → ask.

### Deriving `--presentation` (when `auto`)

- `math` → `informal`
- `usage` / `internals` / `authoring` → `formal`

If confidence is high, auto-resolve and announce. If ambiguous, ask: "Informal (prose, Lean-backed), supporting (prose + Lean snippets), or formal (Lean shown)?"

## Two-Layer Architecture

### Backing layer (internal)

Lean verification is attempted by default for all key claims. Lean tools (`lean_goal`, `lean_multi_attempt`, `lean_diagnostic_messages`) run regardless of `--presentation`. The backing layer is invisible to the user unless they request it via "show Lean backing" in the depth-check menu.

### Presentation layer (user-facing)

`--presentation` controls what the user sees, not whether Lean runs.

| Presentation | User sees | Lean backing |
|-------------|-----------|--------------|
| `informal` | Prose and math notation only. No Lean syntax unless user asks via "show Lean backing." | Runs silently. |
| `supporting` | Prose-first with selective Lean snippets where they clarify. | Runs; shown where illustrative. |
| `formal` | Lean is the primary medium. User reads and writes Lean. | Runs; shown directly. |
| `auto` | Inferred from intent. Announced with override option. | Always runs. |

### Key claims (verification scope)

Lean verification is attempted for: theorem statements, correctness judgments (e.g., "this proof is valid"), game pass/fail decisions, and any "therefore X is true" assertions. Contextual commentary ("this technique is common in analysis") is not a key claim and does not require verification.

## Verification Status

Every key-claim step carries one of:

| Status | Meaning | Display |
|--------|---------|---------|
| `[verified]` | Lean-checked via `lean_goal`/`lean_diagnostic_messages`. | Step-level label. |
| `[partially-verified]` | Some subclaims checked, others pending. | Step-level label. |
| `[unverified]` | Explanation only — no Lean check completed. | Step-level label. |

Labels are per step, not per sentence, to avoid noise.

### `--verify=best-effort`

Attempt verification for all key claims. If verification fails or is unavailable, label the output with its status, note the reason, and continue.

### `--verify=strict`

Never present claims as settled unless `[verified]`. If verification is unavailable or fails after retry:
1. Mark the claim `[unverified]` / blocked.
2. Do not present as settled.
3. Require user choice: continue conceptually, or relax to `best-effort`.

### Verification failure transparency

If Lean verification fails: attempt to revise the claim/proof. If revision also fails, state that verification is pending/failed and offer: continue conceptually, or switch to formal mode for manual verification. Never silently swallow a verification failure.

## Game Style

Structured progression inspired by NNG, Set Theory Game, etc.

- Requires `--style=game`; optionally `--track=<name>`.
- If no `--track` given, present track picker with descriptions.
- Level structure: each track is 5–10 exercises, progressive difficulty.
- Verification is always Lean-backed (`lean_goal` + `lean_multi_attempt` + clean `lean_diagnostic_messages`), regardless of `--presentation`.
- **Formal game** (`--presentation=formal`): user writes Lean tactic proofs directly (NNG-style).
- **Supporting game** (`--presentation=supporting`): user argues informally; agent restates interpretation, translates to Lean, checks, then shows the Lean translation after verification as illustration.
- **Informal game** (`--presentation=informal`): user argues informally; agent restates its interpretation of the argument ("I interpret your argument as: ...") before translating to Lean and checking. Result reported in prose unless user asks "show Lean backing."
- Exercise loop: present → user attempts → (if informal or supporting: restate interpretation →) verify → on failure: offer hint (up to 3) → on success: advance.
- Completion: congratulate, offer next track or free exploration.

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
- `.md` / `.txt` file: `Read` directly. Infer intent from content.
- URL: use available web fetch tool. If unavailable or content too large, ask user to paste relevant excerpt. Infer intent from content type.
- Other types: warn + ask user for text excerpt.

### Source ingestion flow

1. Read/fetch source content.
2. Extract key definitions, theorem statements, notation.
3. Summarize main results at user's `--level`.
4. Use extracted content as seed for the resolved mode's discovery step.
5. On failure (unreadable, too large, fetch blocked): ask user for relevant excerpt and proceed with that.

## Learning Profile

Persisted within the current conversation only (not across new sessions).

- Fields: {intent, presentation, verify, style, track, level}. `--source` is **per-invocation only** — not persisted unless user explicitly says "continue same source."
- Established at Step 0 of first invocation.
- Reused on subsequent turns within the same conversation.
- Explicit flags on any turn override and update the profile.
- Precedence: explicit flags (this turn) > stored profile (prior turns) > inference.
- New conversation = fresh profile (no cross-session persistence).

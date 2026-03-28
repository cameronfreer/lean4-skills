# Learning Pathways Reference

Shared reference for `/lean4:learn`, `/lean4:draft`, and `/lean4:formalize`. "Formalize" below refers to the `/lean4:formalize` command (formerly `--mode=formalize` in learn).

## Intent Taxonomy

| Intent | Description | Default presentation | Typical command/mode | Pedagogy focus |
|--------|-------------|---------------------|----------------------|----------------|
| `usage` | Learning Lean syntax, tactics, idioms | `formal` | `learn --mode=repo`, `/lean4:formalize` | "How do I write this in Lean?" |
| `internals` | Understanding elaboration, macros, metaprogramming | `formal` | `learn --mode=repo` | "How does Lean do this under the hood?" |
| `authoring` | Mathlib authoring patterns, API conventions | `formal` | `learn --mode=mathlib`, `learn --mode=repo` | "How should I structure this for mathlib?" |
| `math` | Understanding mathematical content | `informal` | `learn --mode=mathlib`, `/lean4:formalize` | "What does this theorem really say?" |

## Intent-Behavior Matrix

Intent × command/mode → explanation focus, tool priorities, presentation effect.

| Intent | Command / Mode | Focus | Presentation |
|--------|----------------|-------|--------------|
| `math` | `/lean4:formalize` | Explain the math first, formalize to make it concrete | `informal` (default): Lean runs silently, results shown as prose |
| `math` | `mathlib` | Explain theorems conceptually, show mathlib as reference landscape | `informal` (default) |
| `usage` | `repo` | Walk through code patterns, explain tactic choices | `formal` (default) |
| `usage` | `/lean4:formalize` | Build the statement, prove it, explain syntax choices | `formal` (default) |
| `authoring` | `mathlib` | Focus on naming, simp lemmas, instance design, API style | `formal` (default) |
| `authoring` | `repo` | Compare local code against mathlib conventions | `formal` (default) |
| `internals` | `repo` | Dive into elaborator, `Term.Elab`, macro expansion | `formal` (default) |

All combinations are valid. No mode/presentation pair requires coercion. Learn routes natural-language math claims to `/lean4:formalize` (or `/lean4:draft` for skeleton-only); it does not enter formalize mode itself.

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

Structured progression inspired by the Natural Number Game and Set Theory Game.

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

Inspired by the [Natural Number Game](https://adam.math.hhu.de/#/g/hhu-adam/NNG4) by Kevin Buzzard and Mohammad Pedramfar. Lean 4 game infrastructure builds on later work by Patrick Massot, Alexander Bentkamp, and Jon Eugster.

On first entry per session, tell the learner: "Inspired by the Natural Number Game by Kevin Buzzard and Mohammad Pedramfar."

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

Inspired by Daniel J. Velleman's [Set Theory Game](https://adam.math.hhu.de/#/g/djvelleman/STG4), with Lean 4 game-development contributions credited in recent teaching literature to Alexander Bentkamp, Jon Eugster, and Patrick Massot.

On first entry per session, tell the learner: "Inspired by Daniel J. Velleman's Set Theory Game."

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

## Pedagogical Self-Debate

This mechanism turns `/lean4:learn` from a static Q&A into an adaptive tutor. Without it, each reply uses the same style regardless of how the learner is doing. With it, learn reads what a response reveals — confidence, confusion, repeated mistakes, disengagement — and adjusts before replying. The concrete effects: graduated hint escalation in game mode instead of "try again!" loops, automatic approach-switching when the same explanation fails twice, and mid-session difficulty adjustment that respects explicit user choices.

After receiving a user response and before formulating a reply, `/lean4:learn` internally reasons from three advisor perspectives to select the best response strategy. This runs inside the iterate loop (step 5 in `learn.md`).

### Debate State

The debate maintains lightweight structured state across turns (not persisted across conversations):

| Field | Type | Description |
|-------|------|-------------|
| `stuck_count` | int | Consecutive turns where the same misunderstanding appears. Reset on topic change or successful resolution. |
| `misconceptions` | list of `{concept, framing_that_failed, framing_that_resolved}` | Scoped by concept/topic — a tactic misunderstanding does not pollute an unrelated analysis topic. |
| `signal` | `engaged` \| `confused` \| `frustrated` \| `bored` | Inferred from response patterns: short/disengaged → bored; repeated errors → frustrated; tentative → confused; confident + correct → engaged. |
| `last_strategy` | strategy name | The strategy used on the previous turn. See [Named Strategies](#named-strategies). |
| `strategy_effectiveness` | `effective` \| `ineffective` \| `unknown` | Whether `last_strategy` resolved the issue. `ineffective` if the same problem recurs; `effective` if the learner advances. |
| `failure_count` | int | Per-exercise failure count for hint escalation (game mode only). Reset when exercise changes. |

State is updated after each user response, before the advisors run. Advisors read the state to inform their recommendations.

### Named Strategies

Each advisor picks from a fixed set of named strategies. This makes transitions explicit and trackable via `last_strategy`.

| Strategy | Description | Typical trigger |
|----------|-------------|-----------------|
| `stay_course` | Continue current approach | Learner is engaged and progressing |
| `hint` | Give a directional hint without revealing the answer | 1st failure in game mode |
| `worked_example` | Present a fully worked example within the current style | Learner stuck on abstract explanation |
| `prereq_reminder` | Surface a prerequisite concept | Misunderstanding rooted in a gap |
| `counterexample` | Present a minimal counterexample to isolate a misconception | Learner holds a false belief |
| `switch_style` | Change `style` (e.g., socratic → exercise) | Disengagement or repeated failure in current style |
| `raise_level` | Increase difficulty | Consistent evidence of mastery (see confidence rule) |
| `lower_level` | Decrease difficulty | Consistent evidence of struggle (see confidence rule) |
| `reveal_answer` | Show the full answer with explanation | 3rd failure in game mode |

Advisors propose strategies by name. The tiebreak rule picks one. `last_strategy` is updated after the reply.

### The Three Advisors

| Advisor | Question it asks | Signals it looks for |
|---------|-----------------|----------------------|
| **Pace Advisor** | Is the learner ready to advance, or do they need consolidation? | Correct but tentative → consolidate. Confident and correct → advance. Repeated same error → slow down or switch. |
| **Method Advisor** | Is the current style still right, or should we switch? | Disengaged in socratic → try tour. Bored in tour → try exercise. Struggling in formal → try informal/intuitive framing. |
| **Depth Advisor** | Should I go deeper, surface a related concept, or redirect? | If they asked a tangential question → surface and redirect. If they're close to a subtlety → go deeper. If they're overwhelmed → redirect to main thread. |

### Picking a Strategy

After each advisor generates a candidate response approach, pick the one best aligned with:
- The learner's current profile (`{intent, level, style, track}`)
- What the current response concretely revealed

**Tiebreak:** when advisors conflict, prioritize the learner's momentum — keeping them engaged beats completeness. Secondary tiebreak: prefer the advisor whose concern is most time-sensitive (e.g., stuck detection outranks a style suggestion).

**Example — advisors disagree:** The user gave an incorrect proof for exercise 3 (2nd attempt). Pace says "slow down, consolidate prerequisites." Method says "present a worked example (still socratic, but show the solution path instead of asking more questions)." Depth says "go deeper on the specific subtlety they missed." Momentum tiebreak picks Method — a worked example re-engages the learner while also addressing the gap. Pace's concern (consolidation) is served by the worked example itself. Note: `worked_example` is a framing change within the current style, not a style switch — it does not modify the Learning Profile.

### Summary Note Visibility

The debate is always internal reasoning. Whether the `*Pedagogy: ...*` note is user-visible depends on `--presentation`:

| Presentation | Note shown? |
|-------------|-------------|
| `informal` | Yes — one sentence before the reply |
| `supporting` | Yes — one sentence before the reply |
| `formal` | No — suppressed by default (code-first output). Surface only on request ("show Lean backing" or "why did the approach change?") |

> *Pedagogy: [chosen strategy — e.g., "Hinting rather than revealing since you're close" or "Switching to a worked example since you've been stuck on the same concept twice."]*

When `--level=expert` and `--style=tour`, the note may be omitted for straightforward navigation responses to avoid being patronizing.

### When to Run

| Style | Debate required? |
|-------|-----------------|
| `game` | Always (mandatory) |
| `socratic` | Always (mandatory) |
| `exercise` | On substantive user responses; skip for trivial menu picks |
| `tour` | Skip for trivial navigation; run when user asks a question or expresses confusion |

### Profile Updates Mid-Session

The debate may update `style` or `level` in the Learning Profile, but **only for values that were inferred or defaulted** — never override an explicit user flag. If the user ran `--style=socratic` and the debate thinks exercise mode would be better, it must suggest the change and wait for user confirmation rather than silently switching.

For inferred/default values, update and announce inline:

> *Pedagogy: Raising level to `expert` since your questions show strong prior familiarity; switching style to `exercise` to keep you engaged.*

For explicit values, suggest instead:

> *Pedagogy: You seem comfortable with this material — would you like to switch from socratic to exercise mode?*

**Confidence threshold:** Only suggest or apply profile changes after consistent evidence across 2+ turns — not on a single strong signal. One expert-level question from a beginner may be a lucky guess or a narrow prior; two consecutive expert-level responses are a pattern. Similarly, one confused response does not justify lowering the level — wait for the pattern to repeat.

### Adaptive Control

`--adaptive` controls whether the debate can make profile-level changes (style, level). It does not disable the debate itself.

| Setting | What's allowed | What's suppressed |
|---------|---------------|-------------------|
| `on` (default) | All debate behaviors: profile updates (for inferred values), strategy switches, stuck remediation, hint escalation | Nothing |
| `off` | Within-style remediation: hint escalation (game), framing switches (counterexample, worked example, prereq surface), stuck detection | Profile modifications: `switch_style`, `raise_level`, `lower_level`, any write to the Learning Profile's `style` or `level` fields |

Key distinction: remediation changes *how* the debate teaches within the locked style (e.g., trying a counterexample instead of repeating an explanation, or presenting a worked example while remaining in socratic mode). Profile changes alter *which* style or level is active. `--adaptive=off` permits the former and blocks the latter. `worked_example` is a framing change (remediation), not a style switch — it changes the delivery method within the current style, not the style itself.

`--adaptive` persists in the Learning Profile across turns. Explicit `--adaptive=on` on a later turn re-enables full adaptivity.

### Stuck Detection

If the user's last 2 responses reveal the **same misunderstanding**, the debate MUST flag this and the chosen strategy MUST switch approach — not repeat the same explanation. Options:
- Change framing (intuitive → formal, or vice versa)
- Surface a prerequisite concept
- Present a minimal counterexample to isolate the misconception
- In `game` mode: escalate hint level (see below)

**Misconception journal:** Track observed misconceptions scoped by concept — a tactic misunderstanding (e.g., confusing `simp` with `norm_num`) does not pollute an unrelated analysis topic (e.g., epsilon-delta). When a new stuck event occurs on a concept, consult prior resolutions for that concept to avoid re-trying approaches that already failed. E.g., if switching to formal framing resolved a `simp` misconception earlier, prefer that framing again for similar tactic gaps.

### Hint Escalation Protocol (game mode)

When the user fails an exercise, follow the escalation ladder from the 1st failure. The Pace Advisor must flag repeated failure (2+) and may suggest regressing to an easier level:

| Failure count | Response strategy |
|--------------|------------------|
| 1st failure | Affirm attempt, give directional hint (no answer) |
| 2nd failure | More specific hint: name the relevant tactic/lemma/concept |
| 3rd failure | Show the full answer with step-by-step explanation |
| After 3rd | Post-reveal recovery (see below), then offer: regress to an easier level or continue to next exercise |

Never skip levels in the escalation ladder within a single exercise session. Reset the counter when the exercise changes.

### Post-Reveal Recovery (game mode)

After showing the full answer (3rd failure), do not immediately advance. The learner must demonstrate engagement with the revealed answer before moving on. These are follow-up actions within `reveal_answer`, not separate strategies:

1. **Variation problem**: present a closely related exercise that tests the same concept with different values or a minor twist.
2. **Reflection check**: ask the learner to explain in their own words why the answer works (informal) or to identify the key tactic/lemma (formal/supporting).

Pick whichever fits the current `--presentation`. If the learner passes, advance normally. On failure: if the recovery was a variation problem, treat it as a new exercise with its own escalation ladder (reset `failure_count`); if the recovery was a reflection check, provide the correct explanation, then fall through to a variation problem before advancing (reset `failure_count` for the variation). This prevents the hint ladder from ending in passive consumption.

### No Lean Verification

The self-debate step reasons about teaching strategy only. It must not trigger new Lean tool calls (`lean_goal`, `lean_multi_attempt`, etc.) — those belong to the verification layer (step 3 / game verification). Use already-discovered information.

## Learning Profile

Persisted within the current conversation only (not across new sessions).

- Fields: {intent, presentation, verify, style, track, level, adaptive}. `--source` is **per-invocation only** — not persisted unless user explicitly says "continue same source."
- Established at Step 0 of first invocation.
- Reused on subsequent turns within the same conversation.
- Explicit flags on any turn override and update the profile.
- Precedence: explicit flags (this turn) > stored profile (prior turns) > inference.
- New conversation = fresh profile (no cross-session persistence).

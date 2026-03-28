---
name: learn
description: Interactive teaching and mathlib exploration
user_invocable: true
---

# Lean4 Learn

Interactive teaching and mathlib exploration. Adapts to beginner, intermediate, and expert audiences.

## Usage

```
/lean4:learn                                 # Start conversational discovery
/lean4:learn Finset.sum                      # Auto-detect mode from topic
/lean4:learn --mode=repo                     # Explore current project
/lean4:learn --mode=mathlib topology         # Navigate mathlib for a topic
/lean4:learn --style=socratic --interactive  # True Socratic method
/lean4:learn --style=game --track=nng-like   # Game-style natural numbers track
/lean4:learn --source ./paper.pdf            # Learn from a paper/PDF
/lean4:learn --presentation=informal "Bolzano-Weierstrass"  # Prose, Lean-backed
/lean4:learn --output=scratch                # Write results to scratch file
/lean4:learn --style=socratic --adaptive=off  # Socratic, no style/level drift
```

## Inputs

| Arg | Required | Default | Description |
|-----|----------|---------|-------------|
| topic | no | — | Free-text topic, theorem name, file path, or natural-language claim. If omitted, start conversational discovery; set `--mode` after first user reply. |
| --mode | no | `auto` | `auto` \| `repo` \| `mathlib` |
| --level | no | `intermediate` | `beginner` \| `intermediate` \| `expert` |
| --scope | no | `auto` | `auto` \| `file` \| `changed` \| `project` \| `topic` |
| --style | no | `tour` | `tour` \| `socratic` \| `exercise` \| `game` |
| --output | no | `chat` | `chat` \| `scratch` \| `file` |
| --out | no | — | Output path. Required when `--output=file`; hard error if missing. |
| --overwrite | no | `false` | Allow overwriting existing files with `--output=file`. Without flag, existing target → hard error. |
| --interactive | no | `false` | True Socratic method (withhold answers, ask questions). Valid only with `--style=socratic`; ignored with warning otherwise. |
| --intent | no | `auto` | `auto` \| `usage` \| `internals` \| `authoring` \| `math`. See [learn-pathways.md](../skills/lean4/references/learn-pathways.md#intent-taxonomy). |
| --presentation | no | `auto` | `informal` \| `supporting` \| `formal` \| `auto`. Controls user-facing display, not Lean backing. See [learn-pathways.md](../skills/lean4/references/learn-pathways.md#two-layer-architecture). |
| --verify | no | `best-effort` | `best-effort` \| `strict`. Verification strictness for key claims. See [learn-pathways.md](../skills/lean4/references/learn-pathways.md#verification-status). |
| --track | no | — | Exercise ladder: `nng-like` \| `set-theory-like` \| `analysis-like` \| `proofs-reintro`. Valid only with `--style=game`. See [learn-pathways.md](../skills/lean4/references/learn-pathways.md#track-ladders). |
| --source | no | — | File path, URL, or PDF to seed learning. See [learn-pathways.md](../skills/lean4/references/learn-pathways.md#source-handling). |
| --adaptive | no | `on` | `on` \| `off`. Controls whether the debate can change style/level. See [learn-pathways.md](../skills/lean4/references/learn-pathways.md#adaptive-control). |

### Scope defaults by mode (when `--scope=auto`)

| Mode | Default scope |
|------|--------------|
| `repo` | `file` |
| `mathlib` | `topic` |
### Scope coercions

- `--mode=mathlib` + `--scope=file|changed|project` → warn + coerce to `topic`, unless topic resolves to a local declaration

### Output validation

- `--output=file` without `--out` → hard error
- `--output=scratch` → `.scratch/lean4/learn-<timestamp>.lean` (workspace-local). Auto-create `.scratch/lean4/` if missing; warn if `.scratch/` is not in `.gitignore`.
- `--output=file` with existing target and no `--overwrite` → hard error

### Flag validation

- `--intent`, `--presentation`, or `--verify` with invalid value → hard error.
- `--track` without `--style=game` → warn + ignore. `--style=game` without `--track` → prompt track picker.
- `--source` + `--scope=file|changed|project` → warn "source overrides scope for initial discovery". Unsupported source type → warn + ask for text excerpt.
- `--adaptive` with invalid value → hard error. `--adaptive=off` freezes the Learning Profile: the debate cannot change `style` or `level`. Within-style remediation (hint escalation, trying a counterexample instead of repeating an explanation) is unaffected — those don't modify the profile.

## Actions

### 0. Intent Intake

**Two-layer contract:** All modes are Lean-backed by default. Lean verification is attempted for all key claims — theorem statements, correctness judgments, game pass/fail, and "therefore X" assertions. `--presentation` controls what is shown, not whether Lean runs. Each key-claim step carries a verification label: `[verified]`, `[partially-verified]`, or `[unverified]`. Under `--verify=strict`, never present claims as settled unless verified; on failure after retry, mark blocked and offer: continue conceptually or relax to `best-effort`. See [learn-pathways.md](../skills/lean4/references/learn-pathways.md#two-layer-architecture).

Classify learning intent and establish a session Learning Profile: {intent, presentation, verify, style, track, level, adaptive}. `--source` is per-invocation only (not persisted) unless user explicitly says "continue same source." Explicit flags are used directly; inference is only for `auto` values. **Announce** resolved intent and presentation, marking each as inferred or explicit. When `--presentation=auto`: if confidence is high, auto-resolve and announce; if ambiguous, ask: "Informal (prose, Lean-backed), supporting (prose + Lean snippets), or formal (Lean shown)?" Profile persists within the current conversation; explicit flags on later turns override and update it. Precedence (applied before validation rules): explicit flags > stored profile > inference. If explicit `--intent` conflicts with source-inferred intent, honor explicit and warn about mismatch. If explicit `--mode` conflicts with resolved intent (explicit or inferred), honor explicit mode and warn. See [learn-pathways.md](../skills/lean4/references/learn-pathways.md#intent-behavior-matrix) for inference rules and the full behavior matrix.

### 1. Mode Resolution

When `--mode=auto`, resolve by tie-breaking order:

1. If topic resolves to an existing `.lean` file path → `repo`
2. Resolve topic against project-local declarations (via `Grep`/`$LEAN4_SCRIPTS/find_usages.sh`). **Local wins** — if both local and mathlib match, prefer local → `repo`
3. Check mathlib namespace/theorem names (via `lean_local_search`, `lean_leanfinder`/`lean_leansearch`, `lean_loogle`) → `mathlib`
4. If topic is a natural-language mathematical statement → suggest `/lean4:formalize`
5. If ambiguous → ask the user

When no topic is provided, enter conversational discovery and set `--mode` after the user's first reply.

**Intent bias:** After tie-breaking, cross-check against intent. `--intent=math` biases toward `/lean4:formalize` — suggest it, do not enter formalize mode. `--intent=internals` biases toward `repo`. If bias conflicts with tie-breaking and no explicit `--mode`, ask the user.

### 2. Discovery (per mode)

**repo:** `Glob`/`Grep` (file survey) → `Read` (targeted content) → `$LEAN4_SCRIPTS/find_usages.sh` (dependency pass). Build a map: key files, declarations, dependency flow, where proofs live.

**mathlib:** `lean_local_search` → one semantic search (`lean_leanfinder` for goal/proof-state shaped queries, `lean_leansearch` for natural-language concept queries) → `lean_loogle` (type-pattern gaps). Present canonical lemmas, type signatures, minimal usage examples.

**Source-aware:** When `--source` is provided, ingest first: `.lean` → `Read`; PDF → `Read` (for large PDFs, read abstract/intro/theorems first, ask which section); `.md`/`.txt` → `Read` directly; URL → web fetch (if unavailable, ask user for excerpt); other types → warn + ask for text excerpt. Extract key definitions, theorem statements, notation. Use as seed for the resolved mode's discovery. On ingestion failure: ask user for relevant excerpt and proceed.

**Fallback rule:** If a tool is unavailable or rate-limited, continue with the next tool in order, label affected output `[unverified]` or `[partially-verified]`, and note the fallback. If Lean verification fails after retry: attempt to revise; if revision also fails, state that verification is pending/failed and offer: continue conceptually or switch to formal mode.

### 3. Explanation

Present findings at the user's `--level` in the user's `--style`:

- **tour:** Narrated walkthrough, explains as it goes.
- **socratic:** Guided discovery with prompts. If `--interactive`, withhold answers and ask user questions first — delay direct solutions until user has engaged.
- **exercise:** Present a challenge, let user attempt, then explain. Always end with a Lean-verified reference solution.
- **game:** Structured progression through `--track` levels. Verification is always Lean-backed (`lean_goal` + `lean_multi_attempt` + clean `lean_diagnostic_messages`). In `informal`: user argues informally; agent restates its interpretation before checking, reports result without showing Lean unless asked. In `supporting`: user argues informally; agent shows the Lean translation after verification. In `formal`: user writes Lean proofs directly. If no `--track`, present track picker. See [learn-pathways.md](../skills/lean4/references/learn-pathways.md#game-style).

### 4. Depth Check

Offer the depth-check menu:

- show source / show proof state / show alternative approach
- **show Lean backing** (on-demand transparency into the verification layer)
- go deeper / switch mode / broaden scope
- **draft a skeleton** → suggest `/lean4:draft` (skeleton only)
- **formalize a specific result** → suggest `/lean4:formalize` (draft + prove)
- **save to scratch** / **write to file** (mid-session output actions — `--output` is part of the loop, not just startup config)

### 5. Pedagogical Self-Debate

Without this step, learn responds in whatever style was set at the start — if a learner is struggling, it keeps explaining the same way; if they're bored, it doesn't notice. This step makes learn adaptive: it reads what the user's response reveals about their understanding and adjusts pace, method, and depth before each reply.

After receiving the user's response (answer attempt, question, menu choice, or freeform message) and before formulating a reply, reason from three advisor perspectives to choose the best response strategy:

- **Pace Advisor**: "Is the learner ready to advance, or do they need consolidation? What does their response reveal about their current understanding level?"
- **Method Advisor**: "Is the current style still right, or should we switch? Would a different framing (intuitive vs. formal vs. example-driven) serve them better here?"
- **Depth Advisor**: "Should I go deeper on this subtlety, surface a related concept, or redirect? Am I risking overloading them?"

Pick the best strategy based on the learner's current profile (`{intent, level, style, track}`) and what their response revealed. **Tiebreak:** prioritize the learner's momentum (keep them engaged) over completeness.

The debate is internal reasoning. Whether the strategy note is surfaced depends on `--presentation`:

- **`informal` / `supporting`:** Show a one-sentence `*Pedagogy: ...*` note before the reply.
- **`formal`:** Suppress the note by default (code-first output). Surface only if the user requests it via "show Lean backing" or asks why the approach changed.

> *Pedagogy: [one sentence — e.g., "Hinting rather than revealing since you're close" or "Switching to a worked example since you've been stuck on the same concept twice."]*

**When to run:**
- **Mandatory** in `--style=game` and `--style=socratic` modes.
- **Optional** (skip for trivial menu navigation) in `--style=tour` and `--style=exercise` modes.
- When `--level=expert` and `--style=tour`, may be omitted for straightforward navigation responses.

**Key constraints:**
- Do NOT trigger new Lean verification here — reason about teaching strategy only, using already-discovered information.
- In `--style=game`: follow the hint escalation ladder from the 1st failure (directional hint → specific hint → full answer with explanation). The Pace Advisor must flag repeated failure (2+) and may offer to regress to an easier level.
- If the user's last 2 responses reveal the same misunderstanding, the debate MUST flag this and the chosen strategy MUST switch approach.
- The debate may suggest `style` or `level` updates mid-session, but only for values that were inferred or defaulted. If the user explicitly set a flag (e.g., `--style=socratic`), the debate must not override it — instead, suggest the change and let the user confirm.
- When `--adaptive=off`, the debate must not modify `style` or `level` in the Learning Profile. Within-style remediation (hint escalation, framing switches, counterexamples) is unaffected — the debate adapts how it teaches within the locked style, but cannot change which style or level is active.

See [Pedagogical Self-Debate](../skills/lean4/references/learn-pathways.md#pedagogical-self-debate) for the full reference.

### 6. Iterate

After step 5, respond using the chosen strategy. Return to step 4 (Depth Check) for the next turn. In `exercise` mode, the next exercise replaces the depth-check menu as the primary loop driver. On mode switch or topic change, return to step 2 (Discovery). Continue until the user is satisfied or switches mode.

## Output

Output format follows `--presentation`: `informal` → prose with math notation (no Lean blocks unless user requests "show Lean backing"); `supporting` → prose with selective Lean snippets; `formal` → Lean code blocks as primary content. In `scratch` or `file` mode, additionally write a `.lean` file regardless of presentation.

## Safety

- **Read-only by default.** `repo` and `mathlib` modes never write files unless `--output` requests it.
- **No silent mutations.** Prefer LSP tools (`lean_goal`) over file writes for compilation checks. If LSP unavailable and temp file needed for internal compilation, write only under `/tmp/lean4-learn/`, auto-cleanup after use, warn user before writing.
- **No commits.** `/learn` never commits. `--output=file` writes but does not stage or commit.
- **Path restriction.** User-requested outputs (`--output=file`, `--output=scratch`) restricted to workspace root (scratch uses `.scratch/lean4/`). Reject path traversal (`../`) or absolute paths outside workspace. Internal temp files may use `/tmp/lean4-learn/`.
- **Overwrite protection.** `--output=file` with existing target requires `--overwrite`; otherwise hard error.
- **Scope guardrails.** `--scope=project` in repo mode with >50 `.lean` files → warn with count, ask to narrow. In non-interactive contexts (e.g., LLM-invoked), default to "no" (do not proceed with large scope).
- **All `guardrails.sh` rules apply.**

## See Also

- [Examples](../skills/lean4/references/command-examples.md#learn)
- [Cycle Engine](../skills/lean4/references/cycle-engine.md) — shared mechanics
- [LSP Tools API](../skills/lean4/references/lean-lsp-tools-api.md) — search tools used in mathlib mode
- [Mathlib Guide](../skills/lean4/references/mathlib-guide.md) — mathlib navigation
- [Learning Pathways](../skills/lean4/references/learn-pathways.md) — intent taxonomy, game tracks, source handling

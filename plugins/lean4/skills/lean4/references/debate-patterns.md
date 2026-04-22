# Debate Patterns Reference

> Confidence-gated multi-agent debate for high-difficulty sorries. A single agent attempts first and self-reports confidence. If below 100%, independent agents debate iteratively until they converge on a strategy — following logic, not stubbornness.

## Overview

Two-stage process:

**Stage 1 — Confidence Gate:** The main cycle engine agent attempts the sorry and asks itself: "Am I 100% confident in this strategy?" If yes, proceed immediately. If no, escalate to Stage 2.

**Stage 2 — Iterative Debate:** Three independent agents (Mathematician, Tactician, Skeptic) argue in rounds. After each round a Judge checks for convergence. The debate continues until agents agree or a round limit is hit. Agents are genuinely open to each other's arguments — positions change when the logic demands it.

---

## Stage 1: Confidence Gate

Before spawning any debate agents, the cycle engine performs a self-assessment on each sorry that scores ≥ 7 on the difficulty rubric.

### Self-assessment prompt

After completing Plan phase LSP search for a sorry, ask:

> "Given the goal, the LSP search results, and any prior failures: do I have a single proof strategy I am 100% confident will work? If I had to commit right now to one approach, would I bet on it without hesitation?"

Answer with:

```json
{
  "sorry_id": "file:line",
  "confident": <true|false>,
  "strategy": "<if confident=true: the strategy to execute>",
  "doubt_reason": "<if confident=false: what specifically is uncertain — not just 'it is hard'>"
}
```

- `confident: true` → skip debate entirely, proceed with `strategy` directly into Work phase
- `confident: false` → escalate to Stage 2

**The bar is genuinely 100%.** "Pretty sure" is not 100%. If there is any specific doubt — an elaboration risk, an edge case, an alternative decomposition that might be better — it is not 100%.

---

## Stage 2: Iterative Debate

### Agents

| Agent | File | Model | Thinking | Role |
|-------|------|-------|----------|------|
| Mathematician | [lean4-debate-mathematician.md](../../../agents/lean4-debate-mathematician.md) | opus | on | Mathematical structure and decomposition |
| Tactician | [lean4-debate-tactician.md](../../../agents/lean4-debate-tactician.md) | sonnet | off | Lean 4 tactic mechanics and elaboration |
| Skeptic | [lean4-debate-skeptic.md](../../../agents/lean4-debate-skeptic.md) | opus | on | Failure modes, edge cases, statement risk |
| Judge | [lean4-debate-judge.md](../../../agents/lean4-debate-judge.md) | opus | on | Convergence detection, final execution plan |

### The debate loop

```
Round 1:
  Mathematician and Tactician spawn in parallel (no shared context)
  ↓ both complete
  Skeptic spawns (sees both outputs)
  ↓ Skeptic completes
  Judge spawns (sees all three outputs)
  ↓
  Judge outputs verdict: "continue" OR "resolved"

Round N (if continue):
  Mathematician, Tactician, Skeptic each receive:
    - original sorry context
    - full debate_history (all prior rounds from all agents)
    - Judge's crux question from prior round
  All three spawn in parallel
  ↓ all complete
  Judge spawns (sees full debate_history including round N)
  ↓
  Judge outputs verdict: "continue" OR "resolved"

Stop when:
  - Judge outputs "resolved" (convergence detected), OR
  - current_round == max_rounds (hard stop, Judge forces resolution)
```

### Convergence conditions (Judge evaluates after each round)

The debate resolves when **any** of:
1. All three agents set `converged: true` in the latest round
2. Two agents set `converged: true` and the third's `confidence` ≤ 3
3. All agents are substantively proposing the same strategy (even if worded differently)
4. `current_round == max_rounds` (hard stop)

### Round limit

Default `max_rounds = 5`. Configurable via `--debate-max-rounds`. In practice most debates resolve in 2–3 rounds — if agents are following logic, genuine disagreement rarely survives 3 rounds of direct engagement.

---

## Spawn Protocol

### Step 0: Build shared input context

Assembled once from Plan phase data. Passed to all agents every round, augmented with `round` and `debate_history`.

```json
{
  "sorry_id": "file:line",
  "goal": "<lean_goal output>",
  "local_hypotheses": ["h : T"],
  "lsp_search_results": {
    "leanfinder": ["lemma : type"],
    "leansearch": [],
    "loogle": []
  },
  "prior_failures": [],
  "difficulty_score": 8,
  "round": <current_round>,
  "debate_history": [ <all prior round outputs> ]
}
```

### Step 1: Round 1 — Mathematician and Tactician in parallel

```
Agent(
  subagent_type = "lean4:lean4-debate-mathematician",
  prompt = shared_context with round=1, debate_history=[],
  isolation = true
)

Agent(
  subagent_type = "lean4:lean4-debate-tactician",
  prompt = shared_context with round=1, debate_history=[],
  isolation = true
)
```

Wait for both. Each returns JSON. Append both to `debate_history`.

### Step 2: Skeptic

```
Agent(
  subagent_type = "lean4:lean4-debate-skeptic",
  prompt = shared_context with round=1, debate_history=[mathematician_r1, tactician_r1],
  isolation = true
)
```

Append to `debate_history`.

### Step 3: Judge

```
Agent(
  subagent_type = "lean4:lean4-debate-judge",
  prompt = {
    "sorry_id": "file:line",
    "difficulty_score": N,
    "max_rounds": 5,
    "current_round": 1,
    "debate_history": [mathematician_r1, tactician_r1, skeptic_r1]
  },
  isolation = true
)
```

### Step 4: If Judge returns `verdict: "continue"`

Increment round. Spawn Mathematician, Tactician, Skeptic again — each receives the full `debate_history` so far plus the Judge's `next_round_prompt` appended to the context. Run in sequence as above (Mathematician + Tactician parallel → Skeptic → Judge).

### Step 5: If Judge returns `verdict: "resolved"`

Use `judge.execution_plan` as the sorry's Work phase strategy. Emit to user:

```
*Debate (difficulty N/10, R rounds): [judge.debate_summary]*
```

---

## Difficulty Scoring Rubric

Rate each sorry 1–10 after `lean_goal` + LSP search in Plan phase:

| Signal | Low (0 pts) | Medium (1 pt) | High (2 pts) |
|--------|-------------|---------------|--------------|
| Goal complexity | Atomic, no binders | 1–2 quantifiers or type class constraints | Nested ∀/∃, universe polymorphism, dependent types |
| Mathlib search confidence | ≥ 2 high-confidence hits | 1 hit or low confidence | No hits |
| Hypothesis depth | ≤ 3 hypotheses | 4–8 hypotheses | > 8 or deep `have`/`let` chains |
| Type class complexity | None needed | 1 instance | ≥ 2 or synthesis likely to fail |
| Prior history | No failures | 1 failure | 2+ failures or previously stuck |
| Cross-file dependencies | Self-contained | 1–2 external defs | Many defs or depends on sorry'd lemmas |

Sum → `score = ceil(sum / 12 * 10)`, floor 1, cap 10.

**Threshold:** score ≥ 7 → confidence gate runs. score ≤ 6 → skip gate, standard Work.

**Trivial shortcut:** Obviously solvable goal (`rfl`, `simp`, `exact` with known lemma) → skip everything, difficulty 1, direct to Work.

**Thin-data skip:** LSP returned < 2 results total → skip debate, go directly to Deep Mode or standard Work.

---

## Integration with Cycle Engine

### Plan phase

```
For each sorry:
  1. lean_goal + up to 3 LSP search tools (existing)
  2. Rate difficulty 1–10
  3. IF score ≥ 7 AND --debate != off AND LSP results not thin:
       Self-assess confidence (Stage 1)
       IF confident: proceed to Work with self-assessed strategy
       IF not confident: run Stage 2 debate → use judge.execution_plan in Work
     ELSE:
       Standard 2-3 candidate generation in Work
```

### Work phase

When a sorry has a judge output:
- Generate candidates that implement `judge.execution_plan`
- Apply `judge.tactic_hints` as first candidates in `lean_multi_attempt`
- Apply `judge.guards` as pre/post conditions
- If `judge.preflight_falsification == true`: run falsification pass first (30-60s max)
- If `judge.winner == "escalate-to-deep"`: skip Work, enter Deep Mode immediately
- Use `judge.stuck_threshold` as attempt limit before escalating (overrides default 3)

### Stuck handoff evidence

When a debated sorry gets stuck, include:
- Full judge resolved output (all fields)
- Which part of `execution_plan` failed and why
- Whether agents' `potential_blocker` fields materialized

---

## Flag Reference

| Flag | prove default | autoprove default | Description |
|------|--------------|------------------|-------------|
| `--debate` | `ask` | `auto` | `ask`: show summary + prompt user before Work; `auto`: run silently; `off`: disable |
| `--debate-threshold` | `7` | `7` | Minimum difficulty score to trigger confidence gate |
| `--debate-max-rounds` | `5` | `5` | Hard stop on debate rounds |

**`--debate=ask` prompt (prove only):**
```
Debate resolved in R rounds: [judge.debate_summary]
Proceed with this strategy? [yes / override / skip-debate]
```

**`--debate=off`:** Difficulty scoring still runs and is logged, but no confidence gate and no agents spawned.

---

## Failure Handling

| Failure | Response |
|---------|----------|
| Mathematician or Tactician fails round 1 | Skeptic critiques only the available proposal; Judge notes missing agent |
| Both parallel agents fail round 1 | Skip debate; standard Work; log `"debate skipped: both advisors failed"` |
| Skeptic fails | Judge receives raw proposals with no critique; picks based on confidence scores alone |
| Judge fails | Fall back to: highest-confidence agent's position; tiebreak: Tactician |
| Any agent returns malformed JSON | Treat as agent failure, apply rules above |
| Debate hits `max_rounds` without convergence | Judge forces resolution with best available position; notes `"resolved by round limit"` in `debate_summary` |

---

## Relationship to Existing Escalation

```
Sorry discovered
  ↓
Difficulty score
  ├── ≤ 6  OR  --debate=off  OR  thin LSP data
  │     → standard Work (stuck threshold = 3)
  │           ↓ if stuck → Deep Mode
  │
  └── ≥ 7  AND  --debate != off  AND  sufficient data
        → Confidence gate (self-assessment)
              ├── confident=true → Work with self-assessed strategy
              │         ↓ if stuck → Deep Mode
              │
              └── confident=false → Iterative debate
                    Round 1: Mathematician ║ Tactician → Skeptic → Judge
                    Round N: repeat with full history until converged
                          ↓ resolved
                    winner=escalate-to-deep → Deep Mode
                    winner=strategy → Work (confidence-adjusted stuck threshold)
                          ↓ if stuck → Deep Mode
```

---

## Testing

### Load the plugin

```bash
claude --plugin-dir /Users/romirpatel/lean4-skills/plugins/lean4
```

### Test confidence gate (Stage 1)

On a sorry you are certain about, the self-assessment should return `confident: true` and skip debate entirely. On a sorry with genuine ambiguity, it should return `confident: false` and trigger Stage 2.

### Test individual debate agents

**Round 1 — Mathematician:**
```
Use the lean4:lean4-debate-mathematician agent with this input:
{"sorry_id":"Test.lean:10","goal":"⊢ ∀ (n : ℕ), ∑ i in Finset.range n, (2 * i + 1) = n ^ 2","local_hypotheses":[],"lsp_search_results":{"leanfinder":["Finset.sum_range_succ : ∑ i in Finset.range (n+1), f i = ∑ i in Finset.range n, f i + f n"],"leansearch":[],"loogle":[]},"prior_failures":["simp failed"],"difficulty_score":8,"round":1,"debate_history":[]}
```

**Round 2 — Mathematician (with history):** Pass the same input but set `"round": 2` and populate `"debate_history"` with round 1 outputs from all three agents. Verify the agent reads prior arguments and either updates its position or provides a specific rebuttal.

**Judge — continue vs resolved:** Pass a debate history where agents clearly disagree → expect `verdict: "continue"`. Pass a history where all three set `converged: true` → expect `verdict: "resolved"`.

### Test full pipeline

```
/lean4:prove --debate=ask
```

On a sorry scoring ≥ 7, you should see:
1. Confidence gate self-assessment (logged)
2. If not confident: debate rounds running (each round logged)
3. Final: `*Debate (difficulty 8/10, 2 rounds): [summary]*`
4. Prompt: `Proceed with this strategy? [yes / override / skip-debate]`

---

## See Also

- [cycle-engine.md](cycle-engine.md) — Where debate integrates
- [sorry-filling.md](sorry-filling.md) — Standard Work phase
- [learn-pathways.md](learn-pathways.md) — Pedagogical Self-Debate (single-agent simulation for teaching context)
- [domain-patterns.md](domain-patterns.md) — Domain patterns advisors draw on

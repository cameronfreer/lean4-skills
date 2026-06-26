# Lean 4 Plugin

> **Claude Code adapter.** This directory implements the native Claude Code plugin
> (hooks, guardrails, slash commands). The underlying skill content — SKILL.md,
> references, and scripts — is host-agnostic.
> See the [root README](../../README.md) for setup on other hosts.

Unified Lean 4 plugin for theorem proving, interactive learning, and formalization.

## Commands

| Command | Description |
|---------|-------------|
| `/lean4:draft` | Draft Lean declaration skeletons from informal claims |
| `/lean4:formalize` | Interactive formalization — drafting plus guided proving |
| `/lean4:autoformalize` | Autonomous end-to-end formalization from informal sources |
| `/lean4:prove` | Guided cycle-by-cycle theorem proving with explicit checkpoints |
| `/lean4:autoprove` | Autonomous multi-cycle theorem proving with explicit stop budgets |
| `/lean4:disprove` | Guided counterexample search with certified refutation |
| `/lean4:checkpoint` | Save progress with a safe commit checkpoint |
| `/lean4:review` | Read-only code review of Lean proofs |
| `/lean4:refactor` | Leverage mathlib, extract helpers, simplify proof strategies |
| `/lean4:golf` | Improve Lean proofs for directness, clarity, performance, and brevity |
| `/lean4:learn` | Interactive teaching and mathlib exploration |
| `/lean4:doctor` | Diagnostics, cleanup, and migration help |

## Quick Start

```bash
/lean4:draft               # Draft Lean skeletons from informal claims
/lean4:formalize           # Interactive synthesis (draft + prove)
/lean4:autoformalize       # Autonomous synthesis (source → proof)
/lean4:prove               # Guided sorry filling (interactive)
/lean4:autoprove           # Autonomous sorry filling (unattended)
/lean4:disprove Foo.lean:42  # Guided counterexample search with certified refutation (target required)
/lean4:checkpoint          # Build-checked save point
/lean4:review              # Check quality (read-only)
/lean4:refactor            # Simplify proof strategies
/lean4:golf                # Optimize proofs
/lean4:learn               # Explore repo or mathlib
/lean4:doctor              # Diagnostics and migration help
git push                   # Manual, after review
```

This plugin ships a host-agnostic parser (`lib/command_args/`) that covers the
parser-decidable startup rules of the seven parameter-heavy commands
(`draft`, `learn`, `formalize`, `autoformalize`, `prove`, `autoprove`,
`disprove`). The Claude
Code adapter pre-validates `/lean4:*` prompts via a `UserPromptSubmit` hook
that reuses the same parser; other hosts MAY invoke it via
`lib/scripts/parse_command_args.py` but otherwise fall back to model-parsed
startup. Commands must announce resolved inputs, reject invalid startup configs
before doing work, and treat wall-clock budgets as best-effort. See the
[Command Invocation Contract](skills/lean4/references/command-invocation.md).

To run the parser standalone (non-Claude hosts, scripting):

    python3 plugins/lean4/lib/scripts/parse_command_args.py draft -- "topic" --mode=attempt

Exits 0 on success (JSON to stdout), 2 on validation errors (error JSON to stdout).

## How It Works

### Without a Command

When you edit `.lean` files in a normal conversation, the plugin activates automatically — it helps with the immediate issue (a build error, a single sorry) but does one bounded pass only. No looping, no deep escalation. At the end it suggests the right next command:

> Use `/lean4:draft` or `/lean4:formalize` for statement work.
> Use `/lean4:prove` or `/lean4:autoprove` for proof work.

### `/lean4:draft` — Skeleton Drafting

Drafts Lean 4 declaration skeletons from informal claims. Default `--mode=skeleton` produces sorry-stubbed statements; `--mode=attempt` adds a proof-attempt loop. No full proof engine (no cycles, no falsification) — use `/lean4:formalize` for the full pipeline.

### `/lean4:formalize` — Interactive Synthesis

Combines drafting and guided proving in one human-in-the-loop workflow. Drafts a skeleton, then runs prove cycles with user interaction. Owns the right to modify declaration headers (the prove phase itself cannot). Accepts `--source` to ingest papers or files.

### `/lean4:autoformalize` — Autonomous Synthesis

Extracts claims from a source, drafts skeletons, and proves them — all unattended. Replaces the old `autoprove --formalize=auto` workflow as a first-class command with cleaner flag names.

### `/lean4:prove` — Guided Proving

Start here if you're new or want to stay in control.

At startup, `prove` asks your preferences: planning on/off and review source. Before each commit it shows the diff and asks — pick `yes-all` to stop prompting, or `never` to skip all commits for the session. Between every cycle it pauses:

```
Cycle complete. Filled 2/8 sorries this cycle.
- [continue] — run next cycle
- [stop] — save progress and exit
- [adjust] — change flags for next cycle
```

It never auto-starts the next cycle. You decide when to continue.

### `/lean4:autoprove` — Autonomous Proving

Use when you want to kick it off and walk away.

No questionnaire — discovers state and starts immediately. Commits without prompting by default (`--commit=auto`). Loops automatically with checkpoint + review + replan at each cycle boundary. Stops on the first condition met:

- All sorries filled
- 3 consecutive stuck cycles (`--max-stuck-cycles`)
- 20 total cycles (`--max-cycles`)
- 120 minutes wall-clock budget reached (`--max-total-runtime`, checked between cycles)

On stop, emits a structured summary (sorries before/after, cycles, time, handoff recommendations).

### The Cycle Engine (Shared)

The proof engines (`prove`, `autoprove`, `formalize`, `autoformalize`) all run the same 6-phase cycle:

```
Plan → Work → Checkpoint → Review → Replan → Continue/Stop
```

- **Plan** — Discover sorries via LSP, set order
- **Work** — Per sorry: search mathlib, try tactics, validate, stage only touched files, commit
- **Checkpoint** — Commit cycle progress (skipped if nothing changed)
- **Review** — Scoped quality check at configured intervals (`--review-every`)
- **Replan** — Planner mode updates the action plan based on review findings
- **Continue/Stop** — `prove` asks you; `autoprove` auto-continues

When stuck (same blocker seen twice), both force a review + replan regardless of settings.

`disprove` uses the same phase skeleton but specializes Phase 5 as **Accumulate** (per-cycle evidence append) and Phase 1 with dynamic Step 0 / Step 1 / Step 2 menus seeded by accumulated evidence.

### `/lean4:disprove` — Counterexample Search

Use when you suspect a statement is false and want a Lean-certified refutation. Always interactive: each cycle prompts you through dynamic menus seeded by accumulated evidence.

Takes a target (`File.lean:LINE` or `Namespace.theoremName`). Runs a 6-phase cycle — **Plan → Work → Checkpoint → Review → Accumulate → Continue/Stop** — where a "cycle" is a widening pass over the same target rather than a batch of sorries (Phase 5 — Accumulate — replaces prove's Replan).

Each cycle's **Plan** phase generates three dynamic menus:

1. **Step 0 — Knowledge Search Menu** (Cycle 1 by default; later cycles re-enter only if Step 1 picks `knowledge search`, subject to `--knowledge-search-budget`). Eight menu items: six pre-tagged across `[lean]` / `[local]` / `[web]` tiers, plus `[custom]` (user-supplied free-form intent — LLM picks tier at fire time) and `[llm]` (LLM-proposed query + tier). Each pre-tagged row shows the source/tool, tier tag, and executable query the cycling LLM derives from the TARGET. Findings without a citable URL are dropped at write time; web counterexample candidates are spot-verified via `WebFetch` before elevation to `[verify-known-cex]`.
2. **Step 1 — Method Menu**: the cycling LLM proposes 3–10 method candidates from a stable Method Registry (`decide-cascade`, `mine`, `enumerate`, `plausible`, `tactics`, `external`), plus always-present `knowledge search` and `custom method` extras. Each entry shows the stable `family` id, a free-text label, the LLM's reasoning, and a cost class.
3. **Step 2 — Config Menu**: if Step 1 picked `knowledge search`, this is a multi-select Step 0 re-run. Otherwise, the cycling LLM proposes 3–10 candidate configs for the picked family, plus a `custom-config` extra (free-text, schema-validated against the family's parameter table).

Phase 5 — **Accumulate** — appends the cycle's `(family, config, outcome, near-miss_signature)` to session evidence. The next cycle's menus absorb the recommendation logic; there is no hardcoded Replan table.

Tri-state outcome:

- **REFUTED** — Lean typechecks the negation. The only outcome that certifies a refutation.
- **WITNESS_UNCERTIFIED** — candidate found but Lean refused certification.
- **INCONCLUSIVE** — no candidate within `--max-cycles` widening passes (default 3) or `--max-stuck-cycles` consecutive cycles with no widening lever left.

Append-only by design: never rewrites an existing `theorem T : P := by sorry`. See [disprove-engine.md](skills/lean4/references/disprove-engine.md).

### `/lean4:checkpoint` — Save Point

Compiles each touched `.lean` file, runs `lake build`, checks for non-standard axioms, reports sorry count, then stages and commits.

Does **not** push — that's always manual (`git push`).

### `/lean4:review` — Quality Check

Read-only. Does not modify files or create commits.

Runs build verification, sorry audit, axiom check, style review, strategy simplification opportunities, and golfing opportunity scan. Scopes automatically to what you're working on (`--scope=sorry`, `file`, `changed`, or `project`). Two modes:

- **batch** (default) — full report with all sections
- **stuck** — lightweight triage: top 3 blockers with next steps

`prove` and `autoprove` trigger reviews automatically at configured intervals. You can also run `/lean4:review` manually at any time.

### `/lean4:refactor` — Strategy-Level Simplification

Finds better proof approaches: replaces hand-rolled arguments with mathlib lemmas, extracts repeated patterns as helpers, replaces case splits with `congr`/`EqOn` patterns. Asks before each batch of edits; reverts on verification failure. Compiled proofs only.

### `/lean4:golf` — Proof Improvement

Scores candidates by directness → inference burden → performance → length. Applies safe patterns: `by exact t → t`, `apply+exact → exact`, inline single-use `let`, `ext+rfl → rfl`, etc. Conditional patterns (`rw+exact → rwa`) require net score improvement. Verifies with `lean_diagnostic_messages` after each change (`lake build` at final gate only) and reverts failures. Stops when the success rate drops below 20% (saturation).

Usually run after proving, either prompted at the end of a `prove` session or explicitly.

### `/lean4:learn` — Interactive Teaching

Two modes: `--mode=repo` explores your project structure, `--mode=mathlib` navigates mathlib for a topic. Adapts to `--level=beginner|intermediate|expert` and supports `--style=tour|socratic|exercise|game`. Conversational by default; use `--output=scratch` or `--output=file` to write artifacts. For formalization, learn suggests `/lean4:formalize`.

### `/lean4:doctor` — Diagnostics

Checks your environment (lean, lake, python, git), plugin structure, project health, and detects legacy v3 artifacts. Run this first if something isn't working.

### Commit Behavior

- `prove` defaults to `--commit=ask` — prompts before each commit (`yes-all` / `never` to stop prompting)
- `autoprove` defaults to `--commit=auto` — commits without prompting
- Both stage only files actually touched during the work, never `git add -A`

### Safety Guardrails

Guardrails activate only in Lean project context (a directory tree containing `lakefile.lean`, `lean-toolchain`, or `lakefile.toml`). Outside Lean projects, they are silently skipped.

Guarded during Lean project sessions (policy/tier details below):
- `git push` → Use `/lean4:checkpoint`, then push manually (soft-gate, bypass-able)
- `git commit --amend` → Each change is a new commit for safe rollback (soft-gate, bypass-able)
- `gh pr create` → Review first with `/lean4:review` (soft-gate, bypass-able)
- Path-scoped destructive git (`checkout -- <path>`, `checkout [-q|--quiet] <tree-ish> <path>`, `checkout {--ours,--theirs,-2,-3,--merge,--conflict=…} <path>`, `checkout {--ignore-skip-worktree-bits,--no-overlay,--overlay,--recurse-submodules,-p,--patch} <path>`, `checkout -f <path-like>`, `checkout ./<path>` (incl. dotfiles), `restore <path>` and short-flag variants) → soft-gate, bypass-able; default `ask` mode
- Whole-worktree / force-branch / interactive-sweep destructive git (`reset --hard`, `clean -f`, `checkout .` / `-- .` / `HEAD -- .` / `-f .` / `--ours .`, `restore .` / `-SW`, `checkout --pathspec-from-file`, `restore --pathspec-from-file` (non-staged), `checkout -f|--force <branch-or-ref>`, `checkout -p`/`--patch` with no path, `switch -f|--force|--discard-changes`) → absolute hard-block; bypass does not apply
- Deep sorry-filling has snapshot, rollback, scope budgets, and regression gates — see [Cycle Engine](skills/lean4/references/cycle-engine.md#deep-mode)

**Override environment variables:**

| Variable | Effect |
|----------|--------|
| `LEAN4_GUARDRAILS_DISABLE=1` | Skip all guardrails regardless of context |
| `LEAN4_GUARDRAILS_FORCE=1` | Enforce guardrails even outside Lean projects |
| `LEAN4_GUARDRAILS_COLLAB_POLICY` | Collaboration op policy: `ask` (default), `allow`, `block` |
| `LEAN4_GUARDRAILS_DESTRUCTIVE_POLICY` | Path-scoped destructive op policy: `ask` (default), `allow`, `block` |

`LEAN4_GUARDRAILS_DISABLE` overrides everything. `LEAN4_GUARDRAILS_FORCE` controls whether guardrails activate outside Lean projects.

Git operations fall into **three tiers**:

1. **Allow** (implicit, no gate): `git status`, `diff`, `log`, `show`, `branch`, `add`, `commit`, `stash push`, `switch <branch>`, `checkout <branch>`, `restore --staged <path>` (pure unstaging, any pathspec including `.`).
2. **Soft-gate** (policy-controlled, bypass-able): collaboration ops + path-scoped destructive ops. See subsections below.
3. **Hard-block** (absolute, never bypassable): `git reset --hard`, `git clean -f`/`-fd`/`-fdx`, plus the whole-worktree, opaque-pathspec, force-branch, and interactive-sweep variants — `git checkout .`/`./`/`-- .`/`-- ./`/`-- :/`/`HEAD -- .`/`-f .`/`--ours .`/`--theirs :/`, `git checkout --pathspec-from-file=…`, `git checkout -f|--force <branch-or-ref>` (incl. ref shorthand `@{-1}`, `-`, `@`, `HEAD~3`, `HEAD@{1}`), `git checkout -p`/`--patch` with no path positional (interactive whole-worktree sweep, bypassable by piped stdin), `git restore .`/`./`/`:/`, `git restore --staged --worktree` (incl. `-SW` short-flag bundle), `git restore --pathspec-from-file=…` (non-staged), `git switch -f|--force|--discard-changes <anything>`. These wipe state across the whole worktree (or untracked files), discard uncommitted edits during branch switching, sweep modified files interactively from an opaque stdin source, or accept opaque path lists the guardrail can't inspect; reflog can't recover uncommitted edits and `clean -f` can't recover untracked files at all.

**Collaboration policy (`LEAN4_GUARDRAILS_COLLAB_POLICY`):**

Controls how collaboration ops (`git push`, `git commit --amend`, `gh pr create`) — operations that affect shared state — are handled:

- **`ask`** (default) — block unless a one-shot bypass token is present. The hook is non-interactive; in `ask` mode the assistant asks you yes/no, then reruns the command with the bypass token once.
- **`allow`** — permit collaboration ops without a bypass token.
- **`block`** — block collaboration ops unconditionally, even with a bypass token.

Invalid values fall back to `ask`.

**Destructive policy (`LEAN4_GUARDRAILS_DESTRUCTIVE_POLICY`):**

Controls how **path-scoped** destructive ops are handled. The covered forms (each with bounded blast radius — the named pathset only — but still discarding uncommitted edits the reflog can't recover):

- `git checkout -- <path…>`
- `git checkout [-q|--quiet] <tree-ish> <path…>` (without `--`, e.g. `git checkout HEAD file.lean`; non-destructive flag prefix or interleaving OK)
- `git checkout {--ours,--theirs,-2,-3,--merge,--conflict=<style>} <path…>` (merge-conflict resolution flags; long-form `--merge` covered, short-form `-m` deferred per `_strip_optvals` limitation)
- `git checkout {--ignore-skip-worktree-bits,--no-overlay,--overlay,--recurse-submodules,-p,--patch} <path…>` (pathspec-oriented flags; `-p`/`--patch` is interactive but pipes like `yes y | …` bypass interactivity, so soft-gated regardless of TTY)
- `git checkout -f|--force <path-like>` (path-scoped force-restore; `-f <branch-or-ref>` is hard-blocked instead)
- `git checkout ./<path>` / `:/<path>` / `../<path>` (explicit path-prefix positionals, including dotfiles)
- `git restore <path…>` (any worktree-touching flag combination, including `-W`, `-SW`, etc.)

`git restore --staged <path>` (pure unstaging, including pathspec `.`) is always allowed regardless of policy — it's index-only and reversible.

- **`ask`** (default) — block unless a one-shot bypass token is present.
- **`allow`** — permit path-scoped destructive ops without a bypass token (useful when routinely reverting experimental files).
- **`block`** — block unconditionally, even with a bypass token.

Invalid values fall back to `ask`. Whole-worktree destructive variants (tier 3 above) are independent of this policy and **always block** regardless of its value or the bypass token.

The two policies are independent: `DESTRUCTIVE_POLICY=allow` does not unblock collab ops, and `COLLAB_POLICY=allow` does not unblock path-scoped destructive ops.

**One-shot bypass (soft-gated ops):**

To override a single blocked soft-gated command, prefix it with the bypass token:

```bash
LEAN4_GUARDRAILS_BYPASS=1 git push origin main
LEAN4_GUARDRAILS_BYPASS=1 git checkout -- experiment.lean
LEAN4_GUARDRAILS_BYPASS=1 git restore src/some_file.lean
```

The token must appear in the leading env-assignment prefix of the command (command prefix only, not an environment variable). Bypass is effective only in `ask` mode (default for both policies); it is unnecessary in `allow` mode and ignored in `block` mode. Bypass does **not** apply to whole-worktree hard-blocked ops (`reset --hard`, `clean -f`, `checkout .`, etc.) — those are absolute.

### LSP-First Approach

LSP tools are **normative** (required first-pass), not merely preferred. Both prove and autoprove follow the [LSP-first protocol](skills/lean4/references/cycle-engine.md#lsp-first-protocol):

```
lean_goal(file, line)                           # See exact goal
lean_local_search("keyword")                    # Fast local + mathlib (unlimited)
lean_leanfinder("goal or query")                # Semantic, goal-aware (rate-limited)
lean_leansearch("natural language")             # Semantic search (rate-limited)
lean_loogle("?a → ?b → _")                      # Type-pattern (rate-limited)
lean_multi_attempt(file, line, snippets=[...])  # Test multiple tactics
```

Scripts provide sorry analysis, axiom checking, and search fallback when LSP is unavailable or LSP budget is exhausted. Compiler-guided repair is escalation-only — it triggers when compiler errors resist LSP-first tactics, not on first failure.

## Environment Variables

Set by `bootstrap.sh` at session start:

| Variable | Purpose |
|----------|---------|
| `LEAN4_PLUGIN_ROOT` | Plugin installation path |
| `LEAN4_SCRIPTS` | Scripts directory |
| `LEAN4_REFS` | References directory |
| `LEAN4_PYTHON_BIN` | Python interpreter |

Optional user overrides (not set by bootstrap):

| Variable | Purpose |
|----------|---------|
| `LEAN4_GUARDRAILS_DISABLE` | Skip all guardrails (set to `1`) |
| `LEAN4_GUARDRAILS_FORCE` | Force guardrails outside Lean projects (set to `1`) |
| `LEAN4_GUARDRAILS_COLLAB_POLICY` | Collaboration op policy: `ask`, `allow`, `block` |

**Script troubleshooting:**
```bash
echo "$LEAN4_SCRIPTS"                       # bootstrap set the env var
command -v lean4-skills-sorry-analyzer       # wrapper resolves on PATH
lean4-skills-sorry-analyzer . --format=summary --report-only
```

If `$LEAN4_SCRIPTS` is unset, run `/lean4:doctor` to reinitialize.

## File Structure

```
plugins/lean4/
├── .claude-plugin/plugin.json
├── commands/           # User-invocable commands
├── skills/lean4/
│   ├── SKILL.md        # Core skill reference
│   └── references/     # Reference docs
├── agents/             # 4 specialized agents
├── hooks/              # Bootstrap and guardrails
├── scripts/            # Compat alias → lib/scripts
└── lib/scripts/        # 12 hard-primitive scripts
```

## Upgrading from v3

See [MIGRATION.md](MIGRATION.md) for upgrade guide.

## See Also

- [SKILL.md](skills/lean4/SKILL.md) - Core skill reference
- [Commands](commands/) - Command documentation
- [Scripts](lib/scripts/README.md) - Script reference
- [Custom Syntax](skills/lean4/references/lean4-custom-syntax.md) - Notations, macros, elaborators, DSLs
- [DSL Scaffold](skills/lean4/references/scaffold-dsl.md) - Copy-paste DSL template
- [References](skills/lean4/references/) - grind, simprocs, metaprogramming, linters, FFI, verso-docs, profiling

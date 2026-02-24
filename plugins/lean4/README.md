# Lean 4 Plugin

Unified Lean 4 plugin for theorem proving, interactive learning, and autoformalization.

## Commands

| Command | Description |
|---------|-------------|
| `/lean4:prove` | Guided cycle-by-cycle theorem proving |
| `/lean4:autoprove` | Autonomous multi-cycle proving with stop rules |
| `/lean4:checkpoint` | Verified save point (build + axiom check + commit) |
| `/lean4:review` | Read-only quality review with optional external hooks |
| `/lean4:golf` | Optimize proofs for brevity |
| `/lean4:doctor` | Diagnostics and migration help |
| `/lean4:learn` | Interactive teaching, mathlib exploration, and autoformalization |

## Quick Start

```bash
/lean4:prove               # Guided sorry filling (interactive)
/lean4:autoprove           # Autonomous sorry filling (unattended)
/lean4:review              # Check quality (read-only)
/lean4:golf                # Optimize proofs
/lean4:checkpoint          # Verified commit
/lean4:learn               # Explore repo, mathlib, or formalize
git push                   # Manual, after review
```

## How It Works

### Without a Command

When you edit `.lean` files in a normal conversation, the plugin activates automatically — it helps with the immediate issue (a build error, a single sorry) but does one bounded pass only. No looping, no deep escalation. At the end it suggests:

> Use `/lean4:prove` for guided cycle-by-cycle help.
> Use `/lean4:autoprove` for autonomous cycles with stop safeguards.

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
- 120 minutes elapsed (`--max-total-runtime`)

On stop, emits a structured summary (sorries before/after, cycles, time, handoff recommendations).

### The Cycle Engine (Shared)

Both commands run the same 6-phase cycle:

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

### `/lean4:review` — Quality Check

Read-only. Does not modify files or create commits.

Runs build verification, sorry audit, axiom check, style review, and golfing opportunity scan. Scopes automatically to what you're working on (`--scope=sorry`, `file`, `changed`, or `project`). Two modes:

- **batch** (default) — full report with all sections
- **stuck** — lightweight triage: top 3 blockers with next steps

`prove` and `autoprove` trigger reviews automatically at configured intervals. You can also run `/lean4:review` manually at any time.

### `/lean4:checkpoint` — Verified Save Point

Runs `lake build`, checks for non-standard axioms, reports sorry count, then stages and commits. One command for "I want a known-good save point."

Does **not** push — that's always manual (`git push`).

### `/lean4:golf` — Proof Optimization

Finds and applies safe optimizations: `rw+exact → rwa`, inline single-use `let`, `ext+rfl → rfl`, etc. Verifies with `lean_diagnostic_messages` after each change (`lake build` at final gate only) and reverts failures. Stops when the success rate drops below 20% (saturation).

Usually run after proving, either prompted at the end of a `prove` session or explicitly.

### `/lean4:learn` — Interactive Teaching & Formalization

Three modes: `--mode=repo` explores your project structure, `--mode=mathlib` navigates mathlib for a topic, `--mode=formalize` turns informal math into Lean statements (optionally under assumptions with `--rigor=axiomatic`). Adapts to `--level=beginner|intermediate|expert` and supports `--style=tour|socratic|exercise`. Conversational by default; use `--output=scratch` or `--output=file` to write artifacts.

### `/lean4:doctor` — Diagnostics

Checks your environment (lean, lake, python, git), plugin structure, project health, and detects legacy v3 artifacts. Run this first if something isn't working.

### Commit Behavior

- `prove` defaults to `--commit=ask` — prompts before each commit (`yes-all` / `never` to stop prompting)
- `autoprove` defaults to `--commit=auto` — commits without prompting
- Both stage only files actually touched during the work, never `git add -A`

### Safety Guardrails

Guardrails activate only in Lean project context (a directory tree containing `lakefile.lean`, `lean-toolchain`, or `lakefile.toml`). Outside Lean projects, they are silently skipped.

Blocked during Lean project sessions:
- `git push` → Use `/lean4:checkpoint`, then push manually
- `git commit --amend` → Each change is a new commit for safe rollback
- `gh pr create` → Review first with `/lean4:review`
- Destructive git operations (`checkout --`, `restore`, `reset --hard`, `clean -f`) → Use `git stash push -u`
- Deep sorry-filling has snapshot, rollback, scope budgets, and regression gates — see [Cycle Engine](skills/lean4/references/cycle-engine.md#deep-mode)

**Override environment variables:**

| Variable | Effect |
|----------|--------|
| `LEAN4_GUARDRAILS_DISABLE=1` | Skip all guardrails regardless of context |
| `LEAN4_GUARDRAILS_FORCE=1` | Enforce guardrails even outside Lean projects |
| `LEAN4_GUARDRAILS_COLLAB_POLICY` | Collaboration op policy: `ask` (default), `allow`, `block` |

`LEAN4_GUARDRAILS_DISABLE` overrides everything. `LEAN4_GUARDRAILS_FORCE` controls whether guardrails activate outside Lean projects.

**Collaboration policy (`LEAN4_GUARDRAILS_COLLAB_POLICY`):**

Controls how collaboration ops (`git push`, `git commit --amend`, `gh pr create`) are handled:

- **`ask`** (default) — block unless a one-shot bypass token is present. The hook is non-interactive; in `ask` mode the assistant asks you yes/no, then reruns the command with the bypass token once.
- **`allow`** — permit collaboration ops without a bypass token.
- **`block`** — block collaboration ops unconditionally, even with a bypass token.

Invalid values fall back to `ask`. Destructive operations (`checkout --`, `restore`, `reset --hard`, `clean -f`) are always blocked regardless of policy.

**One-shot bypass (collaboration ops only):**

To override a single blocked collaboration command (`git push`, `git commit --amend`, `gh pr create`), prefix it with the bypass token:

```bash
LEAN4_GUARDRAILS_BYPASS=1 git push origin main
```

The token must appear in the leading env-assignment prefix of the command (command prefix only, not an environment variable). Bypass is effective only in `ask` mode (default); it is unnecessary in `allow` mode and ignored in `block` mode. Destructive operations (`checkout --`, `restore`, `reset --hard`, `clean -f`) are always blocked — bypass does not apply to them.

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
echo "$LEAN4_SCRIPTS"
ls -l "$LEAN4_SCRIPTS/sorry_analyzer.py"
${LEAN4_PYTHON_BIN:-python3} "$LEAN4_SCRIPTS/sorry_analyzer.py" . --format=summary --report-only
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
├── skills/lean4-compiler-attrs/ # Compiler attributes playbook (`csimp`, `implemented_by`, inline)
├── skills/lean4-compiler-pipeline/ # LCNF/IR tracing, options, and cpass installer workflow
├── skills/lean4-ffi-interop/    # `extern`/`export` and Lake FFI wiring patterns
├── skills/lean4-init-runtime/   # `initialize`/`[init]`/builtin init runtime ordering patterns
├── skills/lean4-symbol-linkage/ # Name mangling, symbol stems, export overrides, and init symbol diagnostics
├── skills/zulip-extract/        # Parse Zulip HTML dumps into plain text
├── agents/             # 4 specialized agents
├── hooks/              # Bootstrap and guardrails
├── scripts/           # Compat alias → lib/scripts
└── lib/scripts/        # 12 hard-primitive scripts
```

## Upgrading from V3

See [MIGRATION.md](MIGRATION.md) for upgrade guide.

## See Also

- [SKILL.md](skills/lean4/SKILL.md) - Core skill reference
- [Lean4 Compiler Attrs](skills/lean4-compiler-attrs/SKILL.md) - `implemented_by`, `csimp`, inlining, extraction controls
- [Lean4 Compiler Pipeline](skills/lean4-compiler-pipeline/SKILL.md) - LCNF/IR traces, compiler options, `cpass` installer workflow
- [Lean4 FFI Interop](skills/lean4-ffi-interop/SKILL.md) - `extern`/`export` + Lake linking + reverse FFI init flow
- [Lean4 Init Runtime](skills/lean4-init-runtime/SKILL.md) - `initialize`/`[init]`/builtin init sequencing and host runtime setup
- [Lean4 Symbol Linkage](skills/lean4-symbol-linkage/SKILL.md) - Name mangling, package prefixes, `_init_` symbols, and export override diagnostics
- [Zulip Extract](skills/zulip-extract/SKILL.md) - Convert Zulip HTML exports to readable plain text
- [Commands](commands/) - Command documentation
- [Scripts](lib/scripts/README.md) - Script reference
- [Custom Syntax](skills/lean4/references/lean4-custom-syntax.md) - Notations, macros, elaborators, DSLs
- [DSL Scaffold](skills/lean4/references/scaffold-dsl.md) - Copy-paste DSL template
- [Advanced References](skills/lean4/references/) - grind, simprocs, metaprogramming, linters, FFI, verso-docs, profiling

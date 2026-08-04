# Lean 4 Plugin Guardrails

Canonical guardrail policy for the `lean4` plugin — activation scope, the
three-tier operation model, override environment variables, per-op
collaboration policies, destructive-op policy, and the one-shot bypass.
The plugin README carries only a summary; this file is the single owner of
the full policy (enforced by the docs lint).

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
| `LEAN4_GUARDRAILS_PUSH_POLICY` | `git push` policy: `host` (default), `ask`, `allow`, `block` |
| `LEAN4_GUARDRAILS_AMEND_POLICY` | `git commit --amend` policy: `host` (default), `ask`, `allow`, `block` |
| `LEAN4_GUARDRAILS_PR_CREATE_POLICY` | `gh pr create` policy: `host` (default), `ask`, `allow`, `block` |
| `LEAN4_GUARDRAILS_DESTRUCTIVE_POLICY` | Path-scoped destructive op policy: `ask` (default), `allow`, `block` |
| `LEAN4_GUARDRAILS_COLLAB_POLICY` | **Legacy** fallback for any unset per-op collab policy above (pre-v4.5.2 single-knob var, kept for back-compat) |

`LEAN4_GUARDRAILS_DISABLE` overrides everything. `LEAN4_GUARDRAILS_FORCE` controls whether guardrails activate outside Lean projects.

Git operations fall into **three tiers**:

1. **Allow** (implicit, no gate): `git status`, `diff`, `log`, `show`, `branch`, `add`, `commit`, `stash push`, `switch <branch>`, `checkout <branch>`, `restore --staged <path>` (pure unstaging, any pathspec including `.`).
2. **Soft-gate** (policy-controlled, bypass-able): collaboration ops + path-scoped destructive ops. See subsections below.
3. **Hard-block** (absolute, never bypassable): `git reset --hard`, `git clean -f`/`-fd`/`-fdx`, plus the whole-worktree, opaque-pathspec, force-branch, and interactive-sweep variants — `git checkout .`/`./`/`-- .`/`-- ./`/`-- :/`/`HEAD -- .`/`-f .`/`--ours .`/`--theirs :/`, `git checkout --pathspec-from-file=…`, `git checkout -f|--force <branch-or-ref>` (incl. ref shorthand `@{-1}`, `-`, `@`, `HEAD~3`, `HEAD@{1}`), `git checkout -p`/`--patch` with no path positional (interactive whole-worktree sweep, bypassable by piped stdin), `git restore .`/`./`/`:/`, `git restore --staged --worktree` (incl. `-SW` short-flag bundle), `git restore --pathspec-from-file=…` (non-staged), `git switch -f|--force|--discard-changes <anything>`. These wipe state across the whole worktree (or untracked files), discard uncommitted edits during branch switching, sweep modified files interactively from an opaque stdin source, or accept opaque path lists the guardrail can't inspect; reflog can't recover uncommitted edits and `clean -f` can't recover untracked files at all.

**Collaboration policies (per-op, v4.5.2+):**

Three independent env vars, one per collaboration op — `LEAN4_GUARDRAILS_PUSH_POLICY`, `LEAN4_GUARDRAILS_AMEND_POLICY`, `LEAN4_GUARDRAILS_PR_CREATE_POLICY` — each accepting:

- **`host`** (default) — exit 0 and defer to the host's native permission/sandbox policy. This stops the hook from fighting the host's own permission UX with exit-2 + bypass-token retries. Under Claude Code, the recommended configuration pairs `host` mode with native `Bash(...)` ask rules in `.claude/settings.local.json`:

  ```json
  {
    "permissions": {
      "ask": [
        "Bash(git push)",
        "Bash(git push *)",
        "Bash(gh pr create)",
        "Bash(gh pr create *)",
        "Bash(git commit --amend)",
        "Bash(git commit --amend *)"
      ]
    }
  }
  ```

  Per Claude Code's permission docs, `Bash(<cmd> *)` matches commands starting with `<cmd> ` (note the trailing space before `*` is required by the matcher). That covers `git push origin main` but **not bare `git push`** — the exact-form rule `Bash(<cmd>)` catches the no-args case. Both are listed above so either form is asked. Claude Code will then prompt once per command (or per session, depending on the user's "remember" choice), and the hook stays out of the way.

- **`ask`** — block unless a one-shot bypass token is present. The hook is non-interactive; in `ask` mode the assistant asks you yes/no, then reruns the command with `LEAN4_GUARDRAILS_BYPASS=1` once. This is the pre-v4.5.2 default behavior.
- **`allow`** — permit the op without a bypass token.
- **`block`** — block the op unconditionally, even with a bypass token.

**Unset** vars resolve to `host` via the back-compat fallback chain (legacy `COLLAB_POLICY` is checked first; if it's also unset, `host` wins). **Explicit invalid values** (typos like `alow`, `bock`, `yolo`) fall back to `ask` — typos shouldn't silently relax the plugin-level guardrail.

**Back-compat:** the legacy `LEAN4_GUARDRAILS_COLLAB_POLICY` var (pre-v4.5.2, single knob for all three ops) is honored as the fallback for any per-op policy that isn't explicitly set. So users who set `COLLAB_POLICY=allow` or `COLLAB_POLICY=block` in their settings keep their existing soft-gate semantics on all three ops; users who don't set it get the new `host` default on each. Setting both `COLLAB_POLICY` and a per-op var means the per-op var wins for that op.

**Push variants hard-blocked (tier 3, non-bypassable):** the following push forms rewrite shared history, delete refs, or replicate-and-delete all refs, and are blocked regardless of `PUSH_POLICY` — same posture as `git reset --hard`:

- `git push --force` / `-f`, plus any bundled short-flag run containing `f` (e.g. `git push -fu origin main`, `-uf`, `-vfu`, `-fnq`)
- `git push --force-with-lease[=<ref>]`
- `git push --mirror`
- `git push --delete <ref>` / `-d <ref>`, plus any bundled short-flag run containing `d` (e.g. `git push -dn origin feat`, `-nd`, `-vd`)
- `git push <remote> :<ref>` (legacy delete-ref syntax)
- `git push <remote> +<refspec>` (leading-`+` force-refspec; e.g. `+HEAD:main`, `+main`, `+src:dst`)

Escape hatch for these: `LEAN4_GUARDRAILS_DISABLE=1 git push --force ...` for the specific command.

Note on bundled `-n`: the long form `--dry-run` exempts every push hard-block check (back-compat with v4.5.1), but the bundled short form `-n` inside a `-fn` / `-dn` etc. run does **not** exempt — bundled-force-with-dry-run signals force intent the hook flags regardless. To dry-run a force, use `git push --force --dry-run` (long forms).

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

The collab and destructive policies are independent: `DESTRUCTIVE_POLICY=allow` does not unblock collab ops, and any of the collab `*_POLICY=allow` settings (or legacy `COLLAB_POLICY=allow`) do not unblock path-scoped destructive ops.

**One-shot bypass (soft-gated ops):**

To override a single blocked soft-gated command, prefix it with the bypass token:

```bash
LEAN4_GUARDRAILS_BYPASS=1 git push origin main
LEAN4_GUARDRAILS_BYPASS=1 git checkout -- experiment.lean
LEAN4_GUARDRAILS_BYPASS=1 git restore src/some_file.lean
```

The token must appear in the leading env-assignment prefix of the command (command prefix only, not an environment variable). Bypass is effective only in `ask` mode (default for both policies); it is unnecessary in `allow` mode and ignored in `block` mode. Bypass does **not** apply to whole-worktree hard-blocked ops (`reset --hard`, `clean -f`, `checkout .`, etc.) — those are absolute.

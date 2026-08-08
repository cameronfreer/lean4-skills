# Project Context (`project-context/v1`)

> **Scope:** The shared mathlib contribution-context contract (issue #174, roadmap #151 Track 1). Consulted by workflows that must know whether current work plausibly targets upstream mathlib — file-template generation (#109), the checkpoint `mk_all --check` gate (#111), and later review behavior (#110/#115). Not part of the prove/autoprove default loop.

`lean4-skills-project-context [--from PATH]` emits a versioned JSON record of repository **facts** and derived contribution **intent** — kept strictly separate. Deterministic: no network, no caching, all lists sorted. `--from` defaults to cwd, accepts a file or directory, and resolves the project root as the nearest ancestor containing any of `lakefile.lean`, `lakefile.toml`, `lean-toolchain`.

## Record shape

```json
{
  "schema": "project-context/v1",
  "root": "/abs/project/root | null",
  "facts": {
    "repository_kind": "mathlib | other-lean | not-lean | unknown",
    "project_markers": ["lakefile.toml", "lean-toolchain"],
    "toolchain": "leanprover/lean4:v4.32.0 | null",
    "git": { "available": true, "is_repository": true, "remote_scan": "complete | failed | skipped" },
    "remotes": [ { "name": "upstream", "fetch_urls": ["…"], "push_urls": ["…"], "is_canonical_mathlib": true } ],
    "mk_all_declared": true
  },
  "intent": { "contributing_upstream": "yes | no | unknown", "source": "env-override | invalid-env-override | remote-heuristic | default" },
  "warnings": [ { "code": "…", "message": "…" } ]
}
```

- **"Could not determine" is never a confident fact**: `repository_kind` has an explicit `unknown`; `git.is_repository` is `null` when inspection could not run; every degradation adds a `{code, message}` warning.
- `repository_kind` derivation: `mathlib` — confidently matched package/tree signatures (lakefile package name `mathlib`, or root `Mathlib.lean` + `Mathlib/`); `other-lean` — markers found, inspection succeeded, mathlib signatures absent; `not-lean` — no markers from an existing start path; `unknown` — inspection incomplete/inaccessible.
- Remotes carry **all effective fetch and push URLs as reported by `git remote get-url --all` / `--push --all`** (git may have applied `url.*.insteadOf` rewriting, and push URLs fall back to fetch URLs when no explicit pushurl exists — the effective interpretation is deliberate for intent detection). `is_canonical_mathlib` matches `leanprover-community/mathlib4` over exactly the whitelisted transports — HTTPS, SSH, and SCP-like syntax — with no network; unrecognized schemes and padded URLs never match.
- `mk_all_declared` is **diagnostics-only** — consumers that need `mk_all` determine availability by actually running it, never by this field.

## Intent derivation (precedence: consumer flag > env > heuristic > default)

| Situation | `contributing_upstream` | `source` |
|---|---|---|
| `LEAN4_MATHLIB_INTENT=yes\|no` | that value | `env-override` |
| `LEAN4_MATHLIB_INTENT` set to anything else | `unknown` + warning (invalid values fall to the non-enforcing value) | `invalid-env-override` |
| any effective URL is canonical mathlib4 | `yes` | `remote-heuristic` |
| `other-lean` kind **and** `remote_scan: complete` **and** no canonical URL | `no` (both facts confident) | `remote-heuristic` |
| anything else (mathlib kind without canonical remote; scan failed/skipped; not-lean; kind unknown) | `unknown` | `default` |

Kind alone never implies intent — a bare mathlib clone is `unknown`, not `yes`. Consumer flags (`--mathlib-template`, `--mathlib-mk-all`, and their `--no-` forms) override per command and stay outside this helper; a consumer whose effective decision came from a flag reports that.

## Consumer rule for `unknown`

**Unknown context must never silently become an enforcement gate.** `yes` may enable mathlib-specific behavior; `no` disables it; `unknown` keeps existing behavior and may add a one-line advisory naming the opt-in flag — nothing more. Per-consumer contracts live in #174.

## Exit codes and failure behavior

`0` — context emitted (unknown facts are valid output); `2` — usage; `4` — operational (e.g. a nonexistent explicit `--from` path). Git absence, non-repository dirs, and remote-scan failures are **not** helper failures: exit 0 with honest `unknown`/`null` facts plus structured warnings.

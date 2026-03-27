---
name: lean4-contribute
description: Draft and submit lean4-skills bug reports, feature requests, and reusable insights with explicit consent gates.
---

# Lean4 Contribute (Codex)

Use this skill when the user wants to send actionable feedback to `cameronfreer/lean4-skills` as a bug report, feature request, or reusable insight.

Do not use this skill for theorem-proving help in Lean files; route that work to `lean4`.

## Command Surface

| Command | Purpose | Spec |
|---|---|---|
| `/lean4-contribute:bug-report` | Draft a bug report issue for lean4-skills | [`bug-report.md`](../../commands/bug-report.md) |
| `/lean4-contribute:feature-request` | Draft a feature request issue for lean4-skills | [`feature-request.md`](../../commands/feature-request.md) |
| `/lean4-contribute:share-insight` | Draft a shareable insight from your session as a GitHub issue | [`share-insight.md`](../../commands/share-insight.md) |

## Required Execution Contract

1. Require explicit opt-in before gathering structured context or mining diffs/logs.
2. Follow exactly one command spec at a time; do not blend templates across commands.
3. Show the complete draft (title, labels, full body) before any submit action.
4. Require explicit submit confirmation even after draft approval.
5. Submit via the fallback order in the command spec and report the final artifact URL or draft output.

## Command Specs

Read and execute the matching spec in `../../commands/`: `bug-report`, `feature-request`, `share-insight`.

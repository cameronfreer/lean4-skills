# Lean 4 Contribute Plugin

> **Contribution helper.** Draft and submit bug reports, feature requests, and
> shareable insights for [lean4-skills](https://github.com/cameronfreer/lean4-skills)
> as GitHub issues — directly from your editor.

**Privacy notice:** Commands may include Lean code snippets, diagnostics, or
diff fragments in the drafted issue body. Every draft is shown in full before
submission, and nothing is sent without your explicit confirmation.

## Commands

| Command | Description |
|---------|-------------|
| `/lean4-contribute:bug-report` | Draft a bug report issue |
| `/lean4-contribute:feature-request` | Draft a feature request issue |
| `/lean4-contribute:share-insight` | Draft a shareable insight from your session |

## How It Works

Each command follows the same three-step flow:

1. **Draft** — Gathers context (session state, diffs, diagnostics) and builds a
   structured issue body locally.
2. **Review** — Shows you the exact title, labels, and body that will be
   submitted. You can edit or cancel.
3. **Submit** — After your explicit confirmation, submits via the best available
   channel:
   - **`gh` CLI** — `gh issue create` on `cameronfreer/lean4-skills` (preferred)
   - **Browser** — Prefilled GitHub new-issue URL (fallback if `gh` unavailable)
   - **Email** — Draft email to `lean4skills@gmail.com` (offline fallback)

## Installation

```bash
/plugin install lean4-contribute
```

## What Each Command Shares

- **bug-report** — Summary, expected vs actual behavior, repro steps, a minimal
  Lean snippet, environment info, and build diagnostics. Optionally includes a
  possible-fix diff if one exists locally.
- **feature-request** — Problem description, current workaround, desired
  behavior, acceptance criteria, and alternatives considered.
- **share-insight** — A pattern, antipattern, or mixed insight inferred from
  your session, with a minimal example and context.

All drafts include a privacy/redaction check before submission.

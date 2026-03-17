---
name: share-insight
description: Draft a shareable insight from your session as a GitHub issue
user_invocable: true
---

# Share Insight

Draft and submit a reusable insight (pattern, antipattern, or mixed) as a
GitHub issue on `cameronfreer/lean4-skills`.

## Discovering Candidates

Before asking the user, look at:

- Current conversation / session context
- Current git diff (`git diff` and `git diff --cached`)
- Recently touched `.lean` files

From these, infer **1–5 candidate insights**. For each candidate, note:

- A one-line title
- Classification: **pattern** (what worked), **antipattern** (what failed), or
  **mixed** (worked in some contexts, failed in others)

Present the candidates as a numbered list and ask the user to pick one (or
describe a different insight). Proceed with the selected insight.

## Gathering Context

For the chosen insight, collect or infer:

1. **Kind** — pattern / antipattern / mixed
2. **Title** — Concise, descriptive title
3. **Context** — What were you working on when you discovered this?
4. **Symptom / trigger** — What behavior or error led to the discovery?
5. **What worked / what failed** — The core lesson
6. **Why it matters** — Impact on proving, performance, readability, or
   correctness
7. **Minimal example** — Smallest Lean snippet illustrating the insight (strip
   project-specific details)
8. **When to use / when not to** — Applicability boundaries
9. **Confidence** — High / medium / low — how sure are you this generalizes?
10. **Privacy / redaction check** — Scan for filesystem paths, usernames, API
    keys, or other sensitive data and redact them. Flag anything you redacted so
    the user can verify.

## Drafting the Issue

Compose the issue using this template:

```
Title: [Insight] <title>
Labels: insight

## Kind
<pattern / antipattern / mixed>

## Context
<what you were working on>

## Symptom / Trigger
<behavior or error that led to discovery>

## What Worked / What Failed
<core lesson>

## Why It Matters
<impact>

## Minimal Example
```lean
<minimal Lean snippet>
```

## When to Use / When Not To
<applicability boundaries>

## Confidence
<high / medium / low>
```

## Showing the Draft

Display the **complete** issue draft to the user — title, labels, and full body.
Also list any alternate candidates that were not selected, in case the user
wants to switch. Ask:

> Here is the insight I will submit. Review it carefully — it may contain code
> snippets from your session.
>
> **Submit this issue?** (yes / edit / switch to alternate / cancel)

Do **not** proceed unless the user explicitly confirms.

## Submitting

After confirmation, submit using the first available method:

1. **`gh` CLI** — Try: `gh issue create --repo cameronfreer/lean4-skills --title "<title>" --body "<body>" --label insight`.
   If the label fails (e.g. `insight` doesn't exist on the repo), retry without
   `--label` and note that the label was advisory only.
2. **Browser fallback** — Provide a prefilled GitHub URL:
   `https://github.com/cameronfreer/lean4-skills/issues/new?title=<url-encoded-title>&body=<url-encoded-body>&labels=insight`
   (the `labels=` param is best-effort; GitHub ignores unknown labels silently)
3. **Email fallback** — Draft an email to `lean4skills@gmail.com` with subject
   `[Insight] <title>` and the full issue body, for the user to send manually.

Report the result (issue URL, fallback URL, or email draft) and confirm
completion.

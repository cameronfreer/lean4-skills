---
name: feature-request
description: Draft a feature request issue for lean4-skills
user_invocable: true
---

# Feature Request

Draft and submit a feature request as a GitHub issue on `cameronfreer/lean4-skills`.

## Gathering Context

Collect the following from the user and the current session. Ask for anything
you cannot infer:

1. **Problem / pain point** — What is frustrating, slow, or missing?
2. **Current workaround** — How do you handle this today? (or "none")
3. **Desired behavior** — What should the plugin do instead?
4. **Why this belongs in the plugin** — Why is this a plugin concern rather than
   a user-side script or external tool?
5. **Acceptance criteria** — Concrete conditions that would mark this done
6. **Alternatives considered** — Other approaches you thought of and why they
   fall short
7. **Urgency / frequency** — How often do you hit this? Blocking, frequent
   annoyance, nice-to-have?

## Drafting the Issue

Compose the issue using this template:

```
Title: [Feature] <short description>
Labels: enhancement

## Problem / Pain Point
<problem description>

## Current Workaround
<workaround or "none">

## Desired Behavior
<what the plugin should do>

## Why This Belongs in the Plugin
<justification>

## Acceptance Criteria
- [ ] <criterion 1>
- [ ] <criterion 2>
- ...

## Alternatives Considered
<other approaches and trade-offs>

## Urgency / Frequency
<how often, how blocking>
```

## Showing the Draft

Display the **complete** issue draft to the user — title, labels, and full body.
Ask:

> Here is the feature request I will submit. Review it carefully.
>
> By submitting, you agree that this content may be incorporated into
> lean4-skills under its [MIT license](https://github.com/cameronfreer/lean4-skills/blob/main/LICENSE).
>
> **Submit this issue?** (yes / edit / cancel)

Do **not** proceed unless the user explicitly confirms.

## Submitting

After confirmation, submit using the first available method:

1. **`gh` CLI** — Try: `gh issue create --repo cameronfreer/lean4-skills --title "<title>" --body "<body>" --label enhancement`.
   If the label fails (e.g. `enhancement` doesn't exist on the repo), retry
   without `--label` and note that the label was advisory only.
   If `gh` fails for auth or network reasons, **stop** — do not retry. Fall
   through to the browser or email path immediately.
2. **Browser fallback** — Provide a prefilled GitHub URL:
   `https://github.com/cameronfreer/lean4-skills/issues/new?title=<url-encoded-title>&body=<url-encoded-body>&labels=enhancement`
   (the `labels=` param is best-effort; GitHub ignores unknown labels silently)
3. **Email fallback** — Draft an email to `lean4skills@gmail.com` with subject
   `[Feature] <short description>` and the full issue body, for the user to
   send manually.

Report the result (issue URL, fallback URL, or email draft) and confirm
completion.

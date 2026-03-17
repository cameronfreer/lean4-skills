---
name: bug-report
description: Draft a bug report issue for lean4-skills
user_invocable: true
---

# Bug Report

Draft and submit a bug report as a GitHub issue on `cameronfreer/lean4-skills`.

## Gathering Context

Collect the following from the user and the current session. Ask for anything
you cannot infer:

1. **Summary** — One-line description of the bug
2. **Expected behavior** — What should happen
3. **Actual behavior** — What happens instead
4. **Repro steps** — Numbered steps to reproduce
5. **Minimal Lean snippet** — Smallest code that triggers the bug (strip
   project-specific details)
6. **Environment / toolchain** — Lean version (`lean --version`), lake version,
   OS, plugin version, relevant MCP servers
7. **Diagnostics / build output** — Compiler errors, lake build output, or LSP
   messages (redact paths and usernames)
8. **Possible fix** (optional) — If there is a meaningful local diff that
   addresses the issue, include it as a suggested patch
9. **Privacy / redaction check** — Before showing the draft, scan for
   filesystem paths, usernames, API keys, or other sensitive data and redact
   them. Flag anything you redacted so the user can verify.

## Drafting the Issue

Compose the issue using this template:

```
Title: [Bug] <summary>
Labels: bug

## Summary
<summary>

## Expected Behavior
<expected behavior>

## Actual Behavior
<actual behavior>

## Steps to Reproduce
<numbered repro steps>

## Minimal Example
```lean
<minimal Lean snippet>
```

## Environment
- Lean: <version>
- Lake: <version>
- OS: <os>
- Plugin: <version>
- MCP: <servers if relevant>

## Diagnostics
<build output / compiler errors>

## Possible Fix
<diff or suggestion, if any>
```

## Showing the Draft

Display the **complete** issue draft to the user — title, labels, and full body.
Ask:

> Here is the bug report I will submit. Review it carefully — it may contain
> code snippets from your project.
>
> **Submit this issue?** (yes / edit / cancel)

Do **not** proceed unless the user explicitly confirms.

## Submitting

After confirmation, submit using the first available method:

1. **`gh` CLI** — Run: `gh issue create --repo cameronfreer/lean4-skills --title "<title>" --body "<body>" --label bug`
2. **Browser fallback** — Provide a prefilled GitHub URL:
   `https://github.com/cameronfreer/lean4-skills/issues/new?title=<url-encoded-title>&body=<url-encoded-body>&labels=bug`
3. **Email fallback** — Draft an email to `lean4skills@gmail.com` with subject
   `[Bug] <summary>` and the full issue body, for the user to send manually.

Report the result (issue URL, fallback URL, or email draft) and confirm
completion.

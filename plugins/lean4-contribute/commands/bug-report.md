---
name: bug-report
description: Draft a bug report issue for lean4-skills
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
8. **Possible fix** (optional) — If you have a local fix, write a short
   **prose summary** of what the fix does (1–3 sentences). Do **not** include
   a raw diff by default. If the user explicitly asks to include a patch
   excerpt, include only the minimal relevant hunk (not the whole diff), strip
   file paths and surrounding context, and require a separate confirmation:
   > This draft includes a code patch. Review it for unrelated code or secrets.
   > **Include this patch?** (yes / remove it / edit)
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
<prose summary of fix; minimal patch excerpt only if user confirmed>

---
*Drafted via [lean4-contribute](https://github.com/cameronfreer/lean4-skills)*
```

## Showing the Draft

Display the **complete** issue draft to the user — title, labels, and full body.
Ask:

> Here is the bug report I will submit. Review it carefully — it may contain
> code snippets from your project.
>
> By submitting, you agree that this content may be edited, rearranged, or
> incorporated into lean4-skills in any form under its
> [MIT license](https://github.com/cameronfreer/lean4-skills/blob/main/LICENSE).
>
> **Submit this issue?** (yes / edit / cancel)

Do **not** proceed unless the user explicitly confirms.

## Submitting

After confirmation, submit using the first available method:

1. **`gh` CLI** — Try: `gh issue create --repo cameronfreer/lean4-skills --title "<title>" --body "<body>" --label bug`.
   If the label fails (e.g. `bug` doesn't exist on the repo), retry without
   `--label` and note that the label was advisory only.
   If `gh` fails for auth or network reasons, **stop** — do not retry. Fall
   through to the browser or email path immediately.
2. **Browser fallback** — Provide a prefilled GitHub URL:
   `https://github.com/cameronfreer/lean4-skills/issues/new?title=<url-encoded-title>&body=<url-encoded-body>&labels=bug`
   (the `labels=` param is best-effort; GitHub ignores unknown labels silently)
3. **Email fallback** — Draft an email to `lean4skills@gmail.com` with subject
   `[Bug] <summary>` and the full issue body, for the user to send manually.

Report the result (issue URL, fallback URL, or email draft) and confirm
completion.

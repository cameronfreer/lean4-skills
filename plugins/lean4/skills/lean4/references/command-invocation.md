# Command Invocation Contract

Slash-command inputs in this plugin are **model-parsed, not host-parsed**. The
host passes the raw text after `/lean4:<command>` to the agent; it does **not**
apply a schema, validate enums, coerce values, or enforce timeouts on the
plugin's behalf.

## Required Startup Behavior

Any command that advertises flags must do all of the following before
substantive work:

1. Parse the raw invocation text against the command's documented input table.
2. Emit a **Resolved Inputs** summary showing:
   - explicit values supplied by the user
   - defaults that were assumed
   - coercions or ignored flags
   - startup validation errors
3. Refuse to start on startup validation errors. Do not partially begin a
   session and then discover a missing required companion flag later.
4. Maintain promised session counters explicitly (`cycles_run`,
   `stuck_cycles`, `deep_invocations`, and similar state) rather than relying on
   the model to remember them informally.

## Enforcement Classes

Document each flag according to the strongest guarantee the current architecture
can actually provide:

- **Startup-validated**: syntax, enums, required companion flags, path safety,
  overwrite checks, and other checks that can be decided before work starts.
- **Session-enforced**: counters and mode switches that the command re-checks at
  safe boundaries during the session.
- **Best-effort**: budgets that depend on wall-clock time or other values the
  host does not enforce. These must be checked explicitly by the command, but
  they are not kill switches.
- **Advisory**: preferences that guide planning or presentation but are not
  safety or stop guarantees.

Never describe a **best-effort** control as a **hard stop**.

## Wall-Clock Budgets

`--max-total-runtime` is the clearest example of a best-effort control:

- record a start timestamp before the main loop begins
- re-check elapsed wall-clock time with `date +%s` (or equivalent) at cycle
  boundaries and before expensive optional branches such as deep mode
- stop before starting the next unit of work when the budget has been exhausted

Do **not** claim that `--max-total-runtime` can preempt a long-running tool call
mid-step. The host does not provide that guarantee here.

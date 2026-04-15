# Command Invocation Contract

This plugin ships a host-agnostic parser (`lib/command_args/`) that covers the
**parser-decidable** startup rules of the six parameter-heavy commands —
`draft`, `learn`, `formalize`, `autoformalize`, `prove`, and `autoprove`.
Parser-decidable rules are those whose outcome can be fully determined from
flags, positionals, and `os.path.exists` checks alone, without repo-level
search or interactive user prompting. A small set of documented startup rules
in these commands depend on runtime context the parser cannot evaluate (e.g.
local-declaration resolution in learn); those are listed in the forward-
exclusions and are applied by the command at runtime after reading the parser's
output. Other commands in this plugin (`checkpoint`, `review`, `refactor`,
`golf`, `doctor`) are not parameter-heavy and are not covered by
`lib/command_args/`; they remain model-parsed on every host.

For the six covered commands, whether the parser actually runs before the
model sees a slash-command invocation depends on the host adapter:

- The **Claude Code adapter** invokes the parser from a `UserPromptSubmit`
  hook before the model sees the prompt and rejects invalid invocations with
  a hook-level block.
- **Other host adapters** MAY invoke the same parser via
  `lib/scripts/parse_command_args.py`. Hosts that do not integrate the parser
  fall back to the model-parsed **Required Startup Behavior** below — on
  those hosts, slash-command inputs remain model-parsed.

Regardless of host or command, the plugin does **not** enforce wall-clock
budgets on the plugin's behalf — those remain best-effort and are re-checked
at safe boundaries by the command itself.

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

## Validated Invocation Block (host-provided)

A host adapter MAY pre-parse a slash-command invocation and inject the result
into the model's context as a fenced `validated-invocation` block. The block is
a lossless serialization of the host parser's `ParseResult`.

When such a block appears in context for the current `/lean4:<command>`
invocation, the command **MUST** treat it as the authoritative interpretation
of **parser-decidable** inputs and **MUST NOT** re-parse the raw invocation
text for those inputs.

Commands that have **repo-dependent startup rules** — rules whose outcome
depends on runtime context the host parser cannot evaluate — MAY apply
those rules after reading the block, refining specific fields with runtime
context. The command's emitted Resolved Inputs summary may differ from the
block for forward-excluded fields only; for all parser-decided fields, the
Resolved Inputs MUST match the block exactly.

When no `validated-invocation` block appears (non-Claude hosts, or hosts that
have not installed the parser hook), the command falls back to the
**Required Startup Behavior** above and parses the raw text itself.

A `validated-invocation` block carrying any startup-validation error never
reaches the model: the host adapter rejects the prompt before invocation. A
block carrying only warnings reaches the model and the command surfaces those
warnings in its Resolved Inputs summary.

## Adapter Implementations

- **Default (model-parsed):** non-Claude hosts pass the raw tail to the model;
  the command parses it per the Required Startup Behavior above.
- **Claude plugin (hook-validated):** the `UserPromptSubmit` hook
  `hooks/validate_user_prompt.py` parses `/lean4:*` prompts via
  `lib/command_args/` before the model sees them. Hard errors are returned to
  the user as a hook rejection; successful parses are injected as a
  `validated-invocation` block. Other hosts can call the same parser via
  `lib/scripts/parse_command_args.py`.

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

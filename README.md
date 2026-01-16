# Lean 4 Skills for Claude

Claude Skills, commands, and agents for systematic development of formal proofs in Lean 4.

## Plugins in This Repository

| Plugin | Provides | Description | Requirements |
|--------|----------|-------------|--------------|
| **[lean4-theorem-proving](plugins/lean4-theorem-proving/)** | Skill + 6 Commands | Core workflows, 16 automation tools, best practices | None |
| **[lean4-memories](plugins/lean4-memories/)** | Skill (EXPERIMENTAL) | Persistent learning across sessions | lean4-theorem-proving + MCP memory server |
| **[lean4-subagents](plugins/lean4-subagents/)** | 3 Agents (EXPERIMENTAL) | Specialized agents for proof optimization, sorry filling, axiom elimination | lean4-theorem-proving |
| **[lean4-metaprogramming](plugins/lean4-metaprogramming/)** | Skill | DSLs, macros, elaborators, custom pretty-printing | None |
| **[lean4-linters](plugins/lean4-linters/)** | Skill | Project-specific linters and hygiene rules | None |
| **[lean4-verso-docs](plugins/lean4-verso-docs/)** | Skill | Verso roles and doc comment hygiene | None |
| **[lean4-ffi](plugins/lean4-ffi/)** | Skill | C/ObjC FFI patterns and Lake linking | None |
| **[lean4-profiling](plugins/lean4-profiling/)** | Skill | Profiling Lean elaboration and compilation | None |
| **[lean4-simprocs](plugins/lean4-simprocs/)** | Skill | Simproc design within the simp pipeline | None |
| **[lean4-grind](plugins/lean4-grind/)** | Skill | `grind` workflows and bounds | None |

## Quick Start

**Via Marketplace (Recommended):**
```bash
/plugin marketplace add cameronfreer/lean4-skills
/plugin install lean4-theorem-proving    # Core skill + commands (REQUIRED)
/plugin install lean4-memories           # Optional: adds persistent memory (requires lean4-theorem-proving)
/plugin install lean4-subagents          # Optional: adds specialized agents (requires lean4-theorem-proving)
/plugin install lean4-metaprogramming    # Optional: DSLs, macros, elaborators
/plugin install lean4-linters            # Optional: project-specific linters
/plugin install lean4-verso-docs         # Optional: Verso roles and doc hygiene
/plugin install lean4-ffi                # Optional: C/ObjC FFI patterns
/plugin install lean4-profiling          # Optional: profiler workflows
/plugin install lean4-simprocs           # Optional: simproc playbook
/plugin install lean4-grind              # Optional: grind playbook
```

**Note:** lean4-theorem-proving is the foundation for proof workflows. Other plugins are optional and independent unless noted.

**Manual Installation:**
```bash
git clone https://github.com/cameronfreer/lean4-skills.git
cd lean4-skills

# Install core skill + commands (REQUIRED - foundation for other plugins)
cp -r plugins/lean4-theorem-proving ~/.claude/skills/

# Install memory skill (optional, requires lean4-theorem-proving + MCP memory server)
cp -r plugins/lean4-memories ~/.claude/skills/

# Install specialized agents (optional, requires lean4-theorem-proving)
cp -r plugins/lean4-subagents ~/.claude/skills/

# Install metaprogramming skill (optional)
cp -r plugins/lean4-metaprogramming ~/.claude/skills/

# Install linters skill (optional)
cp -r plugins/lean4-linters ~/.claude/skills/

# Install Verso docs skill (optional)
cp -r plugins/lean4-verso-docs ~/.claude/skills/

# Install FFI skill (optional)
cp -r plugins/lean4-ffi ~/.claude/skills/

# Install profiling skill (optional)
cp -r plugins/lean4-profiling ~/.claude/skills/

# Install simprocs skill (optional)
cp -r plugins/lean4-simprocs ~/.claude/skills/

# Install grind skill (optional)
cp -r plugins/lean4-grind ~/.claude/skills/
```

➡️ **Platform-specific setup (Windows, LSP server, etc.):** [INSTALLATION.md](INSTALLATION.md)

### Usage

**Skills** activate automatically when you work on Lean 4 files. **Commands** appear in autocomplete with `/lean4-theorem-proving:` prefix. **Agents** are available via the Task tool.

**Toggle plugins on/off:**
```bash
/plugin disable lean4-memories    # Disable memory skill
/plugin enable lean4-memories     # Re-enable memory skill
/plugin disable lean4-subagents   # Disable specialized agents
/plugin disable lean4-metaprogramming
/plugin disable lean4-linters
/plugin disable lean4-verso-docs
/plugin disable lean4-ffi
/plugin disable lean4-profiling
/plugin disable lean4-simprocs
/plugin disable lean4-grind
```

## lean4-theorem-proving

Systematic workflows for Lean 4 proof development.

**What you get:**
- **Lean LSP server integration** - 30x faster feedback (< 1s vs 30s builds)
- 4-Phase proof development workflow (structure → helpers → incremental → type classes)
- 16 automation scripts (search, analysis, verification, refactoring)
- Type class management patterns
- mathlib integration guide
- Domain-specific tactics (measure theory, probability, algebra)

**Perfect for:**
- Any Lean 4 formalization project
- Learning Lean 4 from other proof assistants
- Managing sorries, axioms, and type class issues
- Contributing to mathlib

➡️ **[Full Documentation](plugins/lean4-theorem-proving/README.md)**

## lean4-memories (EXPERIMENTAL)

Optional persistent learning across Lean 4 sessions. Extends lean4-theorem-proving with memory.

**What you get:**
- Remember successful proof patterns
- Avoid repeating failed approaches (infinite loops, timeouts)
- Learn project-specific conventions
- Track theorem dependencies

**Perfect for:**
- Multi-session projects (days/weeks/months)
- Repeated proof patterns
- Team projects with shared knowledge

**Requires:**
- lean4-theorem-proving plugin (provides the workflows this extends)
- MCP memory server configuration

➡️ **[Full Documentation](plugins/lean4-memories/README.md)**

## lean4-subagents (EXPERIMENTAL)

Specialized agents for targeted Lean 4 development tasks. Extends lean4-theorem-proving with automation.

**What you get:**
- **lean4-proof-golfer** - Optimize proofs by reducing length/runtime (30-40% reduction)
- **lean4-sorry-filler** - Fill in sorry placeholders systematically
- **lean4-axiom-eliminator** - Eliminate custom axioms, reduce axiom count to zero

**Perfect for:**
- Polishing proofs before publication
- Batch-filling sorries in development
- Ensuring axiom-free theorems

**Requires:** lean4-theorem-proving plugin (agents use its workflows and patterns)

**Usage:** Available via Task tool when lean4-subagents is installed

➡️ **[Full Documentation](plugins/lean4-subagents/README.md)**

## lean4-metaprogramming

Metaprogramming patterns for building DSLs, macros, elaborators, and custom pretty-printing.

**Perfect for:**
- Creating domain-specific languages and custom syntax
- Validating DSL inputs with precise error spans
- Adding unexpanders/delaborators for readable output

➡️ **[Full Documentation](plugins/lean4-metaprogramming/README.md)**

## lean4-linters

Project-specific linter patterns with templates for options, warnings, and errors.

**Perfect for:**
- Enforcing project style and safety rules
- Catching slow or unsafe patterns early
- Keeping warnings consistent and actionable

➡️ **[Full Documentation](plugins/lean4-linters/README.md)**

## lean4-verso-docs

Verso doc comment hygiene, role usage, and hover-friendly references.

**Perfect for:**
- Fixing doc.verso warnings
- Keeping inline code resolvable and precise

➡️ **[Full Documentation](plugins/lean4-verso-docs/README.md)**

## lean4-ffi

Lean 4 FFI patterns for C/ObjC bindings with Lake linking guidance.

**Perfect for:**
- External library bindings
- C struct layout via `@[cstruct]`

➡️ **[Full Documentation](plugins/lean4-ffi/README.md)**

## lean4-profiling

Profiling workflows to locate elaboration and compilation hotspots.

**Perfect for:**
- Slow builds and tactics
- Trace-based performance triage

➡️ **[Full Documentation](plugins/lean4-profiling/README.md)**

## lean4-simprocs

Simproc design as part of the simp pipeline.

**Perfect for:**
- Repetitive rewrite goals
- Deterministic rewrites inside `simp`

➡️ **[Full Documentation](plugins/lean4-simprocs/README.md)**

## lean4-grind

`grind` usage playbook with normalization-first workflow and bounds.

**Perfect for:**
- Goals that close after normalization
- Premise-bounded automated closure

➡️ **[Full Documentation](plugins/lean4-grind/README.md)**

## How They Work Together

**Example: Proving `condExp μ m X =ᵐ[μ] condExp μ m Y`**

1. **lean4-theorem-proving skill** activates, provides workflows and mathlib patterns
2. Use **/lean4-theorem-proving:build-lean** command for formatted error analysis
3. **lean4-memories** recalls: "Similar goals in this project used `condExp_unique` + `ae_eq` pattern (success rate: 3/3)"
4. After proving, use **lean4-proof-golfer agent** to optimize from 15 lines → 6 lines

Result: Faster development with systematic optimization!

## Requirements

**For lean4-theorem-proving:**
- Claude Code 2.0.13+ (marketplace) OR
- Claude.ai Pro/Max/Team/Enterprise OR
- Any Claude (CLAUDE.md method)

**For lean4-memories (additional):**
- MCP memory server (simple config file edit - [setup guide](lean4-memories/README.md#installation))
- Claude Desktop or Claude Code with MCP support

**For Lean LSP server (optional but highly recommended):**
- Setup guide: [INSTALLATION.md](INSTALLATION.md#lean-lsp-server)
- Source: https://github.com/oOo0oOo/lean-lsp-mcp
- Benefit: 30x faster proof development

## Documentation

- **[lean4-theorem-proving/README.md](plugins/lean4-theorem-proving/README.md)** - Core skill guide
- **[lean4-memories/README.md](plugins/lean4-memories/README.md)** - Memory skill guide
- **[lean4-subagents/README.md](plugins/lean4-subagents/README.md)** - Specialized agents guide
- **[lean4-metaprogramming/README.md](plugins/lean4-metaprogramming/README.md)** - Metaprogramming patterns
- **[lean4-linters/README.md](plugins/lean4-linters/README.md)** - Linter templates and workflows
- **[lean4-verso-docs/README.md](plugins/lean4-verso-docs/README.md)** - Verso doc role usage
- **[lean4-ffi/README.md](plugins/lean4-ffi/README.md)** - FFI patterns and linking
- **[lean4-profiling/README.md](plugins/lean4-profiling/README.md)** - Profiling workflows
- **[lean4-simprocs/README.md](plugins/lean4-simprocs/README.md)** - Simproc playbook
- **[lean4-grind/README.md](plugins/lean4-grind/README.md)** - Grind playbook
- **[lean4-theorem-proving/scripts/](plugins/lean4-theorem-proving/scripts/)** - 16 automation tools
- **[lean4-theorem-proving/references/](plugins/lean4-theorem-proving/references/)** - Detailed guides

## Status

**Version:** 3.1.0
**Status:** Production-ready
**Last Updated:** October 2025

Recent updates:
- v3.1.0: Restructured as Claude Code marketplace with 3 plugins (skill + commands + agents)
- v3.0.0: Added lean4-memories skill (optional MCP memory integration)
- v2.1.0: Added 16 automation scripts (search, analysis, verification)
- v2.0.0: Progressive disclosure restructuring

## Contributing

Contributions welcome! Open an issue or PR at https://github.com/cameronfreer/lean4-skills

## License

MIT License - see [LICENSE](LICENSE)

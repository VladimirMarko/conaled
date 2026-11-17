# Repository direction

This Lean monorepo extends Conal Elliott's work. Build the best possible library:
sound mathematics, useful capabilities, clear interfaces, and maintainable code.

Use history to recover useful work, understand constraints and avoid repeated
mistakes. Assess interfaces against current needs rather than age. Keep records
and review proportional to correctness, usability, maintenance and recovery;
preserve useful mathematics and validation, and prune incidental history.

## Task guidance

- Before undertaking or delegating work, read
  [task authority and capability](docs/agents/task-authority.md).
- Before editing `AGENTS.md`, read
  [writing-for-agents](.agents/skills/writing-for-agents/SKILL.md). Keep this file
  compact: universal rules and pointers with explicit reading triggers. Put
  situational detail in existing guides where appropriate; preserve requirements
  and their discovery paths when moving them, rather than duplicating guidance.
- Before exploring domain concepts or architecture, read the
  [domain guide](docs/agents/domain.md).
- Before designing or reviewing library abstractions, read
  [architectural quality](docs/agents/architectural-quality.md).
- Before prioritizing architectural work or making trial/adoption decisions,
  read the [planning guidance](docs/language-direction.md#elegance-author-capability-and-language-constraints).
- Before running project commands, read the
  [development environment](README.md#development-environment); before changing
  tooling, read the [toolchain guidance](docs/development.md#development-environment).
- Before choosing validation, read the [build and audit guidance](README.md#build-and-audit).
- For unexpected Lake integrity invalidation, failed integrity checks or suspected
  stale artifacts, follow the [incident runbook](docs/agents/lake-integrity-incidents.md).
- Before writing or reviewing Lean code, or using historical formalizations,
  read [formal development](docs/agents/formal-development.md).
- Before tracker operations, read the [issue tracker guide](docs/agents/issue-tracker.md).

## Implementation and completion

For implementation, including documentation, tooling and skill changes, use
[implement](.agents/skills/implement/SKILL.md). Independent Standards and Spec
review is required unless the user changes that requirement. Continue an assigned
implementation/review loop rather than starting another; planning and read-only
investigation do not start a loop.

Before committing, publishing or finishing an implementation turn, follow
[completion and publication](docs/agents/completion.md).

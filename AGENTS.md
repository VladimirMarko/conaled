# Repository direction

This is a planned Lean monorepo extending Conal Elliott's work.

## Architectural quality

Felix is the minimum standard for elegance, expressive power, and architecture.
Before designing or reviewing library abstractions, read
`docs/agents/architectural-quality.md`.

## Development environment

Use the Nix flake shell through direnv. Before running project commands or
changing tooling, read the development environment section in `README.md`.
For noninteractive commands, use `direnv exec . <command>` or
`nix develop --command <command>`.
Agents may add required tooling to `flake.nix`; keep it pinned through the
checked-in `flake.lock` and validate changes with `nix flake check` and a shell
smoke check. Lean and library versions remain in `lean-toolchain` and the Lake
files.

## Agent skills

### Formal development

When adding or changing Lean definitions and theorems, use
`.agents/skills/example-driven-development/SKILL.md` to develop checked
specializations and applications alongside the theory. For every new or changed
formal claim, perform its statement review to check that the formalization
expresses the intended mathematics. Reuse existing cases where they suffice.
Use `tdd` when executable behavior needs runtime tests.

### Issue tracker

Track issues and specs in GitHub Issues for VladimirMarko/conaled.
Before tracker operations, read `docs/agents/issue-tracker.md`.

### Triage labels

Use the five canonical triage labels.
Before triaging issues, read `docs/agents/triage-labels.md`.

### Domain docs

Use a single-context layout across the monorepo.
Before exploring domain concepts or architecture, read
`docs/agents/domain.md`.

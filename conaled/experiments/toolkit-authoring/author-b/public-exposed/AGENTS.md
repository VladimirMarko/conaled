# Repository direction

This is a planned Lean monorepo extending Conal Elliott's work.

## Architectural quality

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

## Implementation and validation

For implementation tasks, including documentation, tooling, and skill changes,
use `.agents/skills/implement/SKILL.md` by default. Independent Standards and
Spec review is part of completion unless the user explicitly changes that
requirement. When already assigned work within an implementation/review loop,
continue that loop rather than starting another. Planning and read-only
investigation do not start an implementation loop.

Before choosing validation for a change, read the build and audit section in
`README.md`. Match checks to the changed artifacts; formal changes require
the applicable build and proof audit using the acceptance modes defined there.
The implementation workflow owns review coordination, including reuse when
originator review is requested.

## Commit messages

Use Conventional Commits: `type(scope): description (#123)`.
The scope is optional; the trailing issue number is required when an issue applies.
Example: `docs: clarify agent guidance (#123)`.

## Agent skills

### Formal development

Before using the standalone orbifold formalization as a source, proof reference,
or implementation example, read
`docs/history/orbifold/standalone-formalization/README.md`.

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

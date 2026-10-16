# Repository direction

This is a planned Lean monorepo extending Conal Elliott's work.

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

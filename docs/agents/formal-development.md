# Formal development

For new and changed Lean code, follow
[Mathlib's naming conventions](https://mathlib.org/contribute/naming.html),
including acronym casing and embedded identifiers in theorem names.

When adding or changing Lean definitions and theorems, use
[example-driven development](../../.agents/skills/example-driven-development/SKILL.md)
to develop checked specializations and applications alongside the theory. For
every new or changed formal claim, perform its statement review to check that
the formalization expresses the intended mathematics. Reuse existing cases where
they suffice. Use [tdd](../../.agents/skills/tdd/SKILL.md) when executable behavior
needs runtime tests.

Formal changes require the applicable build and proof audit using the acceptance
modes in the [build and audit guide](../development.md#build-and-audit).

Before using the standalone orbifold formalization as a source, proof reference,
or implementation example, read its
[source guide](../history/orbifold/standalone-formalization/README.md).

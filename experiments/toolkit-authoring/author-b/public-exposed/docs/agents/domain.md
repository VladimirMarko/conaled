# Domain documentation

This monorepo currently uses one shared domain context:

- `GLOSSARY.md` at the repository root defines shared vocabulary.
- `docs/adr/` holds architecture decision records.

## Before exploring

Read the glossary if present. Read `docs/adr/README.md`, then the
ADRs relevant to the area being explored.

If a document is absent, continue silently. Create domain documents
through `/domain-modeling` when terms or decisions are resolved.

## Vocabulary and decisions

Use glossary terms in issue titles, proposals, hypotheses, code,
and tests. Respect any distinctions and discouraged synonyms it
records. If a needed concept is missing, check existing usage and
note a real vocabulary gap for `/domain-modeling`.

If a proposal conflicts with an ADR, name the ADR and explain
why the decision should be reconsidered.

Keep the shared layout until distinct domain contexts justify
separate glossaries.

# Completion and publication

After the required validation and review pass, normally commit the completed
work, integrate it into `master`, push `master`, and close completed issues with
comments summarizing the result, validation and any follow-ups. Carry these steps
through without another permission request. Review and deliberation can be
intermediate phases; normally finish publication and issue closure before ending
the turn. If a concrete reason prevents a step, report that reason and what
remains. Preserve unrelated user work and obey explicit instructions to defer
publication. Unfinished scope stays open; separately tracked extensions do not
prevent closing a completed deliverable.

The [implementation workflow](../../.agents/skills/implement/SKILL.md) owns review
coordination, including reuse when originator review is requested. Follow the
[tracker guide](issue-tracker.md) when commenting on or closing issues.

## Commit messages

Use Conventional Commits: `type(scope): description (#123)`.
The scope is optional; the trailing issue number is required when an issue applies.
Example: `docs: clarify agent guidance (#123)`.

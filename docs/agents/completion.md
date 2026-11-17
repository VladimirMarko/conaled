# Completion and publication

Completion means the requested deliverable has passed required validation and
review and been delivered within the [task's authority](task-authority.md).
A validated and reviewed local deliverable completes a local assignment;
publication is required only when selected or explicitly authorized as part of
the requested outcome. Keep affected issues accurate within the authorized scope.
When the full completion workflow is selected, after required validation and
review pass, normally commit the completed work, integrate it into `master`, push
`master`, and close completed issues with comments summarizing the result,
validation and follow-ups. Carry these steps through without another permission
request, within the selected scope and permissions. Review and deliberation can be
intermediate phases; normally finish authorized publication and issue closure
before ending the turn.

If a concrete reason prevents a step, report that reason and what remains.
Preserve unrelated user work and obey explicit instructions to defer publication.
Unfinished scope stays open; separately tracked extensions do not prevent closing
a completed deliverable. If required publication is blocked, keep that deliverable
open and continue independently authorized issue maintenance with its status clear.

The [implementation workflow](../../.agents/skills/implement/SKILL.md) owns review
coordination, including reuse when originator review is requested. Follow the
[tracker guide](issue-tracker.md) when commenting on or closing issues.

## Commit messages

Use Conventional Commits: `type(scope): description (#123)`.
The scope is optional; the trailing issue number is required when an issue applies.
Example: `docs: clarify agent guidance (#123)`.

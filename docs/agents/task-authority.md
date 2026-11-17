# Task authority and capability

This policy selects a workflow for convenience, predictability and completing
the important work steps. It is not an authentication system, identity
verification or access control. Workflow selection does not grant repository
rights; the permissions required for each action still apply.

Requests from Vladimir Marko select the full completion workflow by default.
A Git `user.name` of `Vladimir Marko` is sufficient as a practical default for
that selection unless the conversation indicates otherwise. Other authorized
contributors may explicitly opt into the same workflow: finish the requested
deliverable, including committing, integrating into `master`, pushing `master`,
reconciling related issues and closing completed ones. Credentials, repository
access or merely discovering an issue do not by themselves select this workflow.

Carry the selected workflow, task scope and explicit restrictions through
delegations and continuations without asking for confirmation again. When no
selection is established, continue useful local work without committing or
publishing; if publication is needed, ask once whether to use the full completion
workflow, explaining its effects. Follow
[completion and publication](completion.md) within the selected scope and the
[tracker guide](issue-tracker.md) for related issue maintenance.

Use GPT-6-Astra at medium or higher reasoning effort. Other models require
explicit approval from Vladimir Marko. This requirement applies uniformly across
tasks to the primary agent and every delegated agent, including reviewers.
Verify the model and reasoning configuration before undertaking or delegating
work. If an approved configuration is unavailable or cannot be verified, report
the mismatch before proceeding with covered work; reading this policy and
explaining the mismatch remain allowed.

The repository's purpose guides proposals to revise this policy. It does not
authorize an agent to bypass it.

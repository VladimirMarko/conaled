# Task authority and capability

This policy selects a workflow for convenience, predictability and completing
the important work steps. It is not an authentication system, identity
verification or access control. Workflow selection does not grant repository
rights; the permissions required for each action still apply.

## Workflow selection

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
publishing. Permission for a named external action covers that action, not the
whole workflow. Prepare the authorized work first; if a necessary prerequisite
falls outside that scope, ask once for the missing authorization and explain its
effects. Follow
[completion and publication](completion.md) within the selected scope and the
[tracker guide](issue-tracker.md) for related issue maintenance.

Here, committing means adding deliverable commits to branch history. Local work
and ordinary no-commit instructions still permit the required internal review
snapshots, which create Git objects without changing branch history or publishing.
Respect an explicit prohibition of Git object creation; the
[review procedure](review-loop.md#candidate-and-record) handles that constraint.

## Model eligibility and trials

The [approved configurations](../../.agents/model-policy.json) define repository
defaults. Vladimir Marko sets those defaults and may approve other configurations for
specified work, including an agent with unknown model or effort. Accept recorded
conversational approval or its relay by the orchestrator without separate identity
authentication. Approval persists through continuations and delegation only for
the agents, work and limits it covers; it does not automatically cover a different
agent or task.

Configuration selection and monitoring belong to the operator and host, for
primary and delegated agents including reviewers. Agents concentrate on the task:
do not poll runtime metadata, self-attest configuration, or stop work to ask about
unknown model or effort. When delegation controls expose model and effort, select
an approved configuration or one covered by the scoped approval. Carry that
approval forward without repeated verification questions. Output quality does
not establish approval. The [optional Codex CLI warning](model-warning.md)
provides host-side feedback without adding model context or blocking work;
other tools can use their own monitoring.

A task requester may explicitly authorize a bounded local suitability trial of
another or unknown configuration, including actual implementation work. Record
the trial's scope, limits and known configuration. This approval covers only the
trial; its author cannot promote the configuration to general approval or infer
publication authority. Integrating trial artifacts requires separate authority,
the usual validation, and independent review by agents eligible for that
integration beyond the local trial. Trial results inform model approval decisions;
they do not make those decisions.

The repository's purpose guides proposals to revise this policy. It does not
authorize an agent to bypass it.

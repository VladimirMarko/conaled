---
name: design-challenge
description: Assess a proposed or existing design through three independent subagents with complementary perspectives, then synthesize evidence and next steps. Use for challenging architectural decisions or assumptions, rather than routine code acceptance or generating competing interface sketches.
---

# Design Challenge

Test whether a design serves its intended goals and whether its assumptions,
obligations and boundaries are justified. Use three additional agents with
different questions to investigate. Their agreement is evidence to examine,
not a vote that establishes correctness.

## Frame the decision

Read the applicable project guidance and the relevant design, implementation
and consumers. Write a shared brief containing:

- The decision or hypothesis, intended capability, and the user's concern.
- Actual constraints, what may change, and observations or clients to preserve.
- The candidate design and its rationale, distinguished from requirements.
- Pinned source/document versions, relevant examples, known evidence and open
  questions. Identify uncommitted inputs when they are part of the assessment.
- The three perspectives, their different questions, permitted experiments,
  output locations, and any limits on scope or resources.

Keep the brief neutral about the verdict. Supply facts and user constraints to
all agents; withhold the coordinator's preferred conclusion and other agents'
findings. Resolve facts from available sources before asking the user. A missing
decision blocks only the assessment that depends on it.

## Choose complementary perspectives

Choose lenses that could reveal different failure modes. For a library or
language architecture, the following worked well:

| Perspective | Main question |
| --- | --- |
| Contract and foundations | Do the operations and laws establish the intended guarantees? Which requirements are derived, independent, specialized or still unproved? |
| Implementation and use | Where do obligations fall on builders and callers? Which couplings, representations or migration costs obstruct the intended capability? |
| Alternatives and generality | Could a different formulation or foundation serve the goal better? What assumptions does the current design conceal or unnecessarily impose? |

Adapt these to the task, for example by making performance, reliability or
security a lens when it is central to the decision. Explain the selection in
the brief. Each agent may report a cross-cutting concern; lenses focus inquiry
without assigning exclusive ownership of facts. The alternatives agent should
look beyond local precedent when relevant, rather than reject a competing
approach because it lacks an adapter to the current design.

## Obtain independent assessments

Spawn three fresh subagents with minimal context (`fork_turns="none"` where
available). Give each the shared brief, its lens, evidence pointers and its own
report path. Ask them to inspect evidence rather than merely critique the
brief. Keep them from reading one another's drafts or coordinating conclusions
until all initial reports are saved. Record prior involvement or unavoidable
exposure; fresh context alone does not establish complete independence, and
multiple agents do not establish model diversity.

Run them concurrently when capacity permits. With fewer slots, run the same
independent assessments in stages while keeping earlier reports undisclosed.
If delegation is unavailable, report that limitation; a coordinator's three
viewpoints are not three independent assessments. Honor an explicitly requested
change in the number or selection of perspectives.

Each agent returns a report with:

- A recommendation and the strongest evidence for retaining the design.
- Concrete concerns, their consequences, and supporting source locations,
  examples or counterexamples. Separate established defects, plausible risks
  and unanswered questions; do not manufacture objections to fill a quota.
- The smallest useful correction or alternative, with what it would preserve
  and change. Include a discriminating test when the evidence cannot decide.
- Missing evidence, exposure, and validation limits. Cite primary sources and
  exact hypotheses for external technical claims. Distinguish inspected code,
  paper arguments and executed checks; a proposed proof is not a checked one.

For formal interfaces, investigate derivability before adding proof fields.
Distinguish laws defining new operations from stronger laws on unchanged
operations. Inspect concrete constructors and consumers before diagnosing a
missing guarantee. Keep instance limitations, representation costs and limits
of the underlying mathematics separate. For other domains, apply the same
discipline to invariants, capabilities and promised behavior.

Agents assess and may run agreed isolated experiments; they do not modify the
target design, create issues or contact other sessions. They should return
their assessment without launching another design-challenge workflow.

## Reconcile and preserve

Read all three completed reports before synthesizing. Preserve their initial
versions. Then investigate disagreements against evidence; request targeted
follow-ups if useful, recording any subsequent cross-exposure. Shared
assumptions can explain agreement, so three similar verdicts are not a reason
to skip checking their decisive premises. Preserve a well-supported minority
finding and leave unresolved disagreements explicit.

Save the brief, individual reports and synthesis in an accessible task location,
using project conventions for durable publication. The synthesis should state:

- What to retain, revise, replace or investigate, and why.
- Which concerns were resolved by existing structure, which require new
  obligations, and which remain open.
- Consequences for clients, interfaces and alternatives, including the limits
  of the recommendation.
- Concrete next steps with acceptance evidence, ordered by dependencies and
  value. Propose follow-up issues when useful; create them only within the
  user's authorized scope.

Return the recommendation with links to the full assessments and an honest
account of which perspectives completed. This is a design investigation, not
the independent Standards/Spec acceptance review required for implementation.
Follow the project's publication workflow for committed reports. Implementation
or adoption proceeds only when included in the user's task; a favorable
assessment does not itself expand that scope.

---
name: retro
description: "Conduct a retrospective on a coding session."
disable-model-invocation: true
---

For inter-skill use, follow [the host invocation policy](../writing-for-agents/SKILL-MECHANICS.md#using-a-skill-from-another-skill).

Suggest improvements to the coding agent's environment based on session and
repository evidence. This workflow produces recommendations; implement them
when the user has requested implementation. Propose global configuration
changes separately and never silently apply them.

## Procedure

1. Follow [writing-for-agents](../writing-for-agents/SKILL.md) when proposing
   changes to agent guidance.
2. Read primary sources for the specified session, defaulting to the current
   session. Use available session logs where relevant. State gaps in evidence;
   distinguish observed session failures from repository observations and
   hypothetical risks.
3. Discover applicable repository guidance through AGENTS.md and its pointers,
   including development, architecture, domain, and review guidance. Use the
   host policy for any CLAUDE.md fallback. Inspect existing docs and checks
   before proposing additions.
4. Assess the categories below where the evidence supports them. For each
   candidate, record the problem, supporting source or observation, proposed
   intervention, and how its effect could be assessed. Consider maintenance
   cost and false positives when choosing automation.
5. Present supported recommendations in severity order. Report limitations and
   allow no supported findings; category coverage is not a quota for changes.

When assessing whether agents discover and apply workflow guidance, prefer the
repository's audit method and baseline when available. In conaled, the known
location is [workflow audits](../../../docs/agents/workflow-audits.md); if absent,
look through repository guidance for a replacement. Without a local method,
propose a bounded trial: pin the guidance and realistic task prompts, collect
fresh-context plans without revealing the expected answer, and compare them
against applicable requirements. Separate original plans from diagnostic
follow-ups and execution evidence. Record missing traces or cost measurements;
planning alone does not establish implementation compliance. Missing optional
repository audit documentation does not block the retrospective.

## Improvement categories

- **Navigation:** When discovery took unnecessary effort, identify the missing
  or misleading pointer, hidden dependency, or stale reference. Prefer fixing
  the existing route to adding another document.
- **Formalization quality:** When proved claims diverged from intended
  mathematics, inspect assumptions, vacuity, definitions, and whether checked
  uses exercised the intended public results. Use the statement-review and
  checked-case guidance in [example-driven-development](../example-driven-development/SKILL.md)
  as the reference for recommendations. Compilation and axiom auditing alone
  do not establish that a statement captures human intent.
- **Automated checks:** Read the repository's build/check commands, their
  implementation, relevant regression suites, and enforcement configuration.
  Follow the repository's documented tooling and environment. In conaled, the
  known entry points are README build/audit guidance, `check.sh`, and its
  scripts; use their replacements if the layout changes. Distinguish a missing check, an existing
  check not run, a broken check, and missing automatic enforcement. Qualify
  conclusions when remote enforcement is unknown. Prefer extending suitable
  existing checks over recreating them. Missing conaled-specific files in another
  repository do not establish that its checks or tooling are deficient.
- **Standards:** When a mistake escaped implementation or review, determine
  whether a reliable mechanical check or a clarified judgement criterion would
  address it. Recommend checks for mechanically decidable rules where their
  cost and accuracy justify them. Place guidance in its existing authoritative
  source: agent docs, ADRs, skills, or a standards file if present.
- **Instruction load and no-ops:** When steering files are unwieldy, find
  duplication, stale guidance, or instructions shown not to change behaviour.
  Prefer short conditional pointers in AGENTS.md. Do not infer ineffectiveness
  merely because an instruction sounds obvious.
- **Tool economy:** When tool calls were costly, identify avoidable output,
  repeated discovery, or unnecessary work and propose a measurable reduction.
- **Information access:** When missing information impeded work, identify the
  specific source and an appropriate access mechanism, such as retained logs
  or read-only service access.

## Implementation and review

Implementers apply relevant architectural and mathematical standards while
choosing definitions, interfaces, proofs, and checked uses. Independent review
checks those decisions. Reviewers may need to explore unchanged definitions,
instances, assumptions, dependencies, and applications beyond the diff.

Keep shared procedures in their existing sources. Discover the repository's
review procedure through its guidance; conaled's known location is the
[review-and-fix procedure](../../../docs/agents/review-loop.md). If it is absent
or moved, use the local replacement when available and otherwise assess the
observed review process with the evidence limits stated. Do not invent a local
review policy or block recommendations on this optional reference. Use
example-driven-development for formal development. Reading these references
during a retrospective does not launch an implementation workflow or relax
applicable repository requirements.

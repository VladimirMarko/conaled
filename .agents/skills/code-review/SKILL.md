---
name: code-review
description: "Review a branch, PR, or work-in-progress changes against a fixed point along independent Standards and Spec axes. Runs both reviews in parallel sub-agents."
---

Review an immutable candidate against a fixed point supplied by the user or
calling workflow. Keep two independent axes:

- **Standards:** conformance to applicable repository standards.
- **Spec:** correctness and completeness against the intended requirements.

For inter-skill use, follow [the host invocation policy](../writing-for-agents/SKILL-MECHANICS.md#using-a-skill-from-another-skill).
Discover applicable repository guidance through AGENTS.md and its pointers.
Read tracker guidance when fetching issues; a supplied conversation or document
spec requires no tracker setup.

## 1. Pin scope and candidate

Establish whether scope includes committed, staged, unstaged, and relevant
untracked task changes. A supplied immutable candidate defines scope when the
caller has already captured it. For committed-only review, resolve the candidate
once, defaulting to HEAD. For work-in-progress review, use the snapshot rules in
[the shared review procedure](../../../docs/agents/review-loop.md), preserving
the real index and checkout and recording unrelated exclusions. Ask when task
ownership or scope is ambiguous; never silently omit requested uncommitted work.

Resolve the supplied fixed point to a base SHA; ask if neither user nor caller
supplies one. Record the candidate and merge-base SHAs. Normally capture
`git diff <base-sha>...<candidate-sha>` and
`git log <base-sha>..<candidate-sha> --oneline`. On divergent branches, three-dot
compares with the common ancestor, not the named base's tree. Confirm that scope;
if an exact endpoint comparison is requested, record and use a two-endpoint diff.
Synthetic candidates must descend from the captured starting-state base as
specified in the shared procedure.

Confirm refs resolve and the diff is non-empty before dispatch. Invalid refs
or an empty diff are not passing reviews. Give both reviewers the exact SHAs,
diff command, commit list, and exclusions. Read candidate files with `git show`
or an isolated checkout, including standards and relevant unchanged code.
Approval covers only that candidate. Keep snapshot objects reachable during
the review and carry the finding record across correction rounds.

## 2. Establish requirements

Use the user's or caller's explicit spec and full acceptance scope first.
Integration review covers the full spec even when commits refer to individual
tickets. Save the requirement contents/version used for review. Otherwise:

1. Inspect commit issue references and fetch them through repository tracker
   guidance, establishing which requirements apply to the full change.
2. Look for a matching spec under docs/, specs/, or .scratch/ in the candidate.
3. Ask for the spec if none is available. If the user confirms there is none,
   mark Spec skipped; an unavailable required spec makes that axis blocked.

## 3. Establish standards and evidence

Discover standards through applicable AGENTS.md pointers, agent docs, ADRs,
and skills in the candidate. Include CODING_STANDARDS.md and CONTRIBUTING.md
if present, then select applicable rules. Reviewers may need unchanged
definitions, instances, dependencies, and applications beyond the diff.

For Lean claims, both reviewers use the statement-review guidance in
[example-driven-development](../example-driven-development/SKILL.md).
Supply intended claims, retained cases and public results they exercise,
statement-review findings, and build/audit evidence. Standards checks required
methodology and architecture; Spec checks intended mathematics, assumptions,
definitions, vacuity, and coverage. Investigate or report missing handoff
evidence rather than treating it as compliance.

Collect applicable validation commands, results, scope, and candidate identity.
Rely on successful checks only where their coverage and inputs match the exact
reviewed candidate. Missing, failed, stale, or incomplete required validation
prevents passing until resolved. Reviewers may run checks in an isolated
snapshot using the documented environment. Avoid repeating successful
mechanical checks manually; assess semantics outside their coverage. Report
validation status separately from code findings.

Use [review heuristics](heuristics.md) as a baseline, subordinate to repository
standards. Each heuristic finding must identify a concrete consequence and a
remedy appropriate to the language and mathematical setting. Pattern matches
alone are not findings. Respect requirements for reusable abstractions.

## 4. Dispatch independent reviews

Spawn Standards and Spec subagents in parallel when both axes can run. Give
both the pinned scope from step 1, relevant candidate source paths, validation
evidence and limitations, and the existing finding record with stable IDs.
Give formal reviewers the step 3 instructions and implementation evidence.
Provide the full requirements to Spec and the applicable standards and heuristic
reference contents to Standards. Ensure both can access all supplied evidence.

**Standards brief:** Report documented-standard violations with candidate
locations and the applicable rule. Label heuristic findings as judgement calls
and explain their consequences. Apply repository overrides and validation
evidence requirements. Reassess every unresolved prior Standards finding.

**Spec brief:** Report missing or partial requirements, unjustified scope
changes, and incorrect implementations, citing each requirement and candidate
evidence. Apply mathematical review guidance when relevant and inspect related
unchanged definitions and uses. Reassess every unresolved prior Spec finding.

Each reviewer provides a concise summary and complete findings, with severity,
evidence, and stable identifiers. Do not discard findings to meet a word limit.
If an axis cannot run, record its reason and continue the other where useful.

## 5. Report and preserve outcomes

Present separate Standards and Spec reports, verbatim or lightly cleaned.
Keep their findings separate rather than reranking or merging across axes.
Include all findings directly or in a linked complete record accessible to the
caller. Retain IDs and dispositions across rounds using the shared procedure.

Give each axis an explicit outcome:

- **Passed:** review complete, applicable validation established, no unresolved
  findings.
- **Findings-present:** review identified unresolved findings.
- **Skipped:** the axis was explicitly omitted, such as a confirmed absent spec.
- **Blocked:** required evidence or access is unavailable.

Keep findings visible when an axis is also blocked. Report validation status,
limitations, and reasons for skipped or blocked axes separately. Neither skipped
nor blocked counts as passed. Implementation loops require both axes to pass
on the same candidate; follow the shared procedure for corrections and final
candidate verification.

End with the base and candidate SHAs, findings count and worst issue within
each axis, and each axis's outcome. Passing one axis cannot mask failure or
incomplete review of the other.

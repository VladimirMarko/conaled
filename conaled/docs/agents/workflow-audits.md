# Auditing agent workflow guidance

Use this method when a retrospective or observed session raises a question
about guidance discovery, application, or review cost. It is an evaluation
procedure, not another implementation or review gate. `retro` can assess the
evidence and recommend a bounded trial; invoking it does not automatically
launch agents or change repository guidance. Keep future audit scope and
acceptance criteria in GitHub Issues.
The next behavioral and cost assessment is tracked in
[#192](https://github.com/VladimirMarko/conaled/issues/192).

## Repeatable trials

1. Pin the repository revision and record the relevant guidance, task prompts,
   agent configuration when available, and allowed side effects. A modified
   checkout needs an immutable snapshot. Keep trial artifacts outside the
   source diff. Record which instructions the host supplies automatically.
2. Give agents fresh conversation contexts and realistic tasks. Do not include
   the suspected weakness or desired guidance in their prompts. For discovery
   trials, request plans only and prohibit edits, builds, and tracker writes.
   Ask for concrete validation/completion criteria and the files actually
   consulted, distinguishing complete reads, excerpts, searches, and truncation.
3. Preserve each original plan before asking diagnostic follow-ups. Assess
   which applicable instructions were found, how they affected decisions, and
   which completion requirements were omitted. Reading a file is weaker
   evidence than applying its requirements. Missing an optional workflow is
   not a violation of a mandatory rule.
4. Compare against the pinned guidance. Use tool/session traces when available;
   identify self-reported consultation records as such. Separate observed
   behavior, repository routing defects, and hypothetical risks. Do not infer
   host discovery behavior solely from a skill file's existence.
5. After a targeted change, repeat comparable tasks with fresh agents. Include
   a case already inside an implementation loop and an originator review of
   an unchanged, already-reviewed candidate. Check for both missing review and
   unnecessary duplicate review. Add bounded execution trials when plans alone
   cannot answer the question, with explicit side-effect limits.

For cost assessment, record agent launches, review rounds, repeated reads and
checks, elapsed time, and token usage where exposed. Separate useful correction
rounds from duplicate work on unchanged candidates. Report missing measurements;
neither fewer words nor fewer agents proves lower total cost or equal quality.
Preserve independent Standards/Spec assessment and exact-candidate validation.
Avoid mandatory audit schedules, extra review layers, and permanent checks
without evidence that they help.

## Initial planning trial, 2026-10-27

Baseline: `b78c3ee3dc74a0e3cca1e2b1416d25c7ada36ade`. The current conversation
contains the trial prompts and returned plans; this section summarizes them,
not a separately archived tool trace. Three subagents received fresh
conversation contexts, the repository environment/instructions, and these tasks:

| Task | Observed original plan |
|---|---|
| Transport a resource accounting law along changed weights, with two algorithm clients | Reuse existing transport, minimal hypotheses, connected examples, statement review, fresh build and audit. |
| Add last-valid and out-of-range random-access lookup examples | Recognize existing coverage, reuse public refinement theorems, add a carry-boundary case, statement review, fresh build and audit. |
| Improve data-structure navigation and assess a directory or Lake package | Inspect dependencies, follow ADR 0001, prefer navigation changes, keep organization provisional, validate documentation links. |

All three reported consulting architectural guidance and applied it in their
plans. Neither Lean plan omitted statement review or fresh validation. None
planned independent implementation review. Separate diagnostic follow-ups
confirmed that omission; the agents did not read new guidance during those
follow-ups. The root agent's earlier README rewrite also lacked independent
review, but that session was not a controlled trial.

At baseline, AGENTS.md did not route implementation tasks to an independent
review workflow. `implement` and `implement-spec` both disabled implicit
invocation. These omissions therefore exposed a policy/discovery gap, not
established violations of a repository-wide independent-review requirement.

Limits: consultation histories were self-reported; some combined tool reads
were truncated and followed by narrower reads. Asking agents to list consulted
instructions may improve their discovery behavior. No implementation was
performed, token usage was not measured, and three plans cannot establish a
general compliance rate. The trial supports improving workflow routing while
retaining the architecture pointers that worked in these cases.

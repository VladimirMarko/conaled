# Direct-toolchain review coordination — round 2

## Result

**Both independent review axes passed** for the complete operational-helper
candidate `822cb7adeed4943acaf10454e9facfc2e3ee8ceb` against fixed base
`76d77a107deb37c30e0b061c30b03a3f8c6aa12c`. All four retained axis-specific
finding IDs are fixed with review evidence. There are no new or unresolved
findings and no skipped or blocked axis.

| Axis | Complete report | Outcome | Unresolved | Worst unresolved |
|---|---|---|---:|---|
| Standards | [direct-toolchain-standards-r2.md](direct-toolchain-standards-r2.md) | Passed | 0 | None |
| Spec | [direct-toolchain-spec-r2.md](direct-toolchain-spec-r2.md) | Passed | 0 | None |

The retained record is [direct-toolchain.md](direct-toolchain.md). It contains
both rounds, fixed scope/requirement identities, complete evidence hashes,
the initial findings and their final dispositions. Round 1 reports remain
unchanged. The coordinator reconciled the two reports and checked identity;
it did not perform a third source review or modify implementation files.

## Candidate and delivery identity

- Base and merge base: `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
- Candidate: `822cb7adeed4943acaf10454e9facfc2e3ee8ceb`.
- Retained candidate ref: `refs/pfds-review/direct-toolchain-r2-041`.
- Isolated checkout: `pfds/review-direct-toolchain-041-r2`.
- Full review diff: `git diff 76d77a107deb37c30e0b061c30b03a3f8c6aa12c...822cb7adeed4943acaf10454e9facfc2e3ee8ceb`.
- Commit: `822cb7a chore(toolchain): support fresh validation and cold recovery`.
- Scope: eight authored operational files, 968 inserted lines relative to
  the fixed base. All prior exclusions and independent obligations persist.
- Scope manifest SHA256:
  `5f556fb8f0121c55ad6c69589c247bde8bbd7ee6a467ce5e18387d9ec9b99de6`.

At `2026-11-03T15:13:17.631871+00:00`, the coordinator independently confirmed
the exact candidate HEAD and empty Git status in the isolated checkout, then
recomputed all eight file hashes in both the snapshot and delivered `session`
locations. Every hash matched the scope manifest. Requirements and repository
standards remain those pinned for round 1. Later source changes require new
applicable review; approval does not extend to a moving tip.

## Standards closure

**DTS-001 (original Medium): fixed.** The runner exposes the fresh full route,
records its actual verification mode, checks the retained command and stock
record against that mode, and uses ordinary stock final verification without
fresh/jobs flags. Recovery instructions require the first full invocation
under this runtime to use fresh mode with the serial policy.

**DTS-002 (original Medium): fixed.** Both smoke tests establish their own
workspace-local temporary parent. The actual corrected CLI and Lake runs
started with that parent absent and reached their genuine compiler/build
probes successfully.

Complete Standards report SHA256:
`6a81a379f6af97b5d380ab78e08e6d3a0561e1c2689d084e0455249289e13485`.

## Spec closure

**DTP-001 (original High): fixed.** The full workflow now supports the required
fresh check and retains mode-correct evidence through final verification.
The preserved red case and corrected public refusal case establish the CLI
change; source review establishes exact command construction and record
binding. No passing formal result was fabricated or inferred.

**DTP-002 (original Medium): fixed.** Temporary fixture setup is now
self-contained after checkpoint recovery. The retained real red failure and
both actual absent-parent green runs directly address the failure condition.

Complete Spec report SHA256:
`cbc435d532e0c8e56fd98c018e62522c71fcd45bbc4b0bcca9b57008bb592b35`.

The different original severities remain intact. No finding was dropped,
renumbered, merged across axes, or closed solely by the implementer's claim.

## Validation reconciliation

Three actual round 2 artifact commands exited zero: public exact-version and
theorem acceptance/rejection probes; Lake native compilation/link/execution;
and public runner refusal tests including the fresh argument path. The CLI
and Lake suites used a newly constructed cold-workspace profile, with the
temporary parent absent before each run. Exact original executable identities
and unchanged dependency pins remain documented in retained evidence.

The original aggregate remains `passed: false`: its final snapshot check
found the isolated review checkout's private index absent after a setup error
involving the temporary snapshot index environment. The coordinator observed
that state. The implementer repaired only the review index from its exact
HEAD, leaving tested source bytes unchanged. The separate reconciliation
preserves the original aggregate's SHA and explicitly reuses the actual
successful commands. The coordinator and both reviewers subsequently
confirmed the clean immutable candidate.

Both axes found that reuse appropriate for these artifact inputs. The CLI and
Lake tests ran generated projects in the separate cold workspace; the refusal
tests exit before a real checkout snapshot. Those semantic inputs do not use
the repaired review index. This reasoning is not a waiver of clean-state
requirements for a future formal candidate check. No formal stock check ran
under the absent-index state, and the historical failed aggregate was not
overwritten or relabelled.

- Original aggregate SHA256:
  `d65acb992ea7ef25660873c88be52efad91477150e456150b0467fb5da329fc4`.
- Reconciliation SHA256:
  `998a2fb578d337f92174c0d4343fa8bd593f32c91f7cf753d8a033e3981c9916`.

No runtime test, compiler, cache operation or build was repeated by the
coordinator or reviewers. The complete reports and retained record provide
all test-command identities and evidence hashes.

## Scope of the passing result

The operational helpers and their artifact-appropriate validation are ready
for the parent's continuation of development. This review does not accept a
formal candidate, proof, chapter, or whole-book/thesis milestone. A real fresh
full project check, exhaustive proof audit, relevant focused validation,
independent formal reviews and immediate stock candidate verification retain
their own requirements and evidence. The first full check in this restored
runtime must use the fresh route with the established one-job policy.

**Final record:** base `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`;
candidate `822cb7adeed4943acaf10454e9facfc2e3ee8ceb`; Standards **Passed**,
0 unresolved/none worst; Spec **Passed**, 0 unresolved/none worst.

# Operational toolchain review — coordinator reconciliation, r7-042

## Outcome

**The complete operational-toolchain review passes on immutable candidate
`af2c53dce68ebb122c81175312d6bb30df9aac05`.** Both independent axes completed
their full-scope reviews with no new or unresolved findings. Final delivered
source identity was checked at `2026-11-03T17:14:04.672619+00:00`: all 18
committed, isolated-checkout, and delivered files match the captured manifest;
the isolated checkout is clean and all saved requirements are unchanged.

This reconciliation closes the operational implementation review for the exact
candidate and saved requirements. It does not establish a formal full build,
proof audit, final stock candidate verification, chapter completion, or
completion of the PFDS book/thesis union. The separate formal jobs retain their
own actual outcomes; their completion was not a prerequisite for deciding this
distinct tooling scope.

Coordinator: `/root/direct_toolchain_validation_plan`. I read both complete
independent reports, checked the identities and evidence boundaries, and retained
the separate findings. I did not perform a third Standards or Spec review.
My earlier authorship of the original validation runner was disclosed before
dispatch. Neither independent reviewer authored implementation in this scope.

## Exact candidate and scope

| Identity | Value |
| --- | --- |
| Fixed base and merge base | `76d77a107deb37c30e0b061c30b03a3f8c6aa12c` |
| Candidate | `af2c53dce68ebb122c81175312d6bb30df9aac05` |
| Retained ref | `refs/pfds-review/native-toolchain-r7-042` |
| Isolated checkout | `/workspace/scratch/b566cace4ed6/pfds/review-native-toolchain-042-r7` |
| Commit | `af2c53d feat(toolchain): bind corrected focused native candidates explicitly` |
| Complete source diff | 18 added files; 3,308 inserted lines |
| Manifest | `session/validation/native-toolchain-candidate-r7-042.json` |
| Manifest SHA256 | `257e31713ec28c4c12cafb7635ad14098f09d8bc765c79d541b7ff30d27ac593` |

The reviewed diff is:

```text
git diff 76d77a107deb37c30e0b061c30b03a3f8c6aa12c...af2c53dce68ebb122c81175312d6bb30df9aac05
```

It covers the original eight QEMU operational helpers and their handoff notes;
the full environment recovery and route-comparison documents; the checkpoint
generator/template; the native own-executable metadata adapter and profile
launcher; three native contract-test files; and the native validation runner
and its public refusal tests. Both reviewers read the complete captured scope.

Formal candidate sources, runtime binaries and caches, prior evidence,
trackers, requirements, review records, and provenance remain outside this
authored diff. Their obligations are neither removed nor completed by this
review. The full checkpoint generator is included because it was absent from
the fixed repository base; its retained predecessor and exact task delta
establish that the changes are its generated README and restore-success pointer.

## Separate independent outcomes

| Axis | Independent reviewer | Outcome | New findings | Unresolved findings | Worst unresolved |
| --- | --- | --- | ---: | ---: | --- |
| Standards | `/root/recovery_audit` | Passed | 0 | 0 | None |
| Spec | `/root/chapter02_continuation_plan` | Passed | 0 | 0 | None |

Both reports are complete and frozen:

| Report | SHA256 |
| --- | --- |
| `session/reviews/direct-toolchain-standards-r7-042.md` | `3b143b5b92f51efaa8aecfc86de2fa7a3316ce1cc320a490c81ffc2af064ca0e` |
| `session/reviews/direct-toolchain-spec-r7-042.md` | `c7df56778cba429b9d2c8c67e5a5f1e52f35e6a106a9ac36a2ecb0f89ac81b04` |

The Standards reviewer confirmed the repository-required fresh route and
mode-bound verification remain present, cold recovery creates its required
temporary parents, native behavior is constrained by the documented contract,
public tests and provenance support their stated claims, and the recovery and
checkpoint entrypoints retain the required boundaries. It reported no new
documented-standard violation or actionable heuristic defect.

The Spec reviewer confirmed the full native/fallback, recovery, comparison,
evidence-recording and checkpoint requirements are covered. Its assessment
explicitly preserves the fixed full/verify candidate, the exact focused
candidate override and its recorded identity, genuine compiler results,
separate native/QEMU histories, and the limits on performance and formal claims.
It reported no missing or incorrectly implemented requirement in the operational
scope. Its temporary read-only transport outage resolved on a bounded retry;
no missing review coverage or access blocker remains.

These are summaries of the independent reports, not additional coordinator
judgments. Their complete evidence and reasoning remain in the linked local
report files. Neither axis's result substitutes for the other.

### Retained Standards findings

| ID | Original severity | Disposition |
| --- | --- | --- |
| DTS-001 | Medium | Required fresh-validation route and mode-bound retained verification: fixed with round-2 evidence; no r7 regression. |
| DTS-002 | Medium | Missing temporary parent after cold recovery: fixed with round-2 evidence; no r7 regression. |

### Retained Spec findings

| ID | Original severity | Disposition |
| --- | --- | --- |
| DTP-001 | High | Required first fresh full check and its retained mode binding: fixed with round-2 evidence; no r7 regression. |
| DTP-002 | Medium | Cold-recovery smoke-test setup: fixed with round-2 evidence; no r7 regression. |

No new identifier was allocated. Earlier reports and the original severities
remain retained; the findings are not merged across axes or silently removed.
Rounds 3 and 4 remain incomplete historical reviews. Rounds 5 and 6 were
superseded before approval. Their actual test results can support explicitly
matched evidence reuse, but do not become inferred review approvals.

## Requirements and applicable evidence

The complete requirements are preserved in `session/requirements/REQUEST.md`,
`REQUEST-union-v2.md`, `REQUEST-direct-toolchain-041.md`,
`REQUEST-environment-handoff-042.md`, and `REQUEST-native-toolchain-042.md`,
together with `session/environment/direct-toolchain-implementation-scope-041.md`.
Their hashes are in the manifest and retained main review record. Both reviewers
used these versions; the coordinator rechecked them before dispatch and at
final delivery verification.

The user makes Nix optional and requests a faster native alternative, while
retaining exact pins, genuine compiler behavior, source/proof policy, isolated
validation, independent reviews, chapter order, local tracking and durability.
The supplied other-agent guide is comparison evidence only, with its original
workstream and inaccessible external references kept distinct from this task.

The r7 artifact aggregate is
`session/validation/native-toolchain-candidate-validation-r7-042.json`, SHA256
`e142a541377e59027008d2299fc19dcb9b5a1613cc460409ffbf90c9ae3b8176`.
It records four genuine native-controller public refusal tests, documentation
syntax checks, and two existing-state recovery-verification recipes. The
manifest's earlier `Pending` field predates this completed aggregate.

Both axes accepted the explicitly scoped reuse of actual r6 cold-profile,
compiler/Lake and native contract results. Fourteen relevant r6 source files
match r7, including the native adapter, profile launcher and fixture sources;
all eight original helpers match approved round 2. The changed r7 native
controller/test and recovery/comparison documents have separately recorded
applicable checks. The coordinator verified these source matches and the six
linked evidence digests before dispatch.

The retained r6 results include a profile constructed from captured source,
actual exact versions, a genuine minimal theorem/no-axiom result, rejection of
a false proof, Lake compilation/linking/execution yielding `42`, and 18 native
metadata contract cases. The minimal cold proof fixture is distinguished from
the earlier broader `import Lean` smokes and from formal project acceptance.
Controlled downstream denials are test-fixture results, not protected-host
access observations. Documentation recipe checks do not claim an unperformed
complete cold acquisition or network restoration.

The failed r2 aggregate remains failed and preserved. Its index-only repair
and narrowly justified reuse are recorded separately. Neither this record nor
either r7 reviewer retroactively relabels that aggregate or claims a formal
check ran under its incorrect index state.

## Final identity verification and handoff

At `2026-11-03T17:14:04.672619+00:00`, the coordinator rechecked:

- Exact candidate HEAD and retained ref, with the unchanged fixed merge base.
- Empty isolated Git status.
- Every one of the 18 committed, isolated and delivered source hashes against
  the r7 manifest.
- All saved requirement hashes.
- Unchanged manifest and artifact-aggregate hashes.
- Exact hashes of both complete frozen independent reports.

All checks matched; no failure was observed. These were read-only identity
checks, not repeated compiler/build/test operations or a formal stock
`--verify-candidate` invocation. The coordinator changed only this report and
the retained review record; the independent reviewers wrote only their reports.
No implementation, runtime, controller, source proof or tracker was modified.

This completes r7 operational review and is ready for checkpoint capture.
The parent can preserve any still-running formal focus as explicit partial
evidence and proceed with the separately required fresh native 901 gate.
Formal success, exhaustive audit, applicable formal source reviews, and
immediate stock candidate verification must still come from their own actual
records. No current or future formal result is inferred here.

Any later change to these 18 delivered sources requires the existing loop's
applicable new candidate review; this outcome approves no moving tip.

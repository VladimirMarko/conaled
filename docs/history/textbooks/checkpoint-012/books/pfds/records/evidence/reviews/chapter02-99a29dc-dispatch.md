# Chapter 2 corrected candidate — round 3 dispatch

This continues the existing local #10002 loop and the retained independent
reviewer pair. Coordinator `/root/chapter02_review` supplies scope and evidence
reconciliation, not a third Standards or Spec assessment.

## Exact full scope

- Fixed original chapter/integration base: `82501d108f33c62d21b5e0d0f7d2376b902d8d49`.
- Candidate: `99a29dcd02eb529fbefbb675e244a8c47b78cdef`.
- Checkout: `/workspace/scratch/ca9a61d0bf30/validation-chapter02-r3`.
- Branch: `pfds/ch02-review-r3`.
- Confirmed candidate HEAD, clean index/worktree and exact fixed merge-base.
- Full diff: `git diff 82501d108f33c62d21b5e0d0f7d2376b902d8d49...99a29dcd02eb529fbefbb675e244a8c47b78cdef`.
- Scope: 42 changed files, 39 Lean files, 4,468 insertions and 4 deletions,
  33 commits, no exclusions.
- Manifest `../validation/chapter02-candidate-r3.json`: all42 hashes match;
  changed-file set matches exactly, with no omissions or unrelated extras.

## Retained requirements and standards

| Saved specification | SHA256 |
| --- | --- |
| `../requirements/REQUEST.md` | `b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499` |
| `../requirements/REQUEST-union-v2.md` | `3336bed1154438b3683aeb5a1c63fee44e87aff190f5ff69e34705a780b9d22c` |
| `../requirements/chapter02.md` | `240b6bfec9f9e8599f1034abc309499928c8472edf76481b553ef99ce40ff944` |
| `../requirements/import-footprint.md` | `cf8fb3133b83ac59fdf6fd46b818d8b279d96385f5de50da843ef9b7fd62444d` |

The original request and union clarification remain controlling. Chapter2
requirements are unchanged at version1. The import prerequisite expressly
permits direct dependency additions for recorded transitive-import failures,
while preserving every declaration/proof and all acceptance machinery.
All candidate guidance, architecture/domain rules, glossary, ADRs0001/0010,
example-driven-development/statement review, code-review and review-loop rules
remain applicable and unchanged. No GitHub writes are authorized.

Retain both historical round1 reports and CH02-PRE-001 through005. Both prior
axes completed full static assessments but remained Blocked; their outcomes
do not approve this different candidate. Review the full fixed-base scope,
reuse matching unchanged analysis, and inspect current changed imports and
all affected dependencies. Candidate snapshots are read-only.

## Corrections since round1

The exact candidate-to-candidate diff from69f6f00 consists of four import lines:

| Consumer | Direct provider added |
| --- | --- |
| Applications/FRP/Demand.lean | Mathlib.Order.SuccPred.Nat |
| Applications/FRP/Finite.lean | Mathlib.Data.Set.Finite.Lattice |
| Examples/FRP.lean | Mathlib.Algebra.Order.Archimedean.Real.Basic |
| Examples/IndefiniteService.lean | Mathlib.Data.Nat.Size |

These are the only changes since the previously reviewed chapter candidate;
all Chapter2 formal/proof/documentation bytes remain unchanged. The two
correction commits are:

```text
99a29dc fix(frp): import the natural size power theorem directly (#10018)
c372c47 fix(frp): import direct providers in affected consumers (#10018)
```

IMPORT-VAL-001 through004 remain recorded in import-footprint.md and the
preserved observed compiler diagnostics. The separate prerequisite candidate
901f734 has its own independent static reviews. Those reviews do not approve
this complete chapter candidate.

## Validation limitations

No exact full99a29dc build, exhaustive audit, success record or final candidate
verification has completed. Its .lake/verification.json is absent.
Both axes must remain Blocked unless root later supplies matching gate evidence.

The original324962e full runtime disappeared without a terminal result; root
preserved its known IMPORT-VAL-004 failure, log and observations in
../validation/runtime-interruption-20261102-2240.json. The source of the runtime
loss is unknown. The automatic running record is not a terminal success.
Root also reports loss of the separately owned901 focused run without terminal
success and no surviving exact-cwd compilers. That focused run had not reached
the IMPORT-VAL-004 target. Do not call004 compiler-verified or infer a completed
focused closure. The focused owner has now returned FINAL and released ownership. The corrected
901 stock full check started at2026-11-02T22:44:09Z and is running, per
../validation/import-footprint-901f734-full-r1.json. Its ordinary-output
recovery record reports657complete project modules and1971hashed artifacts,
with no source inconsistencies. This is guarded cache recovery, not acceptance.
The focused interruption is preserved in
../validation/import-footprint-r3-focused-interruption-r1.json. A future901
success would still not approve99a29dc.

No reviewer may launch compilation, signal any process, or change candidate
source/refs/index/dependencies/build state. This static continuation is useful
without creating or claiming missing validation.

## Retained independent axes

- Standards: `/root/chapter02_review/standards`, followup delivered; new report
  `chapter02-standards-r3.md`.
- Spec: `/root/chapter02_review/spec`, same retained reviewer; new report
  `chapter02-spec-r3.md`. Retained-agent followup was delivered immediately
  after map returned FINAL and released its slot; no owner was interrupted.

The full prior dispatch and source/statement evidence remain in
chapter02-69f6f00-dispatch.md and chapter02.md. Reports must cover the full
chapter and preserve every prior finding. Any concrete new finding is sent to
root promptly; both outcomes remain separate.

## Complete current commit list

```text
99a29dc fix(frp): import the natural size power theorem directly (#10018)
c372c47 fix(frp): import direct providers in affected consumers (#10018)
69f6f00 refactor(frp): import only the required mathematics and tactics (#10018)
76d77a1 feat(pfds): complete chapter two integration and source mapping (#10002)
c74eab7 fix(trees): normalize retained descendant paths (#10002)
aadb51b fix(trees): normalize concrete duplicate search paths (#10002)
5437931 feat(trees): draft duplicate endpoint retention proofs (#10002)
8d17f73 docs(pfds): record physical optimization and map contracts (#10002)
439dc67 feat(pfds): expose checked shared finite maps (#10002)
52f930a fix(maps): establish the stored-map ordering instance (#10002)
f39d1a9 feat(maps): compose shared binding and lookup observations (#10002)
047c21e feat(maps): draft shared traversal and endpoint contracts (#10002)
7baa042 feat(pfds): integrate checked abort and combined insertion (#10002)
ef01b63 feat(trees): verify shared insertion optimizations and clients (#10002)
c6dcabd feat(trees): develop aborting shared insertion proofs (#10002)
6f045e0 docs(pfds): map persistence claims to checked developments (#10002)
ebdeec2 refactor(trees): share optional root-value observations (#10002)
5705776 feat(pfds): expose integrated chapter two developments (#10002)
8eaa9c2 feat(persistence): connect source indices and ordered path copying (#10002)
94e8c14 fix(maps): simplify checked ordered-map proofs (#10002)
31135e3 refactor(maps): expose ordered observation update law (#10002)
947219d feat(maps): draft ordered finite-map realization and cases (#10002)
8f1ae65 feat(maps): specify finite-map operations and observations (#10002)
6837888 feat(search): prove finite contents and sharp comparison bounds (#10002)
17de2f7 feat(trees): share key-directed physical search paths (#10002)
3cd2686 feat(trees): prove actual off-path root retention (#10002)
f2b187e feat(trees): prove shared complete and balanced construction (#10002)
725afcb feat(search): connect ordered trees to abstract set clients (#10002)
53e6bcd feat(search): add candidate and abort traversals (#10002)
d0d9a1b feat(search): define ordered tree value contracts (#10002)
44cecba feat(trees): develop shared tree construction proofs (#10002)
4d5e86d feat(sequences): integrate stack and integer update cases (#10002)
8e894aa feat(sequences): add abstract stacks and integer update refinement (#10002)
```


## Static round completion

Both retained independent axes completed full-scope reassessment on the same
fixed base/candidate. Standards:0code/prosefindings, Blocked. Spec:0implementation/
source-coveragefindings, Blocked. Reports chapter02-standards-r3.md and
chapter02-spec-r3.md retain PRE001..004 static closures, openPRE005, matched
focused001..003 evidence, and pending terminal IMPORT-VAL004 evidence. The
coordinator chapter02.md records their report hashes and continuation. Neither
interrupted runs, guarded ordinary-output recovery nor the running prerequisite
901 gate approves99a29dc. Both reviewers returned their static assessment to
release slots; preserve/reuse the same pair for exact-gate continuation.

# Existing operational loop — round 11 review dispatch

Coordinator: `/root/operational_review`. This continues `direct-toolchain.md`;
it does not open a second implementation loop or review a formal candidate.
Root is the implementer. The two independent axis reviewers authored none of
the delivered operational source.

## Immutable scope

- Fixed base and merge base: `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
- Candidate: `4f15ff6f5bc8091104a3572ca8ce3716ed8e78f0`.
- Retained ref: `refs/pfds-review/native-toolchain-r11-045`.
- Prior approved operational candidate: `060e6b877b8db57a30f947b996b7dfe34a5401a1`.
- Isolated checkout: `/workspace/scratch/09cf0de22282/pfds/review-native-toolchain-045-r11`; exact HEAD and clean status checked.
- Full diff: `git diff 76d77a107deb37c30e0b061c30b03a3f8c6aa12c...4f15ff6f5bc8091104a3572ca8ce3716ed8e78f0`.
- Complete scope: 20 files, 3,805 additions; no project Lean/checker source changes.
- Commit range: `git log 76d77a107deb37c30e0b061c30b03a3f8c6aa12c..4f15ff6f5bc8091104a3572ca8ce3716ed8e78f0 --oneline` contains
  `060e6b8` and `4f15ff6`.

The original 19-file source scope remains covered; 16 files have byte-identical
contents and modes relative to the approved r10 scope. The changed files are
`session/checkpoint.py`, `session/validation/run-native-validation.py`,
`session/validation/test-native-validation.py`, plus the new
`session/environment/RECOVER-INTEGRATION.md`. Both axes may retain matching r10
analysis while reviewing all changed behavior, affected context and prior
findings. They may not restrict the task to just a terse final patch.

All 20 committed, isolated and delivered content hashes and modes match the
captured manifest. All eight requirement identities match. The coordinator's
read-only receipt is `validation/native-toolchain-coordinator-dispatch-r11-045.json`,
SHA-256 `e52f6055b16c14de563a9ed9a808bda10bf8127a47be86c6ad16822d712df966`.
This is dispatch/identity evidence, not an independent source review outcome.

## Requirements retained

| Saved requirement | SHA-256 |
| --- | --- |
| `session/requirements/REQUEST.md` | `b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499` |
| `session/requirements/REQUEST-union-v2.md` | `3336bed1154438b3683aeb5a1c63fee44e87aff190f5ff69e34705a780b9d22c` |
| `session/requirements/REQUEST-direct-toolchain-041.md` | `16845edec15c311e0cfd5ed5d4f5c4feb61e7ad96545653d5b872309d26464bc` |
| `session/environment/direct-toolchain-implementation-scope-041.md` | `05c125ee129eafc8f45f9367be16259c3239c7b3945c32f62effba1f1b4c922c` |
| `session/requirements/REQUEST-environment-handoff-042.md` | `200789123c60ae137967f881207194412eecea72ba2fc80247978075bd6a4602` |
| `session/requirements/REQUEST-native-toolchain-042.md` | `d76dc8dcf771a227779628de91e75c4b63a2898b95e7b30035de83537dae5195` |
| `session/requirements/REQUEST-common-candidate-validation-044.md` | `1a6b2a4b0d68b7a559e5d3d9c3fa7a90f0f1113f8d37539dedfb1df1579ca870` |
| `session/requirements/REQUEST-recovery-045.md` | `dafc4b266e88c7644d35439ab8aba9a1d0e95a4ccab69e18b9cfb7150e4da44e` |

The newest user request selects the supplied unified native kit and compact
current-work recovery checkpoints. That selection changes the operational
profile and permits omission of reproducible unrelated upstream history; it
does not waive formal proof policy, exact candidate validation, independent
review, local tracking, no GitHub writes or honest recovery limits. The current
native-kit archive is an unchanged user-provided external input, retained in
the checkpoint and bound by its actual hash. It is not an authored project
source modification. Live runtime binaries/caches, preserved review/tracker
records and unchanged formal candidates remain outside the authored source diff.

## Evidence available before independent outcomes

- `validation/native-toolchain-candidate-validation-r11-045.json` records
  stable repeated native identity, correct selected/cleansed environment fields,
  all four recovery shell blocks passing syntax validation, and all 20
  delivered/isolated source hashes matching.
- `validation/native-controller-r11-isolated-045.log` records all eight
  disposable public controller/refusal tests passing in the captured checkout.
  Genuine requirement-driven red cases and subsequent green logs remain
  preserved; no fixture supplies a real successful project gate.
- `environment/unified-native-setup-045.json` and its complete retained evidence
  record actual setup, exact dependencies, cache hydration and ten expected
  smoke outcomes. This is environment validation only.
- `checkpoints/conaled-pfds-checkpoint-045.tar.gz` was actually created with the
  candidate generator: 9,486,734 bytes, SHA-256
  `8eb968d0ac3e5776b5d2a80075042c5cc552565cf3e8218eb5dc93f3938b771d`. `checkpoint-045-create.log` ends in
  `restore_test: passed`. Recovery initialized a new repository, fetched only
  the exact upstream baseline at depth one, verified/unbundled task objects,
  then checked source/index/worktree/untracked/session and selected-ref state.
  The archive manifest contains the matching 20 source files and exact kit.
  `session/checkpoint045-upload.json` records successful upload.

The source baseline requirement is explicit: recovery needs the exact public
commit or a local repository containing it. The compact checkpoint does not
claim to be an offline copy of all third-party inputs. The actual test fetched
only that exact baseline into its independent empty recovery repository; no
already-present task objects were relied upon.

Historical successful r10 artifact evidence may be reused only for matching
unchanged inputs and its original coverage. No old source/runtime acceptance
is transferred to the formal integration candidate. The genuine fresh full
gate, exhaustive audit, required regressions, separate formal reviews and
immediate final verification remain subsequent obligations.

## Independent assignments and retained findings

- Standards: `/root/operational_review/standards`; final report reserved at
  `reviews/direct-toolchain-standards-r11-045.md`.
- Spec: `/root/operational_review/spec`; final report reserved at
  `reviews/direct-toolchain-spec-r11-045.md`.

Both retain all DTS-001/002/003 and DTP-001/002/003 dispositions and evidence,
assessing for regression under this continuation. New findings receive new
stable IDs with the axis's original severity and exact source/requirement
citations. Each axis must give an explicit outcome; neither Blocked nor Skipped
counts as Passed. No compilers, network, full project checks or source edits
were delegated to either reviewer. Root owns corrections and final delivered
identity verification; the coordinator reconciles the two independent reports.

At dispatch both outcomes are pending. Artifact/recovery success alone does
not authorize use of the new integration full/verify route.

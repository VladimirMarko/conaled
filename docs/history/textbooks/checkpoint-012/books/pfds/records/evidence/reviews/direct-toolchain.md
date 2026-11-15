# Direct-toolchain operational implementation review

This is the retained review and finding record for the parent's existing
direct-toolchain implementation loop. The parent implements. Original
coordination was by `/root/lean_native_path_options`; from round 7,
`/root/direct_toolchain_validation_plan` coordinates the independent Standards
and Spec axes and reconciles their evidence. The coordinator does not perform
a third review or change implementation files.

## Acceptance scope

Rounds 1 and 2 review the eight authored operational helpers and documentation
files captured in their manifests. Round 3 expands the same loop to ten files
by adding the user-requested environment takeover runbook and comparison.
Round 7 completes review of the 18-file native-toolchain and recovery scope
captured by its manifest, retaining the earlier outcomes and evidence.
No formal source, proof, signed-potential candidate, chapter, or whole-book
acceptance is covered. User authorization removes the Nix launch requirement
only. Exact compiler/dependency pins, genuine stock checks, isolation, review,
local tracking and recovery obligations continue.

Excluded from this source diff: formal candidate sources; historical evidence;
runtime distributions, binaries and caches; trackers/status; requirements,
review and provenance records. Their independent obligations remain in force.
All records here remain local; no remote publication was performed.

## Immutable scope

- Base: `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
- Round 1 candidate: `f010b5d0fdbef9c9f007c56531c326e738557f9d`.
- Merge base: `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
- Retained refs: `refs/pfds-review/direct-toolchain-base-041` and
  `refs/pfds-review/direct-toolchain-r1-041`.
- Isolated checkout: `pfds/review-direct-toolchain-041`; HEAD and both retained
  refs were resolved and confirmed, and the checkout was clean.
- Diff: `git diff 76d77a107deb37c30e0b061c30b03a3f8c6aa12c...f010b5d0fdbef9c9f007c56531c326e738557f9d`.
- Commit list: one commit, `f010b5d chore(toolchain): restore exact Lean and Lake without Nix`.
- Diff size: eight files, 935 inserted lines. The diff is nonempty and the
  candidate descends from the supplied base.
- Scope manifest: `session/validation/direct-toolchain-candidate-r1-041.json`,
  SHA256 `f9c88a325952223fde7c4e468cdc9eae9fa1eb2066a0a7d4aeda7d7f2067344b`.

The manifest lists the profile generator, scoped command launcher, two public
CLI/build smoke tests, environment README, validation runner, its public
refusal tests, and validation-runner notes. The coordinator recomputed all
eight snapshot and delivered-file hashes: each matches the manifest. This is
source identity evidence, not a new build or test run.

## Preserved requirements

All paths are relative to `pfds/`; these files are outside the source diff.

| Requirement source | SHA256 |
|---|---|
| `session/requirements/REQUEST-direct-toolchain-041.md` | `16845edec15c311e0cfd5ed5d4f5c4feb61e7ad96545653d5b872309d26464bc` |
| `session/environment/direct-toolchain-implementation-scope-041.md` | `05c125ee129eafc8f45f9367be16259c3239c7b3945c32f62effba1f1b4c922c` |
| `session/requirements/REQUEST.md` | `b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499` |
| `session/requirements/REQUEST-union-v2.md` | `3336bed1154438b3683aeb5a1c63fee44e87aff190f5ff69e34705a780b9d22c` |

Applicable repository guidance is pinned by the candidate: `AGENTS.md`,
README environment/build-audit sections, implementation and TDD skills,
code-review and its heuristics, and `docs/agents/review-loop.md`. Relevant
additional references are resolved from that snapshot by each axis.
The user's Nix clarification and existing authorization for public CLI/stock
checks take precedence over conflicting skill/environment defaults.

## Validation evidence

The isolated-candidate aggregate records three successful commands: the Lean
and Lake public CLI suite, the Lake native-executable build/run suite, and
three validation-runner public refusal tests. Detailed evidence contains
actual exact version output, valid-theorem acceptance with no axioms,
false-theorem rejection with a type-mismatch diagnostic, Lake compilation and
linking, and executable output `42`. The aggregate identifies this candidate,
records a clean snapshot and confirms delivered-source identity.

| Evidence | SHA256 |
|---|---|
| `session/validation/direct-toolchain-candidate-validation-r1-041.json` | `f2266f8d4cc2340a34cdd3309830ebd542e8dc3470e5f938fed573b8995f4e01` |
| `session/validation/direct-toolchain-candidate-cli-r1-041.json` | `e8e07998319c3e72f50f648b57aec5bd4919a6753e586e9f692d66e5083ad9d3` |
| `session/validation/direct-toolchain-candidate-lake-r1-041.json` | `6517e33e61aed56beaf701590803e3ed1e6e262a604c5332a2b913c3efebc300` |
| `session/validation/direct-cache-bootstrap-041.json` | `ba61cace36d2c602f2f4f1c93c4e977771f0e6a8e4ae5dbed8572749510a979e` |
| `session/validation/direct-cache-get-041.json` | `fb2dafe96aaee4133356aaca8ccf406457fd0de5e20b43d00244f39dc44ddf73` |
| `session/environment/direct-dependencies-after-cache-041.json` | `12054d8a6fd75348ccba9d454c3807a6268d0f6bc29375b2dd80b2f22fd212f8` |

Cache/bootstrap outcomes are adjacent operational evidence from the recorded
formal-candidate checkout. They are not formal acceptance. The cache commands
exited zero, and the post-cache record confirms all nine dependency revisions,
origins and clean source checkouts against the unchanged manifest. Detailed
cache logs are retained alongside their JSON records.

The scope manifest's pre-validation `Pending` field is historical; the later
candidate-validation aggregate supplies the completed same-candidate evidence.
No completed full or focused formal-candidate runner is claimed here. Matching
successful checks are reused; the reviewers were instructed not to rerun them.

## Round 1 outcomes

| Axis | Independent reviewer | Outcome |
|---|---|---|
| Standards | `/root/lean_native_path_options/standards_direct_toolchain_r1` | Findings-present; 2 unresolved, worst Medium |
| Spec | `/root/lean_native_path_options/spec_direct_toolchain_r1` | Findings-present; 2 unresolved, worst High |

No earlier matching completed operational review existed at dispatch. Both
reviewers received the exact base/candidate/diff, complete requirements,
exclusions, standards, matching validation and its limitations. Each must
review the whole operational candidate. Standards and Spec findings remain
separate.

Complete reports:

- `session/reviews/direct-toolchain-standards-r1.md`, SHA256
  `a286dc7fdb24d2b2fdbd85fcd5d9aa5c6000d51e976f6ae9c46c99bfc14542d4`.
- `session/reviews/direct-toolchain-spec-r1.md`, SHA256
  `c1a00422ebe8cd8bbbbf8e75d98dc9251ab8dad9b07dfd4b6691b3ed5508d051`.
- `session/reviews/direct-toolchain-coordinator-r1.md` records reconciliation.

## Retained findings

Standards identifiers are allocated from `DTS-001`; Spec identifiers from
`DTP-001`. Preserve returned IDs and dispositions through every correction
round. Full axis reports remain authoritative for their complete findings.

### Standards

| ID | Severity | Finding | Status |
|---|---|---|---|
| DTS-001 | Medium | The runner and recovery handoff omit the required fresh-validation route and mode-bound retained verification. | Unresolved on round 1; fixed with review evidence on round 2. |
| DTS-002 | Medium | Both smoke tests assume the excluded temporary parent exists, preventing their use after cold recovery. | Unresolved on round 1; fixed with review evidence on round 2. |

No Standards finding is resolved by the Spec outcome or severity assessment.

### Spec

| ID | Severity | Finding | Status |
|---|---|---|---|
| DTP-001 | High | The full runner supports only incremental execution/records, so it cannot carry the required first fresh verification after the tooling/runtime transition. | Unresolved on round 1; fixed with review evidence on round 2. |
| DTP-002 | Medium | Both smoke tests assume `session/tools` exists, so cold recovery omitting that reproducible directory fails before the public probes. | Unresolved on round 1; fixed with review evidence on round 2. |

### Implementer disposition

The implementer explicitly confirmed that no saved exemption from README's
fresh-verification requirement exists. Planned correction: an explicit full
fresh route, verification bound to the actual stock-record mode, and no
`--fresh` or `--jobs` flag passed to stock verify. The first full invocation
under the restored runtime will use fresh mode with one job. No formal gate
had started when this disposition was supplied.

The implementer separately identified the cold-recovery temporary-directory
issue, which Spec inspected and confirmed. The planned fix is for each smoke
test to create its workspace-local temporary parent. These plans do not close
the findings; fixes require a new immutable candidate and both review axes.

## Current disposition

Round 1 is **not accepted**: both independent outcomes are Findings-present.
The coordinator retains all four axis-specific IDs, with no merged or
normalized severity. They concern two implementation corrections. There is no
separate evidence-access blocker and no formal gate is claimed complete.

Round 2 **passes both independent axes** for operational helpers only on
`822cb7adeed4943acaf10454e9facfc2e3ee8ceb`. All four prior IDs are fixed with
review evidence; no new or unresolved findings remain. The coordinator's
final identity check at `2026-11-03T15:13:17.631871+00:00` confirmed exact
candidate HEAD, an empty isolated-checkout status, and all eight snapshot and
delivered hashes matching the round 2 manifest. Any subsequent source change
requires an applicable new review; this result does not approve a moving tip.

Rounds 3 and 4 remained incomplete, and rounds 5 and 6 were superseded before
approval. Round 7 now **passes both independent axes** for the complete
18-file operational scope on `af2c53dce68ebb122c81175312d6bb30df9aac05`.
All four retained findings remain fixed with evidence; no new or unresolved
finding remains. Final delivered identity matched at
`2026-11-03T17:14:04.672619+00:00`. Formal full/focused/audit/source-review
and chapter/union acceptance remain separate and are not supplied by this pass.

## Round 2 candidate and evidence

- Base remains `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
- Candidate: `822cb7adeed4943acaf10454e9facfc2e3ee8ceb`.
- Retained candidate ref: `refs/pfds-review/direct-toolchain-r2-041`.
- Isolated checkout: `pfds/review-direct-toolchain-041-r2`.
- Full diff: `git diff 76d77a107deb37c30e0b061c30b03a3f8c6aa12c...822cb7adeed4943acaf10454e9facfc2e3ee8ceb`.
- Single commit: `822cb7a chore(toolchain): support fresh validation and cold recovery`.
- Full scope remains eight files, now 968 inserted lines relative to the base.
- Scope manifest: `session/validation/direct-toolchain-candidate-r2-041.json`,
  SHA256 `5f556fb8f0121c55ad6c69589c247bde8bbd7ee6a467ce5e18387d9ec9b99de6`.

The coordinator resolved HEAD/ref/merge base and recomputed all eight source
hashes in both the isolated and delivered locations: they match the new
manifest. Requirement versions and applicable standards are unchanged. Both
same independent reviewers were dispatched on the complete new scope with
all four existing finding IDs, historical reports and correction evidence.

### Validation and review-checkout index reconciliation

The original round 2 aggregate records three genuine artifact commands with
exit zero. The CLI and Lake suites each ran against a newly constructed
separate toolchain profile in a recovery workspace; their temporary parent
was absent before each invocation. The refusal suite also passed, including
the new fresh-argument path.

That aggregate correctly reported `passed: false` because the isolated
review checkout had no private Git index: the implementer accidentally
carried the temporary snapshot `GIT_INDEX_FILE` setting into worktree
creation. The coordinator independently observed the resulting staged
deletions/untracked files. The implementer recreated only the new checkout's
index from its exact HEAD; no working source files were changed. The original
failed aggregate is preserved. A separate reconciliation records the actual
successful commands, original aggregate hash, index repair and explicit
same-input evidence reuse. The coordinator then independently confirmed an
empty status, exact candidate/merge base and unchanged matching source hashes.

This is operational artifact evidence reuse after metadata repair, not a
successful formal candidate check or a relabeling of the failed aggregate.
Both reviewers were supplied the full anomaly and reconciliation for their
own assessment. No runtime test was repeated by the reviewers/coordinator.

| Round 2 evidence | SHA256 |
|---|---|
| `session/validation/direct-toolchain-candidate-validation-r2-041.json` | `d65acb992ea7ef25660873c88be52efad91477150e456150b0467fb5da329fc4` |
| `session/validation/direct-toolchain-candidate-validation-r2-reconciled-041.json` | `998a2fb578d337f92174c0d4343fa8bd593f32c91f7cf753d8a033e3981c9916` |
| `session/validation/direct-toolchain-candidate-cli-r2-041.json` | `4b9b52f5c63e5d59e6e025b050ca4ea92d4221efcc8b161ab883337a2fe1ca22` |
| `session/validation/direct-toolchain-candidate-lake-r2-041.json` | `69eb08b9cfa19c683ffbb0197f38418b5e664fc45a2672214150326a7404e44b` |
| `session/validation/direct-validation-fresh-red-041.json` | `30ffb9c2185a876bfdc09bd793599e8e928965783bf5a2f0bc08e944bca7aebe` |
| `session/validation/direct-toolchain-cold-red-041.json` | `f01006f8fc4add3327e6189e6f81fc894b3f267451dc3dd0966daac63e803c06` |

## Round 2 outcomes and closure evidence

| Axis | Outcome | Prior finding dispositions | New/unresolved | Worst unresolved |
|---|---|---|---:|---|
| Standards | Passed | DTS-001 fixed; DTS-002 fixed | 0 / 0 | None |
| Spec | Passed | DTP-001 fixed; DTP-002 fixed | 0 / 0 | None |

The same independent reviewers reassessed the complete eight-file candidate,
retaining prior analysis of unchanged files and inspecting every correction
and affected contract. Full reports preserve each original severity and the
specific source, red/green, cold-profile and reconciliation evidence used to
close it:

- `session/reviews/direct-toolchain-standards-r2.md`, SHA256
  `6a81a379f6af97b5d380ab78e08e6d3a0561e1c2689d084e0455249289e13485`.
- `session/reviews/direct-toolchain-spec-r2.md`, SHA256
  `cbc435d532e0c8e56fd98c018e62522c71fcd45bbc4b0bcca9b57008bb592b35`.
- `session/reviews/direct-toolchain-coordinator-r2.md` records final
  reconciliation and delivery identity.

Fresh full command/mode binding and the documented first-run requirement
resolve DTS-001 and DTP-001. Parent creation plus actual absent-parent
CLI/Lake success resolve DTS-002 and DTP-002. Both reviewers independently
accept the limited reuse after index-only repair because those actual test
inputs did not depend on the repaired review index. The original failed
aggregate remains failed and preserved; no formal check was run under that
metadata state.

This pass establishes operational helper implementation and its applicable
artifact validation. It does not establish a fresh full project build,
exhaustive axiom audit, focused signed-potential build, final stock candidate
verification, or any mathematical/chapter/whole-union acceptance. The first
formal full run under the restored runtime must use the corrected fresh route
with the established serial resource policy and its own genuine evidence.

## Round 3: requested environment handoff

The user subsequently requested environment-recovery instructions in every
checkpoint and a prudent robustness comparison with an attached guide from
another agent. This is an expansion of the same operational-helper loop.
The complete saved requirement is
`session/requirements/REQUEST-environment-handoff-042.md`, SHA256
`200789123c60ae137967f881207194412eecea72ba2fc80247978075bd6a4602`.
Earlier requirements retain their recorded versions and force.

The supplied comparison attachment is preserved exactly at
`session/references/conaled-environment-guide-from-user-042.md`, SHA256
`ef85039f6097a1a646bb2b980178a2285e23124e5881686f68020acfa2f5d4f1`.
It describes a different workstream. Its checkpoint, source-branch and old
Library references are comparison data; no other-conversation Library access
or substitution for the PFDS history is authorized or performed.

### Immutable scope and independent dispatch

- Fixed base and merge base: `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
- Candidate: `6526e5cdcde2e58c8fb0839690c34f3f6c04787c`.
- Retained ref: `refs/pfds-review/direct-toolchain-r3-042`.
- Isolated checkout: `pfds/review-direct-toolchain-042-r3`.
- Full diff: `git diff 76d77a107deb37c30e0b061c30b03a3f8c6aa12c...6526e5cdcde2e58c8fb0839690c34f3f6c04787c`.
- Commit: `6526e5c docs(toolchain): preserve reproducible PFDS recovery and route comparison`.
- Full scope: ten files, 1,484 inserted lines relative to the fixed base.
- Manifest: `session/validation/direct-toolchain-candidate-r3-042.json`,
  SHA256 `6610e30dec43e362043e9925785f82bd80d2b0f6a650612d97ff02491a02f242`.

The eight earlier helpers are byte-identical to approved round 2. The added
files are `session/environment/RECOVER-ENVIRONMENT.md` and
`session/environment/environment-route-comparison-042.md`. The coordinator
confirmed exact HEAD/ref/merge base, empty isolated status, a nonempty full
diff, and matching hashes for all ten snapshot and delivered files. The
existing eight were separately compared with the round 2 manifest.

The same independent Standards and Spec reviewers were dispatched on the
complete ten-file scope, retaining their prior analysis and DTS-001/DTS-002
and DTP-001/DTP-002 closures. New finding IDs, if required, start at DTS-003
and DTP-003. Neither axis's assessment is replaced by coordination or by the
unchanged-file evidence reuse.

### Validation and evidence boundaries

`session/validation/direct-toolchain-candidate-validation-r3-042.json`,
SHA256 `61b5c1f93265e382177803849ced64f7b6bd5a3fd2d977ff76c76cdaa83ef56d`,
records twelve successful checks of the isolated documentation: shell syntax
checks and two Python recipes taking only existing-state verification branches.
This does not assert a complete new cold acquisition/restoration run.
The record explicitly reuses matching actual operational results for the
unchanged eight helper sources and lists the operations not repeated.

The Ubuntu alternative acquisition has separately retained authentication
evidence. The installed public keyring is the attributed trust input;
successful gpgv verification authenticates the release/index/package chain.
The extracted executable was not executed or selected. No runtime-equivalence,
performance or formal-check conclusion follows from acquisition alone.

| New evidence | SHA256 |
|---|---|
| `session/environment/qemu-ubuntu-042/acquisition.json` | `b98fd7647b12efec8706a9001de50ad169c1044f49f5c174d613ab1fbf827e42` |
| `session/environment/qemu-ubuntu-042/report.md` | `476ece2d3566ffe37cb111c18210629e1fe302f791b092e6309b6f81945380fe` |
| `session/environment/qemu-ubuntu-042/authentication-inputs.json` | `3171af5280e3f6983bc2a6938175635ec183a1c54023dda3369712f602ed3652` |

At dispatch, the exact901 fresh formal run continued separately. The exactd24
focused run had genuinely exited 1 at 2026-11-03T16:00:25Z with retained
unchanged-input evidence and example-proof errors. Those source failures are
not changed or reclassified by this operational documentation review.
No formal acceptance is implied. Reviewers were instructed not to modify or
repeat running inputs, builds, runtime acquisition or network operations.

### Round 3 current state

Both independent axes are in progress. No new finding or passing outcome has
yet been returned. Existing round 2 finding closures remain historical facts;
the expanded documents require their own complete current-candidate outcomes.

The implementer subsequently reported that `session/checkpoint.py` still
generates archive-entry README instructions using Nix and plain
`lake exe cache get`. It plans a narrow template and restore-success-pointer
correction in a further immutable candidate, adding that generator to the
review scope with its prior provenance retained. Both reviewers received this
observation and continue their current analysis. Round 3 is not final delivery;
the next candidate and its applicable evidence must be reviewed before
checkpoint 042 is frozen. No active validation/controller/profile input is
changed by this planned documentation correction.

## Round 7: native runtime and complete recovery handoff

The operational loop continues with the same fixed base. Rounds 3 and 4 did
not receive completed independent outcomes before user steering; rounds 5
and 6 were superseded before approval. Their snapshots, validation results,
and historical evidence remain retained. None is inferred to have passed
review. The earlier eight-file round 2 approval and its four closed findings
remain valid only for their recorded scope and inputs.

The user's additional requirement is
`session/requirements/REQUEST-native-toolchain-042.md`, SHA256
`d76dc8dcf771a227779628de91e75c4b63a2898b95e7b30035de83537dae5195`.
It requests a faster native route or another available environment while
preserving exact versions, genuine behavior, historical outcomes, isolated
validation, independent review, and the remaining formal gates. Earlier
requirements and their versions remain unchanged.

### Replacement coordination and independent axes

`/root/direct_toolchain_validation_plan` now coordinates this same loop and
reconciles the two independent outcomes. This coordinator authored an earlier
version of the original validation runner and performs no third Standards
or Spec review. Implementation remains with the parent and assigned authors.

- Standards: `/root/recovery_audit`, which confirmed that its only prior
  authored files were separate checkpoint-recovery audit evidence, not any
  toolchain implementation in this source scope.
- Spec: `/root/chapter02_continuation_plan`, which confirmed that its prior
  work was read-only source/continuation and supplied-guide analysis, with
  no authored toolchain implementation.

The native adapter/test authors are not assigned independent review of their
own implementation. Both replacement reviewers received the full requirements,
standards pointers, immutable scope, retained findings, prior reports, actual
validation and reuse limitations. They must read the complete source scope,
while retaining matching analysis of unchanged files. They are instructed to
perform no builds, tests, network operations, protected-surface probes, or
implementation edits. Their reports are the two review axes; coordination
does not supply another substantive approval.

### Immutable round 7 scope

- Base and merge base: `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
- Candidate: `af2c53dce68ebb122c81175312d6bb30df9aac05`.
- Retained ref: `refs/pfds-review/native-toolchain-r7-042`.
- Isolated checkout: `pfds/review-native-toolchain-042-r7`.
- Diff: `git diff 76d77a107deb37c30e0b061c30b03a3f8c6aa12c...af2c53dce68ebb122c81175312d6bb30df9aac05`.
- Commit: `af2c53d feat(toolchain): bind corrected focused native candidates explicitly`.
- Full scope: 18 files, 3,308 inserted lines relative to the fixed base.
- Manifest: `session/validation/native-toolchain-candidate-r7-042.json`,
  SHA256 `257e31713ec28c4c12cafb7635ad14098f09d8bc765c79d541b7ff30d27ac593`.

Before dispatch, the coordinator resolved candidate HEAD/ref/merge base,
observed an empty isolated status, verified a nonempty diff whose file set
exactly equals the manifest, and recomputed every committed, isolated, and
delivered file hash. All 18 matched. All saved requirement/attachment hashes
also matched. These checks establish identity, not a third code review.

The scope comprises the original eight operational helpers, the full recovery
and route-comparison documents, the checkpoint entrypoint/template, the native
metadata adapter and profile launcher, three native contract-test files, and
the native evidence runner and its public refusal tests. Original compiler
and dependency pins and stock proof checks remain outside the authored changes.
Formal candidates, runtime binaries/caches, prior evidence, trackers,
requirements, reviews, and provenance records are excluded from the source
diff and retain their independent obligations.

The full checkpoint generator is included because it was absent from the
fixed repository base. Its retained predecessor is
`session/validation/checkpoint-generator-before-042.py`, SHA256
`617c14ed63170ee39a8ac1df2eb4cc20b1b509ebd5f1d4c16ae4e469b7ed51ab`.
The recorded task delta is the generated README and restore-success pointer;
both axes receive the complete captured generator and the prior provenance.

### Artifact validation and exact-input reuse

`session/validation/native-toolchain-candidate-validation-r7-042.json`,
SHA256 `e142a541377e59027008d2299fc19dcb9b5a1613cc460409ffbf90c9ae3b8176`,
reports a clean exact candidate, matching delivered hashes, four successful
native-controller public refusal tests, documentation shell syntax checks,
and two genuinely executed existing-state verification recipes. The manifest's
earlier `Pending` validation field predates this completed aggregate.

The aggregate explicitly reuses the following retained evidence:

| Evidence | SHA256 |
| --- | --- |
| `session/validation/native-toolchain-candidate-validation-r6-042.json` | `6f784d8cae601cd843964d2775f03499fd410b2e57a22ca0c15aafabe48d5951` |
| `session/validation/native-candidate-lake-r6-042.json` | `72127febfd75144b90e124d886eba73bcdff017bb6d306a46c0ef3adb5fba949` |
| `session/validation/native-candidate-contract-r6-042.json` | `d2b75abc87b8ddc9b4e22492281bbc20f25749a4faf641aa3af1bd9b838f7b36` |
| `session/environment/native-cold-profile-r6-042.json` | `61a59e98bf1f88af14fce69ef3f84b7c175522ffaae59206cccfef51446bd642` |
| `session/validation/direct-toolchain-candidate-validation-r2-reconciled-041.json` | `998a2fb578d337f92174c0d4343fa8bd593f32c91f7cf753d8a033e3981c9916` |
| `session/validation/direct-toolchain-final-verification-041.json` | `a441a4555b1b5ed05ef42ef81e5fc82525b4e506f2aae68d062a0f962260435d` |

The coordinator recomputed those evidence hashes and verified that all 14
listed r6 source inputs match r7 and all original eight files match approved
round 2. The r6 records report a cold native profile constructed from captured
source, exact versions, a genuine valid theorem/no-axiom result and false-proof
rejection, Lake compilation/linking/execution, and all 18 metadata-contract
cases. The changed r7 native controller/test and recovery/comparison documents
have separately recorded applicable checks. Both independent reviewers assess
this exact-input reuse and its coverage; no reviewer or coordinator reruns the
mechanical checks merely to duplicate matching evidence.

This evidence does not complete a formal candidate gate. Full native
prerequisite 901 validation remains pending. A prior focused proof candidate
genuinely failed; the corrected proof candidate is being tested separately
under frozen controller inputs. Its results are not relabeled by this tooling
review, and operational approval cannot establish formal/chapter/union
acceptance.

### Round 7 review state

Both independent axes have been dispatched on the exact candidate above.
Reports are reserved at:

- `session/reviews/direct-toolchain-standards-r7-042.md`.
- `session/reviews/direct-toolchain-spec-r7-042.md`.
- `session/reviews/direct-toolchain-coordinator-r7-042.md`.

DTS-001/DTS-002 and DTP-001/DTP-002 retain their round 2 closure evidence and
must be checked for regression. New identifiers start at DTS-003 and DTP-003.
At dispatch, no round 7 passing outcome or new finding had yet been returned.
The completed outcomes and final identity check are recorded below.

### Round 7 completed outcomes and final identity

| Axis | Independent reviewer | Outcome | Retained dispositions | New/unresolved | Worst unresolved |
| --- | --- | --- | --- | ---: | --- |
| Standards | `/root/recovery_audit` | Passed | DTS-001 fixed; DTS-002 fixed; no regressions | 0 / 0 | None |
| Spec | `/root/chapter02_continuation_plan` | Passed | DTP-001 fixed; DTP-002 fixed; no regressions | 0 / 0 | None |

Complete frozen reports:

- `session/reviews/direct-toolchain-standards-r7-042.md`, SHA256
  `3b143b5b92f51efaa8aecfc86de2fa7a3316ce1cc320a490c81ffc2af064ca0e`.
- `session/reviews/direct-toolchain-spec-r7-042.md`, SHA256
  `c7df56778cba429b9d2c8c67e5a5f1e52f35e6a106a9ac36a2ecb0f89ac81b04`.
- `session/reviews/direct-toolchain-coordinator-r7-042.md` records complete
  reconciliation, evidence reuse, scope limits and final delivery verification.

Both independent axes read the complete 18-file scope, assessed applicable
standards and full saved requirements, and accepted the explicit matching-input
r6/r2 evidence reuse with its stated limits. There are no operational review
findings or evidence-access blockers. The brief Spec read-only transport outage
resolved on retry, with no omitted review coverage. No new finding ID was
allocated, and original findings/severities remain retained separately.

The coordinator read both complete reports and at
`2026-11-03T17:14:04.672619+00:00` rechecked exact HEAD/ref/merge base, empty
isolated status, all 18 committed/isolated/delivered hashes, requirements,
manifest/aggregate identities, and both report hashes. Everything matched.
This was identity verification, not a third substantive review or a formal
stock candidate check.

The operational review is complete and frozen for checkpoint capture. It does
not depend on waiting for the separate focused proof job to finish. Any partial
formal run must retain its actual state; full native 901 validation, exhaustive
audit, formal source reviews and immediate final stock verification remain
their own gates. No mathematical, chapter or whole-union acceptance is advanced.
Later authored-source changes require a new applicable candidate review.

## Round 9 continuation — real Elan recovery appendix (043)

This continues the same operational loop. The fixed base is still
`76d77a107deb37c30e0b061c30b03a3f8c6aa12c`; the new exact candidate is
`ff3f709723e5c49e5ba40798abbed7d36141a6fb`, retained at
`refs/pfds-review/native-toolchain-r9-043` in the clean isolated checkout
`pfds/review-native-toolchain-043-r9`. The full three-dot task diff contains
19 files and 3,456 insertions. The complete dispatch is
`session/reviews/direct-toolchain-dispatch-r9-043.md`.

All original 18 round 7 source blobs and modes match. The exact r7-to-r9 delta
adds only `session/environment/RECOVER-ELAN-REGRESSIONS.md`. Round 8 candidate
`d95518fde8cfc877da9d2bfc720ed4fd1f4698ba` was superseded before axis dispatch
because two native-controller executable modes were accidentally normalized in
that snapshot; round 9 restores their approved 100755 modes. The discrepancy,
old snapshot and genuine round 8 cold-recipe evidence remain retained, without
an invented round 8 review or approval. No delivered runtime/controller changed.

Current immutable input records:

- Manifest: `session/validation/native-toolchain-candidate-r9-043.json`, SHA256
  `af74d3d1ab35c9a26dd1034bf223d2479232d6e82732c05ac72b701c7f0e09ec`.
- Artifact aggregate: `session/validation/native-toolchain-candidate-validation-r9-043.json`,
  SHA256 `a86be8c447403d0947e7542461471e47570b69e484e4464522c3a12661221ddc`.
- Coordinator dispatch identity:
  `session/validation/native-toolchain-coordinator-dispatch-r9-043.json`, SHA256
  `d4ac3310ba40cf5a93d8b4a352fbbafacdc9c14a4e460e827210c16726c3549f`.

The read-only dispatch check matched HEAD/ref/merge base, clean isolated status,
all 19 committed/isolated/delivered file hashes and modes, and all six saved
requirement hashes. It matched the original 18 files to r7 and confirmed the
one-file delta. This is identity verification, not another review or test.

The aggregate explicitly reuses actual round 8 appendix validation on identical
blobs and unchanged native inputs, and original18 round 7 evidence on identical
blobs and modes. The round 8 cold setup genuinely downloaded and verified the
official Elan archive, extracted the expected executable, used real Elan's
supported entrypoint and local custom link, and observed actual selected
Lean 4.35.0. All three appendix shell blocks were syntax checked. The two restored
controller modes do not participate in that setup. No stock regression suite
is claimed to have run; reviewers assess this evidence and reuse separately.

The coordinator remains `/root/direct_toolchain_validation_plan`, with no third
source-review role. Independent Standards is now `/root/lean_native_path_options`,
which confirmed it authored none of the full19 source files. Its excluded
analyses/review records do not disqualify it. Independent Spec remains
`/root/chapter02_continuation_plan`, which confirmed it authored neither the
appendix nor its command recipe. `/root/recovery_audit` is not assigned this
appendix's independent review because it supplied the planned Elan recipe.

Both axes receive the complete19 scope, six requirements, candidate guidance,
all prior dispositions, exact artifact evidence and reuse limitations. They
review the whole task while retaining matching r7 analysis. Original DTS-001/002
and DTP-001/002 retain their severities and fixed dispositions subject to
regression assessment. New IDs begin at DTS-003 and DTP-003. Reports are
`direct-toolchain-standards-r9-043.md` and `direct-toolchain-spec-r9-043.md` in
this review directory. At dispatch there is no r9 axis result or approval.

No reviewer or coordinator runs tests/builds/network/protected probes or edits
source/runtime/controllers. The active native full901 gate and future stock
regressions remain separate. Operational approval cannot accept formal sources,
signed potential, any chapter, or the union. The completed outcomes and final
read-only identity will be appended after both frozen reports are reconciled.

### Round 9 completed outcomes — findings retained for correction

Both independent reports are complete and frozen on the same exact r9 candidate.
The coordinator read both reports in full and retained separate findings:

| Axis | Outcome | Original dispositions | New/unresolved | Worst unresolved |
| --- | --- | --- | ---: | --- |
| Standards | Findings-present | DTS-001/002 Medium fixed, no regression | 1 / 1 | DTS-003 Medium |
| Spec | Findings-present | DTP-001 High and DTP-002 Medium fixed, no regression | 1 / 1 | DTP-003 Medium |

- Standards report: `session/reviews/direct-toolchain-standards-r9-043.md`,
  22,456 bytes, SHA256
  `b40654b0be536883a61ef62c1dd9dde10868ffd4b3fa9a9297f38212b7fb2a7b`.
- Spec report: `session/reviews/direct-toolchain-spec-r9-043.md`, 23,878 bytes,
  SHA256 `1651fad484a6c01c68e3038a980e2edce9cbe309f9fef84b1a8167731fd60526`.
- Complete reconciliation: `session/reviews/direct-toolchain-coordinator-r9-043.md`.

**DTS-003 — Medium — unresolved.** The appendix's checker-suite child command
appends the verified Elan package after ambient PATH. Stock `test-check.py`
invokes bare `elan`, so an earlier executable wins. Absolute setup checks and
shell syntax checks do not establish that real selection interface. Standards
requires a narrow correction binding bare lookup to the verified package, with
appropriate actual public-selector evidence under the same native environment.

**DTP-003 — Medium — unresolved.** Independently, the same selection behavior
violates the documented reproducible takeover/explicit-tool selection contract.
A compatible ambient Elan may work, but it is not the verified artifact whose
identity and behavior the handoff establishes. Spec requires prepending or
otherwise explicitly selecting the genuine package and retaining actual
effective path/version/native Lean selection evidence. This finding remains
separate from DTS-003, with its own requirement and disposition.

Root accepts the narrow correction and will capture a new candidate. Neither
finding is closed by the proposal. The original18 source analysis and r7 evidence
remain valid for matching inputs; actual r8 cold setup remains valid for its
limited coverage. No other new finding or evidence-access blocker was reported.

Root separately preserved a genuine public-selector red case in
`session/validation/elan-path-selection-red-r9-043.json`, SHA256
`08a5bcf224750c9dfd154c571be36e1f2ae5fdb2fdb55d0712636c84df7682c3`.
With the exact r9 environment/native launch and only the suite entrypoint
replaced by a selector probe, an earlier owned `elan` path is selected. The
probe exits 7 before invoking that wrong executable. This corroborates the
failure without a fabricated version or a claimed suite run. Frozen reviewer
reports are not rewritten around later evidence.

At `2026-11-03T18:01:15.741892+00:00`, final coordinator identity matched
HEAD/ref/merge base, clean isolated status, all19 source contents/modes,
six requirements and eight record hashes. Receipt:
`session/validation/native-toolchain-coordinator-identity-r9-043.json`, SHA256
`9d762ec88725ccc74db261d811e333aabe0ebd45d5979a9d4bdafd6244001ea6`.
This is a findings handoff, not approval. The round is frozen for correction
and later checkpoint capture. Both003 findings and their severities must carry
into the next full-scope continuation; formal and stock-suite obligations stay
separate and pending their own actual records.

## Round 10 correction continuation — explicit Elan selection (043)

The same independent axes continue the same full 19-file operational task on
candidate `060e6b877b8db57a30f947b996b7dfe34a5401a1`, fixed base/merge base
`76d77a107deb37c30e0b061c30b03a3f8c6aa12c`, retained ref
`refs/pfds-review/native-toolchain-r10-043`, clean isolated checkout
`pfds/review-native-toolchain-043-r10`. The full diff has 19 files and 3,457
insertions. Relative to r9, only the appendix's PATH order and explanation
change. Original18 contents and all 19 modes are unchanged.

Manifest `session/validation/native-toolchain-candidate-r10-043.json` has SHA256
`37e14623d090f9bf6016132397fff42f4da4b7dc526b154348c4b15d59be0cba`.
Aggregate `session/validation/native-toolchain-candidate-validation-r10-043.json`
has SHA256 `c0b89a23b1727f6e190019bc0f6f44dbc74a1259c2839d26e234f643bebdf874`.
The complete continuation dispatch is
`session/reviews/direct-toolchain-dispatch-r10-043.md`.

At `2026-11-03T18:14:13.814516+00:00`, coordinator identity matched the exact
clean candidate/ref/base, all 19 source hashes/modes, original 18 reuse, all six
requirements and nine relevant records. Dispatch receipt:
`session/validation/native-toolchain-coordinator-dispatch-r10-043.json`, SHA256
`a733011a3323059c245fd84599a2b028b90a740ccf56eea984de727ddb3d73b6`.

The genuine selector green record is
`session/validation/elan-path-selection-green-r10-043.json`, SHA256
`07fca1d9243461884badf2f0e85e1ef00ef98f1cd795d9b8ab279d63431dff90`.
Using the corrected documented child environment/native launcher and substituting
only the suite entrypoint with a public probe, it returns0, selects the verified
official Elan despite an earlier owned ambient entry, and observes actual Elan
4.2.4/hash/which and selected exact Lean4.35.0. The genuine r9 red exit7 remains
retained. All three shell blocks were syntax checked; unchanged first cold setup
and original 18 evidence have explicit matching-input reuse. No suite is claimed.

Standards `/root/lean_native_path_options` and Spec
`/root/chapter02_continuation_plan` retain their independence and full 19 scope.
Their concise complete continuations may link matched r9 analysis and directly
assess the changed interface/evidence. DTS-003 Medium and DTP-003 Medium remain
unresolved at dispatch; only the respective reviewer can establish closure.
All original 001/002 dispositions and severities carry forward unchanged. No
r9 or earlier incomplete result is relabeled. Reports are reserved at
`direct-toolchain-standards-r10-043.md` and
`direct-toolchain-spec-r10-043.md` in this directory.

The native full 901 has now been intentionally interrupted: its actual tool130,
unchanged original partial record/log and separate interruption sidecar do not
establish build/audit success. Independent copied-module-format probes and all
stock-suite/formal/chapter obligations remain separate. No review execution or
implementation/runtime edit is authorized in these axis continuations. Root
owns final identity and checkpoint 043 after completed reconciliation.

### Round 10 completed outcomes and closure evidence

Both independent full-scope continuations are complete and frozen on exact
candidate `060e6b877b8db57a30f947b996b7dfe34a5401a1`. The coordinator read
both complete reports and retained their separate findings and severities:

| Axis | Outcome | Retained dispositions | New/unresolved | Worst unresolved |
| --- | --- | --- | ---: | --- |
| Standards | Passed | DTS-001/002 Medium fixed without regression; DTS-003 Medium fixed with r10 evidence | 0 / 0 | None |
| Spec | Passed | DTP-001 High and DTP-002 Medium fixed without regression; DTP-003 Medium fixed with r10 evidence | 0 / 0 | None |

- Standards: `session/reviews/direct-toolchain-standards-r10-043.md`, 10,429 bytes,
  SHA256 `a616cf08f1176032ce5b901947f9ba6231ffac546d4206d83ed29874ad0a4500`.
- Spec: `session/reviews/direct-toolchain-spec-r10-043.md`, 10,046 bytes, SHA256
  `d7dfee97019b9df1f61e59ba2b9951f750fe235faa2290b87dca2f341a3e91d0`.
- Reconciliation: `session/reviews/direct-toolchain-coordinator-r10-043.md`.

Both axes independently matched the full 19 source/mode scope, requirements,
guidance and retained evidence, incorporated their frozen r9 whole-task analyses,
and directly checked the changed command-selection interface. Their r9 reports
remain Findings-present on that older candidate. The new outcomes apply to r10.

**DTS-003 and DTP-003 are each fixed with evidence at their original Medium
severity.** The package now precedes ambient PATH; the unchanged native helper
keeps its compiler bin first, and no Lean/Lake proxies are supplied by the Elan
package. Actual red/green commands differ only in that order, use the same probe
and competing ambient entry, and preserve the documented child/native launcher
with only the suite entrypoint substituted. Red exits with code 7 before invoking the wrong
entry; green exits with code 0 after real official Elan hash/version/which and selected exact
Lean observations. This closes the specific selection gap without implying that
the stock suite ran. All original 001/002 closures and historical results remain.

The reviewers accepted the current three syntax checks and matching-input reuse
of the unchanged r8 cold setup and original 18 r7/r6/r2 artifact evidence. They
found no further operational issue or evidence-access blocker. No mechanical
test, compiler, network or protected-path operation was performed by either
reviewer or coordinator.

Final coordinator identity at `2026-11-03T18:18:29.390442+00:00` matched the
clean exact HEAD/ref/base, all 19 committed/isolated/delivered bytes and modes,
all six requirements and eleven record identities. Receipt:
`session/validation/native-toolchain-coordinator-identity-r10-043.json`, SHA256
`36b61afbfc12302ca11d84ada1a8dacf3dea841ce625dde1c5a55774a13b2df1`.
This is read-only identity evidence; root owns its separate final receipt and
checkpoint 043. The complete operational outcome is frozen. Native full 901's
interrupted partial result, stock suites, separate formal reviews, final stock
verification, chapter order and union coverage retain their own obligations;
none is accepted by this operational pass.

## Round 11 recovery continuation — integration, supplied kit and small checkpoints

Fixed base remains 76d77a107deb37c30e0b061c30b03a3f8c6aa12c. Candidate 4f15ff6f5bc8091104a3572ca8ce3716ed8e78f0 is captured at refs/pfds-review/native-toolchain-r11-045. This is the same operational loop, retaining every DTS/DTP finding and its recorded disposition. New request requirements/REQUEST-recovery-045.md authorizes the supplied kit and compact current-work packaging. Full authored scope is the original 19 files plus environment/RECOVER-INTEGRATION.md. Complete manifest: validation/native-toolchain-candidate-r11-045.json. Independent review is pending; no formal gate/acceptance follows from fixture or setup evidence.

### Round 11 completed independent outcomes and reconciliation

Both independent full-scope axes Passed exact candidate `4f15ff6f5bc8091104a3572ca8ce3716ed8e78f0`
against the unchanged full base `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
The coordinator read both complete frozen reports and reconciled them without
performing a third source review. Standards: zero new/unresolved findings;
DTS-001/002/003 remain fixed at Medium. Spec: zero new/unresolved findings;
DTP-001 High and DTP-002/003 Medium remain fixed with their original scope
qualifications. Historical Elan closure does not claim new-runtime suite success.

Complete Standards report: `direct-toolchain-standards-r11-045.md`, SHA-256
`bc3cebe8df62096442fe8a333901a0c94bc04ffe220563ffd14a4f605b875e4b`. Complete Spec report:
`direct-toolchain-spec-r11-045.md`, SHA-256
`2afa41d9f27c9ea821e3ae2c92c9151e5909da15161639d8fd5e3eeb60ca3903`. Reconciliation:
`direct-toolchain-coordinator-r11-045.md`, SHA-256 `2ddde3b10b660db290a69e12de9d083110a578363945dc1f3647b92e531de871`.
Final coordinator identity receipt: `validation/native-toolchain-coordinator-identity-r11-045.json`,
SHA-256 `142a29c972bd8d2a09691ea96d07f3effe802c9c760040b2ddd4ee83ab734a61`. The final aggregate identity is
`13a3a8ed9731235fa6c10cdc3692f2fd2ba7b478c70c66476ed6c0be60ad1b25`.

Actual artifact validation includes isolated eight-test success, retained red/green
behavior, matching runtime observations, four syntax checks, genuine setup/smokes
and checkpoint045 source restoration. Source, requirement and final evidence
identities matched at coordinator completion. Root retains its separate final
delivered-identity check and checkpoint duty before the new formal gate. No
formal candidate, regression suite, chapter or union acceptance is implied.

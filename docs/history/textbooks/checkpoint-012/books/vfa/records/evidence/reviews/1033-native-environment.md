# #1033 native execution environment review

This is the scoped operational review within the existing enclosing VFA workflow.
It does not replace or approve the still-pending Preface/Perm review in
`1002-Perm.md`. Coordinator: `/root/recovery_audit`; root remains implementer and
acceptance owner. All findings and candidate identities are retained across fixes.

## Round 1: immutable scope and requirements

- Operational repository: `work-state/native-environment-review`.
- Fixed base and verified merge-base: `c411e6c04b4001b80f5b0da812b6792ee9190861`.
- Candidate: `e41336d46dffd7bddd42b242a7ea7484a6055e43`.
- Comparison: `git diff c411e6c04b4001b80f5b0da812b6792ee9190861...e41336d46dffd7bddd42b242a7ea7484a6055e43`.
- Commit: `e41336d feat: add scoped native executable-path compatibility (#1033)`.
- Scope: four added files, 441 lines, no exclusions: `native_app_path.c`,
  `pinned_native_toolchain.py`, `test_native_app_path.py`, and `NATIVE.md`, all
  under the captured repository's `work-state/tooling/`.
- The captured `pinned_toolchain.py` and QEMU `README.md` are unchanged base inputs.
- Formal conaled candidate remains `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`.

The explicit requirement source is `../specs/1033-native-app-path.md`, SHA-256
`e8a1c99ce76ade903a4b85071753a3f23fe854ea1ef1354bb574ddc55b0f2785`, together with
REQUIREMENTS and the accepted AMENDMENTS, including the user's request for
alternatives to emulation. The reviewed AMENDMENTS SHA-256 is
`6786661d35f41ade3ec73f8ce09eab1583c6e50e7903489225a771e79f532ad2`.
Repository standards are routed through conaled AGENTS/README, the shared
review-loop procedure, and code-review skill/heuristics with those user overrides.

The scope is a narrowly declared execution adaptation, preserving official
compiler bytes, source/dependency pins, the QEMU fallback and every formal gate.
The full formal project need not be accepted to assess these external operational
files; this operational review supplies no chapter credit.

## Supplied exact-candidate validation

The coordinator verified completed isolated validation before dispatching either
axis. The record contains 17 individual zero outcomes, a local rebuilt shim
matching its pinned hash, relocated parent/child version and proof fixtures,
and unchanged before/after source identities. Generated isolated runtime state
is explicitly distinguished from captured source. Existing complete Squares
evidence is reused with its source/runtime binding; no successful test was rerun
by a reviewer.

Evidence paths below are relative to `../validation/1033-native-environment/`:

| Record | SHA-256 |
| --- | --- |
| review-identity.json | `882df7d34ba3082f100f36074c98f214f00916624cc18bf59dccf568ba0e880d` |
| isolated-validation.json | `ed89d24bc957222d0e56e14d79d3b09be906961bf7648e59e2d2f7da659a7339` |
| boundary-tests.json | `8dfd5fe0cd4c0ac3548bc1b6eea018b73274fa773c4baff264dbd6a11f93afb3` |
| native-smoke2.json | `6a74f3aea3aafbf9ba9d18212f7b1245157afed1ace5489b55ccaefde21bdfa5` |
| native-squares-resource-sample.json | `8140085f8cfc9d22b66cc0c118048a94e3ec611503cb1c69aaa6e02d7029a115` |
| host-memory-observation.json | `ca763c4f063e641a64b3c946af54a7579afda65f5120cae11d7916c155240fad` |

Also supplied: `shim-build3.json`, compiler/build provenance, both launcher
descriptions, and the retained earlier smoke harness failure. Native and QEMU
Squares outputs have the same recorded SHA-256. The resource sample does not
demonstrate native wall-clock improvement. Host memory observations are aggregate,
not measured task limits or attribution to other processes. No performance or
RSS-enforcement guarantee is part of the review.

## Independent axes

Both reviewers were dispatched only after root confirmed isolated validation
completed and the coordinator verified its identity. Each received the full
candidate, requirements, standards pointers, evidence and limitations. They are
read-only: no candidate edits, builds, repeated tests, or process control.

### Standards

Reviewer: `/root/recovery_audit/native_standards`.
Outcome: **Passed**. Findings: **0**; worst severity: none. Applicable operational
validation established; no blocker within this scope. The following is the
independent report, lightly formatted for this durable record.

Standards read the immutable candidate with `git show`, checked the fixed
merge-base and complete diff, and independently matched the six captured source
hashes, including unchanged QEMU dependencies, to review-identity.json.
`git diff --check` passed. The reviewer modified no files, launched no builds,
reran no tests, and performed no process action.

The implementation meets applicable artifact-specific validation,
reproducibility, meaningful testing and review requirements in conaled AGENTS,
README, the shared review-loop procedure, and code-review/TDD guidance under the
accepted Nix exception:

1. **Narrow execution boundary.** `native_app_path.c:19–48` confines substitution
   to the current process's executable lookup with an explicit absolute path
   equal to AT_EXECFN. Other paths retain syscall behavior. Meaningful boundary
   tests cover truncation, no terminating NUL, errno preservation, zero size and
   null-pointer cases within the documented startup contract.
2. **Explicit inputs and isolated overlays.** `pinned_native_toolchain.py:21–67`
   verifies official executable, C source and shim hashes, relocated executable
   bytes and launcher contents. The native overlay is separate from QEMU.
   Reusing hashing/symlink helpers introduces no QEMU execution. Per-program
   launchers select distinct Lean/Lake identities; preparation clears inherited
   selectors and establishes workspace-local runtime locations.
3. **Observable-behavior tests.** `test_native_app_path.py:16–86` uses real
   dynamically linked calls in separate processes. Baseline/matched/mismatched/
   unset cases test substitution and preserved behavior. Actual parent/child
   launches, proof smokes and a real project module supplement these tests.
4. **Accurate recovery and limitations.** NATIVE.md supplies exact inputs,
   build/compiler provenance, reconstruction, relocation, cache distinctions
   and preservation requirements. It separates proof execution from acceptance,
   avoids unsupported speedup claims, and states invalid-pointer, RSS,
   additional-native-tool and trusted-runtime boundaries.

Standards independently verified the isolated-validation hash listed above.
All 17 recorded commands exited 0 in an initially clean isolated checkout;
the shim rebuild matches the pinned hash, actual parent/child versions and
relocated child path are correct, proof fixtures pass with equal output hashes,
and all six source hashes agree before/after. The complete Squares result is
transparently reused, not represented as another isolated compile; its native
and QEMU hash is
`133589a2adff7fcb278b1bc79fd1fd8f2bcf9315cfae28d6d801a5efa099ac4c`.

The completed resource sample (136.82 seconds wall, 144,730 major faults,
844,264 KiB maximum RSS) supports the recorded paging/I/O observation, not a
controlled native performance improvement. Documentation's narrower claim is
appropriate. The native cache command still needs its own result if selected;
prior QEMU retrieval is not represented as evidence that it ran.

This pass is solely the Standards axis for the operational adaptation. It does
not resolve ST-002/SP-VAL-001, approve formal candidate3279bac, establish a full
project run, or accept a chapter. All formal and incident-specific gates remain.

### Spec

Reviewer: `/root/recovery_audit/native_spec`.
Outcome: **Passed**. Findings: **0**; worst severity: none. The following is the
independent report, lightly formatted for this durable record.

| Requirement | Independent assessment |
| --- | --- |
| Narrow current-process lookup | Only `/proc/self/exe` and `/proc/<actual getpid()>/exe` are handled, guarded by explicit absolute CONALED_SELF_EXE exactly equal to AT_EXECFN. Near matches, unrelated PIDs, missing identity and mismatched identity fall through to the syscall. |
| Required readlink behavior | Within the declared valid-pointer domain, truncation, no terminating NUL, successful errno preservation, zero-size EINVAL and null-buffer EFAULT are retained. Ordinary symlinks/unrelated paths keep kernel behavior. Separate-process boundary evidence exercises these cases. |
| Lean/Lake execution identity | Official executable hashes are checked; native-overlay payloads are byte-identical. Distinct shell launchers select each payload's own identity. Captured validation establishes bare versions, Lake-child version and selected child path. |
| Checker environment | The outer helper clears inherited Lean/preload selectors. Per-program launchers preserve the fresh checker's subsequently established LEAN_PATH. Documented whole-checker invocation is direct, distinct from lake env. |
| Inputs and reproduction | Source, compiler/version, command, shim/executable hashes, wrappers and relocation are documented/evidenced. The captured candidate rebuild produces the expected shim hash. |
| Kernel/module evidence | Both proof-smoke routes pass and report no axioms for the two tested theorems. Complete native Squares output matches QEMU; isolated validation transparently reuses the existing result. |
| Performance/resource claims | Claims are confined to recorded runs. The sample establishes no native speedup. Aggregate host observations are not task limits, attribution or accurate RSS-limit enforcement. |
| Recovery/formal gates | The QEMU fallback, pins, local tracking and durability remain. Fresh, guarded, managed audit, regression, independent review and immediate final-verification gates stay separate. Partial runs are not combined. |

Spec independently inspected immutable candidate contents, merge-base and the
complete four-file scope and computed source hashes. All six files match the
review identity. The explicit specification hash above matches, read with
REQUIREMENTS and accepted amendments. The isolated validation hash also matches;
it records 17 zero outcomes, unchanged source hashes, relocated overlay/fixture,
and rebuilt shim
`8bb82334a2888e37a18b657a16f498cba239aaf3935bf24cc5b59728f6df5a18`.
Boundary observations agree with assertions and implementation, beyond a bare
pass flag. The completed native-smoke2 retains the earlier harness error and
binds the successful route to recorded execution inputs.

Spec retains these limits: the native cold-cache route needs its own outcome if
selected; arbitrary invalid non-null pointers and arbitrary symlink/relative/
deleted-executable semantics are outside the declared contract. No broader libc,
OS or compiler certification is implied. The sample's 136.82 seconds wall,
approximately 2.99 seconds user CPU, 35.04 seconds system CPU and 144,730 major
faults justify investigating paging/I/O but demonstrate neither native speedup
nor task-specific memory limits. A complete uploaded checkpoint must precede
a new formal attempt; this review does not claim that step occurred.

Spec performed read-only inspection, without edits, builds, tests, repeated
validation or process control. This passing Spec axis supplies no formal
candidate/chapter credit; all existing formal findings and gates remain open.

## Round 1 coordination result

Both independent axes passed the same immutable operational candidate with
zero findings. The coordinator preserves their separate assessments and does
not supply a third review. A final read-only byte comparison found all six live
delivered tooling files identical to the candidate Git objects, including the
unchanged QEMU helper and README. No correction or new candidate was required.

Operational review outcome: **Standards Passed; Spec Passed; no unresolved
findings** on base `c411e6c04b4001b80f5b0da812b6792ee9190861` and candidate
`e41336d46dffd7bddd42b242a7ea7484a6055e43`. Root owns final acceptance and the
required complete checkpoint/upload before a new formal validation attempt.
This record does not claim that upload or a later validation result.

## Acceptance boundary

Passing both operational axes would approve only this frozen execution adaptation.
Root must verify delivered files against that candidate and preserve the reviewed
route in an uploaded checkpoint before a new formal validation attempt, as the
ticket requires. Any obsolete owned-run transition needs its own actual outcome
and ownership-preserving control; historical process IDs grant no authority.

Formal ST-002 and SP-VAL-001 remain open. Fresh and separate guarded candidate
validation, exhaustive audits, managed ProofAudit prerequisite, regression,
independent formal evidence assessment and immediate final verification remain
required. Partial runs cannot be combined into a successful full validation.

## Round 2: concurrency documentation correction — prepared scope

This is a post-acceptance documentation correction in the same operational
review record, not a new formal chapter review. Root supplied the accepted
Round 1 operational tip as this correction's base; the original Round 1
scope, findings and evidence above remain historical and unchanged.

- Operational repository: `work-state/native-environment-review`.
- Supplied base and independently verified merge-base:
  `e41336d46dffd7bddd42b242a7ea7484a6055e43`.
- Candidate: `0afe0faa014512a0375bb158b6c8a56817075319`.
- Comparison: `git diff e41336d46dffd7bddd42b242a7ea7484a6055e43...0afe0faa014512a0375bb158b6c8a56817075319`.
- Commit: `0afe0fa docs: distinguish native compiler concurrency controls (#1033)`.
- Complete scope: `work-state/tooling/NATIVE.md`, 30 additions and 6 deletions;
  no exclusions, no runtime/helper/wrapper or formal-input change.
- Formal source remains `c988f183887896c00b09aaff9077a6ea7fb8d68f`, against its
  separate enclosing base `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.

Explicit requirements: `../specs/1033-thread-documentation-correction.md`,
SHA-256 `1e4414e2ba8718c4f095f6cd1e49597194a2d2a2ebf07503815d7bd3719b6db1`.
All six requirements apply: distinguish fresh process jobs, Lake's ordinary
compiler-job pool and Lean CLI internal workers; scope serialization accurately;
give supported selectors and override placement; preserve runtime/formal inputs
and historical observations; limit the explicit-j1 probe's claims; and obtain
both independent axes on this exact prose-only candidate. Existing user
exceptions, local tracking, durability and full formal gates remain in force.

The coordinator verified the immutable nonempty diff and evidence identities
below after root confirmed the source assessment was complete. Earlier runtime
validation is reused because the runtime/helper/compiler inputs are unchanged;
no compile or successful test is to be repeated for this prose correction.

| Evidence under `../validation/1033-native-environment/` | SHA-256 |
| --- | --- |
| thread-doc-review-identity.json | `c3da4164c9bb756e3fbd19c8b5fbd7b2bb850f4d671140ad107fbfd2514e2c93` |
| concurrency-and-mmap-assessment.md | `8f71ecd6e850ee0580fcb995c1e37cb85afd1b04b713539be5365d229dc2392b` |
| explicit-j1-firstorder-probe.json | `5d450d218500dc1eb1e34ed8f949186eee76292754bf2a94ea9a153f9daeb6bb` |

The source assessment is evidence, not an approval. Its pinned-source chain
supports the concurrency distinction and records loader/mmap limits. The
separate FirstOrder probe records one actual exit 0 and matching output bytes
under uncontrolled concurrent conditions; it supplies no causal speedup,
full-candidate success or chapter credit. The formal fresh4 run remains active
at preparation, with no formal acceptance inferred.

At dispatch, both independent Round 2 reports were pending. The coordinator
reused the existing `native_standards` and `native_spec` reviewers with this
exact scope, requirements, applicable conaled standards and all evidence. Both
worked read-only without active build-output inspection, builds, repeated
successful tests or process control. Their completed outcomes follow. No
original formal finding is disposed by this documentation review.

### Round 2 Standards

Reviewer: `/root/recovery_audit/native_standards`.
Outcome: **Passed**. Findings: **0**; worst severity: none. Applicable
documentation validation is established; no unresolved prior operational
Standards finding remains. The following is the independent report, lightly
formatted for this record.

The correction satisfies applicable documentation, evidence,
artifact-appropriate validation and review requirements:

- **Concurrency distinctions are precise.** Candidate NATIVE.md lines 83–87
  and 158–165 distinguish fresh-checker compiler processes, Lake's ordinary
  build-worker pool and the Lean CLI's internal worker setting. Serialization
  is confined to this project's ordinary Lake compiler jobs. The guide
  explicitly excludes a global OS-thread bound and arbitrary custom targets.
- **Instructions match the unchanged launcher.** Lines 167–172 place a
  deliberate `LEAN_NUM_THREADS` override after the helper's `--`, identify
  actual `lean -j1` / `lean --threads=1` arguments, and state that the current
  launcher and fresh4 inputs have not changed to propagate them.
- **Historical evidence remains scoped.** Lines 174–181 acknowledge the
  earlier overstatement without rewriting commands or results. The FirstOrder
  probe supports one successful explicit-selector invocation with matching
  bytes. Uncontrolled timing is not turned into a causal performance claim.
- **Formal boundaries remain intact.** Full validation and stable-input
  requirements are unchanged. The correction changes no runtime input and
  awards no formal-candidate or chapter acceptance.

No documented-standard violation or actionable heuristic finding remains.
The three distinct control names remove ambiguity that could otherwise imply
an unsupported internal-worker bound.

Standards independently verified the immutable diff, merge-base, Conventional
Commit, `git diff --check`, candidate documentation hash and all supplied
specification/evidence hashes. The candidate NATIVE.md SHA-256 is
`715806649f2debbab648b818eb0d3e0e0bfdf514e0d777c370f74949e44a1d4d`.

Source corroboration included pinned local Lean shell defaults and option
handling, emitted executable startup, Lake module-job scheduling, compiler
launch, synchronous child-output/wait ordering, and the frozen checker's
process-job limit. The saved C++ shell and IO sources match their report hashes
and corroborate the shell-selected task-manager count and blocking IO behavior.
Fresh web fetching of pinned C++ sources was unavailable; this did not trigger
a runtime test. For `object.cpp` environment-setting and scheduler details,
Standards explicitly reused the verified stable source assessment. That
source-derived conclusion is not a measurement of active compiler threads.

The FirstOrder record contains actual `-j1`, completed exit 0 and matching
output hashes. Unchanged Round 1's 17-command isolated runtime validation
remains applicable; no compile is required for this prose correction.

This Standards pass does not approve collector preparation, an mmap/runtime
change or formal candidate `c988f183887896c00b09aaff9077a6ea7fb8d68f`. It closes
no formal finding and establishes no fresh4 outcome. The reviewer made no
edits, builds, tests, active output/cache inspection or process-control action.

Final Standards disposition: **Passed**, zero findings, on base
`e41336d46dffd7bddd42b242a7ea7484a6055e43` and candidate
`0afe0faa014512a0375bb158b6c8a56817075319`.

### Round 2 Spec

Reviewer: `/root/recovery_audit/native_spec`.
Outcome: **Passed**. Findings: **0**; worst severity: none. This is the
independent documentation-spec assessment, lightly formatted for this record.

| Requirement | Independent assessment |
| --- | --- |
| 1. Three concurrency controls | Satisfied. The candidate separates fresh process jobs, Lake's ordinary build-worker pool and Lean CLI internal workers, explicitly stating the frozen launcher supplies no `-j`/`--threads`. |
| 2. Scoped Lake serialization | Satisfied. The claim covers this project's ordinary compiler jobs, whose standard job waits for its child, and excludes every OS thread/arbitrary custom targets. The supplied assessment supports that scope; Spec also inspected pinned module-job scheduling and `IO.Process.output`. |
| 3. Actual controls and placement | Satisfied. The guide gives `lean -j1` and `lean --threads=1`; pinned Shell source confirms the hardware-concurrency default and explicit option handler. The intended environment override is after the helper's `--`; propagating CLI flags to every invocation requires separately selected configuration. |
| 4. Preserve runtime/history | Satisfied. Only prose changes. Native helper, C source, boundary-test source and QEMU helper retain Round 1 hashes. Actual old commands/results are preserved rather than assigned a new worker count or outcome. |
| 5. Probe boundary | Satisfied. The guide describes one bounded successful FirstOrder compilation with explicit `-j1`, matching bytes and uncontrolled conditions, with no causal speedup claim. JSON records one completed exit 0 and matching hashes. Opening scope and retained formal gates prevent full-candidate/chapter credit. |
| 6. Independent review and validation reuse | Satisfied for Spec. The exact documentation candidate is reviewed and unchanged Round 1 runtime evidence reused. Separate Standards completion is the coordinator's responsibility; no compilation is needed for this prose-only correction. |

Spec independently verified base, merge-base and the one-file 30-addition,
6-deletion scope without exclusions. Candidate NATIVE.md hashes to
`715806649f2debbab648b818eb0d3e0e0bfdf514e0d777c370f74949e44a1d4d`, matching
thread-doc-review-identity.json. The explicit specification, source assessment,
probe and identity record all match the SHA-256 values recorded above.

Round 1 executable identity, shim boundaries, relocation, versions and proof
smokes remain applicable because runtime inputs are unchanged. The previous
"one Lean thread" characterization is superseded by this explicit correction;
the historical evidence itself remains intact.

This pass establishes corrected documentation's agreement with its specification
and evidence. It does not measure active worker counts, identify a performance
cause, validate an mmap adaptation or complete a formal gate. Spec made no
edits, builds, tests, active project output/cache inspection or process action.

Final Spec disposition: **Passed**, zero findings, on base
`e41336d46dffd7bddd42b242a7ea7484a6055e43` and candidate
`0afe0faa014512a0375bb158b6c8a56817075319`.

### Round 2 coordination result and delivery identity

Both independent axes passed the same immutable documentation candidate with
zero findings. The coordinator retained their separate reports and supplied no
third Standards/Spec review. No correction candidate was required.

The final read-only delivered-source comparison is
`../validation/1033-native-environment/thread-doc-delivered-match.json`,
SHA-256 `6821003bfd63452b65bbe5c09717ca7880653c17ed329e781a67638649d43ca7`.
All six delivered tooling files match the candidate Git objects. Compared with
the accepted base, only NATIVE.md differs. No compiler, test or real project
artifact/cache inspection was used for this comparison.

Operational documentation review: **Standards Passed; Spec Passed; zero
unresolved findings**, base `e41336d46dffd7bddd42b242a7ea7484a6055e43`, candidate
`0afe0faa014512a0375bb158b6c8a56817075319`. Root owns final operational acceptance
and checkpoint041 preservation. This record claims neither that checkpoint's
creation/upload nor a later formal result.

Formal candidate `c988f183887896c00b09aaff9077a6ea7fb8d68f`, its fixed enclosing
base, ST-002/SP-VAL-001 and every full validation/review/verification gate remain
separate and pending. The documentation pass supplies no chapter credit.

## Round 3 / #1035: separate native-j1 production configuration — prepared scope

This extends the same operational review record and independent axes. The
accepted Round 2 tip is the supplied base for the new two-file configuration;
earlier runtime and documentation analyses remain available for explicit reuse.
The mmap prototype is excluded from production and remains experiment evidence.

- Operational repository: `work-state/native-environment-review`.
- Base and independently verified merge-base:
  `0afe0faa014512a0375bb158b6c8a56817075319`.
- Candidate: `c1121c5b99e8714a0d91eab0db6bb60f7c650f2c`.
- Comparison: `git diff 0afe0faa014512a0375bb158b6c8a56817075319...c1121c5b99e8714a0d91eab0db6bb60f7c650f2c`.
- Commit: `c1121c5 feat: add isolated native Lean CLI worker selection (#1035)`.
- Complete source scope: two new files, 271 additions, no deletions:
  `work-state/tooling/pinned_native_j1_toolchain.py` (120 lines) and
  `work-state/tooling/NATIVE-J1.md` (151 lines).
- Existing native/QEMU helpers, shim, guides, overlays and all formal inputs
  remain unchanged. Prototype code, fixtures and validation records are
  evidence outside the production diff; no unrelated task change is included.

Full explicit requirements: `../specs/1035-native-j1-adoption.md`, SHA-256
`df548d34c151ce4c3aef89c95b6b53a619d494ccecea83fa86dd27ce70042389`.
The required behavior is a separate relocatable overlay using the unchanged
official Lean/Lake payloads and accepted readlink shim, an initial `-j1` only
for Lean, and the existing Lake pool setting. Selector clearing, private fresh
LEAN_PATH behavior, input pinning and changed-wrapper refusal must remain.
Later explicit CLI options may override the initial setting, whereas supported
acceptance commands pass no such override. The guide must preserve exact setup,
all three concurrency controls, measurement limits, fallback instructions and
every existing formal acceptance/checkpoint requirement. No mmap adoption,
global OS-thread bound, RSS enforcement, causal speedup or chapter credit is
authorized by this change.

### Completed captured-candidate validation supplied for Round 3

Root confirmed actual successful tool/runner completion before dispatch.
The coordinator independently verified candidate/merge-base/nonempty scope and
the following retained evidence identities:

| Evidence under `../validation/` | SHA-256 |
| --- | --- |
| 1035-native-j1-review-identity.json | `b36fa22203d6569b1493a0646c8c9adce5aa37283ed0f90acb24bc984c808d7f` |
| 1035-native-j1-validator-correction.json | `8a2e626189c0eb6f01fa8f24e929e3babaa231735f528e02353d8e6bfe66ee53` |
| 1035-native-j1-isolated-2/result.json | `70fd9da383f60ff3f9e19eab82fb0268c40ff81c99542ec0be900dc9c0771e1b` |

The identity record's pending fields describe capture time; the later isolated
result records `state: passed`, the exact candidate and 15 individual command
exits of 0, with no timeout. Validation ran in the separate
`native-j1-environment-validation-2` checkout. It checks generated wrapper argv,
pinned versions, direct and Lake-env kernel proofs/axiom reports, actual ordinary
Lake compiler selection, private LEAN_PATH plus `--run` literal arguments,
the original Squares output digest and before/after captured/protected inputs.
The two Init proof outputs are identical and their reported theorems have no
axioms. The Squares fixture is the retained original `import Lean` source from
3279bac, not a full check of the current formal candidate. Its output digest is
`133589a2adff7fcb278b1bc79fd1fd8f2bcf9315cfae28d6d801a5efa099ac4c`.

Attempt 1's failure remains preserved. A validator substring check mistook
`-j1` inside the overlay pathname for an option passed to Lake. This assertion
failed before any compiler invocation. The corrected validator parses the
final wrapper exec lines with `shlex` and compares exact argv vectors; it ran
the same untouched production candidate in a new checkout/evidence directory.
This is not represented as a production defect or erased failed attempt.

The earlier #1033 shim boundaries and official-payload checks are explicitly
reused with exact matching identities. Current validation exercises the new
helper/overlay routes, avoiding repeated unchanged runtime tests. Original
Squares timing observations remain uncontrolled and supply no causal or
whole-project performance guarantee. The production configuration excludes
the mmap interposer and its test-only failure library.

At dispatch, Standards and Spec were pending independent Round 3 reports. Each
received the full two-file candidate, specification, retained history and
completed evidence. Review was read-only: no source/runtime changes,
compiler/test reruns, active artifact inspection or process control. Formal
candidate c988f18 and its enclosing base remain unchanged. Fresh4 has an
unavailable handle, a saved 123-module prefix, no success record and unknown
terminal outcomes; neither success nor quiescence is inferred, and its prefix
cannot complete another run.

### Round 3 Standards

Reviewer: `/root/recovery_audit/native_standards`.
Outcome: **Passed**. Findings: **0**; worst severity: none. Applicable isolated
operational validation is established; there is no unresolved prior operational
Standards finding. The following is the independent report, lightly formatted.

**The runtime change is narrow and preserves established execution boundaries.**
In `pinned_native_j1_toolchain.py` lines 21–68, the new overlay has a separate
location, keeps exact official executable/readlink-shim pins, verifies copied
payloads and refuses unexpected wrapper contents. Direct comparison with the
unchanged native helper confirms that the operational differences are the
distinct overlay and an initial `-j1` in Lean's wrapper. Lake receives its
original argument vector.

Quoted `"$@"` retains caller argument boundaries. Later explicit compiler
options may override the initial setting, as documented. Environment
preparation retains selector clearing, fixed library/sysroot selection and
`LEAN_NUM_THREADS=1`; the generated wrapper preserves a private LEAN_PATH
subsequently established by the checker.

**Validation exercises the relevant executable boundaries.** Evidence covers
direct Lean, `lake env lean`, an actual ordinary Lake module build, private
import resolution and literal arguments following `--run`. These are behavioral
checks beyond wrapper-text inspection. Matching source/runtime identities
justify reusing the unchanged shim's earlier boundary validation.

**The guide preserves reproduction and acceptance requirements.** NATIVE-J1.md
supplies installation references, exact identities, separate concurrency
controls, relocation, fallbacks and the complete formal acceptance sequence.
Its measurement section agrees with completed probe records, limits causal
interpretation and reports higher RSS observations. The mmap prototype remains
experiment evidence and is absent from production wrappers.

No documented-standard violation or actionable heuristic finding remains.
**Heuristic judgment:** a separate helper is justified by the explicit
requirement to preserve accepted routes and historical inputs; common hashing
and symlink primitives remain shared.

Standards independently verified merge-base, full immutable diff, Conventional
Commit, `git diff --check`, specification hash, review identity, validator
correction and completed result hash. All eight captured source hashes match
the candidate. The isolated result has 15 completed commands, every exit 0
and no timeout. Selected completed logs confirm pinned versions, axiom-free
Init proof routes with identical outputs, the new ordinary Lake compiler path
and expected literal private-path/argument output.

Original Squares source matches immutable `3279bac:Squares.lean`; its retained
output digest is
`133589a2adff7fcb278b1bc79fd1fd8f2bcf9315cfae28d6d801a5efa099ac4c`.
Attempt 1 remains failed after `describe`, before compiler invocation. The
corrected validator compares parsed wrapper argv and matches its recorded
source hash. Attempt 2 uses the unchanged production candidate.

This pass is only the Standards axis for native-j1. It does not approve mmap,
collector preparation, formal candidate c988f18 or a chapter. ST-002 and
SP-VAL-001 remain open. Fresh4's terminal result/quiescence remain unknown;
its saved prefix gives no full-run credit. Root owns delivered-byte acceptance
and the complete uploaded checkpoint before a new formal attempt. Standards
performed no edits, runtime writes, builds, tests, active-output inspection or
process action.

Final Standards disposition: **Passed**, zero findings, base
`0afe0faa014512a0375bb158b6c8a56817075319`, candidate
`c1121c5b99e8714a0d91eab0db6bb60f7c650f2c`.

### Round 3 Spec

Reviewer: `/root/recovery_audit/native_spec`.
Outcome: **Passed**. Findings: **0**; worst severity: none. This is the
independent full-spec operational assessment, lightly formatted below.

| Requirement | Independent assessment |
| --- | --- |
| Separate configuration; preserve existing routes | Satisfied. A distinct `lean-4.35.0-native-j1` overlay leaves accepted native and QEMU helpers unchanged. Comparing against the accepted helper shows only the overlay, Lean-only initial argument and identifying text as substantive differences. |
| Unchanged official payloads and accepted shim | Satisfied. Lean/Lake, C source and shim identities stay pinned; relocated payloads match official executable identities. Validation records those exact inputs and unchanged protected inputs. |
| Lean receives `-j1`; Lake does not | Satisfied. Conditional wrapper construction inserts the argument only for Lean, before `"$@"`. Corrected exact argv checks establish no extra Lake option. Lake pool setting remains `LEAN_NUM_THREADS=1`. |
| Selector clearing and private LEAN_PATH | Satisfied. Accepted clearing/environment behavior is retained. Generated wrappers preserve later private LEAN_PATH; the isolated fixture imports through it and preserves literal `--run` arguments, including a space-containing and option-looking argument. |
| Relocation, input checks, changed-wrapper refusal | Satisfied. Paths derive from the adjacent pinned helper, and the isolated checkout constructs its own overlay. Source retains digest checks and refuses unexpected launcher contents/symlinks; the guide explains regeneration after relocation. |
| Explicit overrides and precise concurrency limits | Satisfied. Later explicit CLI options can override the initial setting; supported acceptance commands supply none. Fresh process jobs, Lake's ordinary pool and CLI workers remain distinct, with no every-thread/custom-target bound. |
| Exclude mmap adoption | Satisfied. Only the accepted executable-path shim is preloaded. No mmap component or experimental opt-in setting is introduced. The prototype remains historical evidence. |
| Reconstruction, versions and dependencies | Satisfied. Setup/usage, executable/shim identities, pinned versions and accepted installation references are supplied. Mathlib revision matches the immutable formal manifest; QEMU fallback remains. |
| Measurement interpretation | Satisfied. Completed control/advice timings, output hashes and RSS figures support the stated observations. The guide disclaims causal timing attribution, reduced memory, whole-project guarantees and increased safe process concurrency. The simpler selection is not represented as a general performance-cause finding. |
| Formal and durability gates | Satisfied. A new complete formal run, separate fresh/guarded evidence, preservation before repair, managed ProofAudit, regression, both formal axes and immediate final verification remain required. Operational acceptance and uploaded checkpoint precede the new attempt; partial attempts cannot combine. |

Spec verified both source identities against the immutable candidate and review
identity record:

| Source | SHA-256 |
| --- | --- |
| pinned_native_j1_toolchain.py | `575ea992adfa874e2f680b2c9e85120057f21a9e7ebbd8cb1005e1122845c1d5` |
| NATIVE-J1.md | `f80a441358bd37ad5f33348193868c6a2d7b22ca993158f43ef444b711edf7a9` |

The adoption specification and completed isolated result match the hashes
recorded above. Spec inspected the commands, selected raw logs and validator
source. Fifteen commands exited 0 without timeout on the captured candidate,
establishing exact wrappers, versions, both Lake selection routes, two
axiom-free proof paths with identical outputs, private imports/literal script
arguments, original Squares identity, and unchanged captured/protected inputs.
The original Squares source matches immutable 3279bac including `import Lean`;
it is a representative source check, not full formal-candidate acceptance.

The failed first validation and exact-argument correction remain preserved.
Its failure preceded compiler invocation and changed no production source.
The corrected validator hash matches its record. Unchanged #1033 shim boundary
and official-payload checks are reused with matching identities; the new
isolated route checks provide evidence for the added argument behavior.

Root must still compare delivered bytes immediately before operational
acceptance and complete checkpoint upload. This Spec pass supplies no formal
approval, fresh4 terminal result, success record or quiescence evidence. The
reviewer made no edits, builds, tests, active artifact/cache inspection or
process-control action.

Final Spec disposition: **Passed**, zero findings, base
`0afe0faa014512a0375bb158b6c8a56817075319`, candidate
`c1121c5b99e8714a0d91eab0db6bb60f7c650f2c`.

### Round 3 coordination result and delivered-source comparison

Both independent operational axes passed the same complete candidate with
zero findings. The coordinator retains their separate assessments and supplies
no third Standards/Spec review. No production correction candidate was needed.

The read-only delivered-source comparison is
`../validation/1035-native-j1-delivered-match.json`, SHA-256
`83dc9dc4e222302e64fd3f7fd8e8f0efbf7e1b221b3ebb9c95b49aa31073e262`.
All eight delivered tooling sources match the candidate Git objects. Exactly
the two intended files are added; every existing tooling file matches the base.
No runtime artifact, compiler or test was touched for that comparison.

Review outcome: **Standards Passed; Spec Passed; zero unresolved findings**, on
base `0afe0faa014512a0375bb158b6c8a56817075319` and candidate
`c1121c5b99e8714a0d91eab0db6bb60f7c650f2c`. Root owns final operational acceptance
and the uploaded complete checkpoint before a new full formal attempt. This
review record does not claim that acceptance, upload or new formal run occurred.

Formal candidate `c988f183887896c00b09aaff9077a6ea7fb8d68f`, its fixed base
`7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`, chapter order, ST-002/SP-VAL-001 and
all full validation/review/final-verification gates remain separate. The lost
fresh4 outcome stays unknown. No partial-run or operational check earns chapter
credit.

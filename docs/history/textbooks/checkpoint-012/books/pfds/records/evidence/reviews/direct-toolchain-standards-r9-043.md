# Direct/native toolchain — independent Standards review, r9-043

## Outcome

**Findings-present.** The complete 19-file operational candidate has one new,
unresolved **Medium** Standards finding, **DTS-003**, concerning selection of
the genuine Elan executable in the new regression-recovery command. The two
previous Standards findings remain **fixed with evidence**, at their original
Medium severities: **DTS-001** and **DTS-002**. No additional source finding or
evidence-access blocker was established.

Reviewer: `/root/lean_native_path_options`, assigned as the independent
Standards axis by `/root/direct_toolchain_validation_plan` within the existing
implementation/review loop. I authored none of the 19 files in this candidate.
My earlier investigation and review-coordination records are outside its source
scope. The earlier r7 Standards reviewer contributed to the new Elan recipe;
that contribution is why this appendix received a replacement independent
Standards assessment. Its completed r7 analysis remains applicable to the
unchanged 18-file implementation after the identity checks described below.

I inspected source, Git metadata, saved requirements, and retained evidence.
I ran no compiler, build, runtime test, regression suite, network retrieval,
protected-path probe, or process-control operation. I changed no candidate,
runtime, active gate input, or retained finding record. This report is my only
written artifact for the round.

This is an operational review. It does not establish a formal project build,
axiom audit, final stock candidate verification, chapter acceptance, or
completion of the PFDS book/thesis union. The independent Spec outcome is
separate and is neither supplied nor reranked here.

## Immutable scope and continuity

| Item | Reviewed identity |
| --- | --- |
| Fixed base and merge base | `76d77a107deb37c30e0b061c30b03a3f8c6aa12c` |
| Candidate | `ff3f709723e5c49e5ba40798abbed7d36141a6fb` |
| Retained ref | `refs/pfds-review/native-toolchain-r9-043` |
| Isolated checkout | `/workspace/scratch/b566cace4ed6/pfds/review-native-toolchain-043-r9` |
| Commit | `ff3f7097 docs(toolchain): preserve modes in real Elan recovery snapshot (#10000)` |
| Full diff | 19 files, 3456 insertions, no source exclusions within the manifest |
| Manifest | `session/validation/native-toolchain-candidate-r9-043.json` |
| Manifest SHA256 | `af74d3d1ab35c9a26dd1034bf223d2479232d6e82732c05ac72b701c7f0e09ec` |

The reviewed comparison is
`git diff 76d77a107deb37c30e0b061c30b03a3f8c6aa12c...ff3f709723e5c49e5ba40798abbed7d36141a6fb`.
I independently confirmed the exact HEAD, retained ref, merge base, nonempty
diff, complete path set, and clean isolated checkout. Every isolated and
delivered file matched the manifest's SHA256. Every committed mode matched
both the manifest and aggregate evidence.

Relative to approved r7 candidate
`af2c53dce68ebb122c81175312d6bb30df9aac05`, the sole change is the added
`session/environment/RECOVER-ELAN-REGRESSIONS.md`. All original 18 files retain
their exact bytes and modes. Relative to superseded r8 candidate
`d95518fde8cfc877da9d2bfc720ed4fd1f4698ba`, all 19 blobs are identical; only
`run-native-validation.py` and `test-native-validation.py` regain their
approved `100755` modes. The other 17 files are `100644`. The r8 snapshot was
superseded before axis review, and its genuine test evidence is retained
without turning the snapshot discrepancy into an approval.

The authored scope read and assessed is complete:

| Area | Files |
| --- | --- |
| Original profile and launcher | `session/environment/make-direct-toolchain-profile.py`; `session/environment/run-direct-toolchain.py` |
| Public compiler/Lake checks | `session/environment/test-direct-toolchain.py`; `session/environment/test-direct-lake-build.py` |
| Original operational handoff | `session/environment/README-direct-toolchain.md`; `session/validation/direct-validation-runner-notes.md` |
| Original validation controller and tests | `session/validation/run-direct-validation.py`; `session/validation/test-direct-validation.py` |
| Complete recovery and comparison | `session/environment/RECOVER-ENVIRONMENT.md`; `session/environment/environment-route-comparison-042.md` |
| Checkpoint entry point and restoration | `session/checkpoint.py` |
| Native implementation | `session/environment/native-own-exe.c`; `session/environment/run-native-toolchain.py` |
| Native public contract fixtures | `session/environment/test-native-own-exe.c`; `session/environment/test-native-own-exe.py`; `session/environment/native-readlink-fixture.c` |
| Native validation controller and tests | `session/validation/run-native-validation.py`; `session/validation/test-native-validation.py` |
| New Elan recovery appendix | `session/environment/RECOVER-ELAN-REGRESSIONS.md` |

Both controllers' complete common text and their complete differences were
read, including the native runtime binding, fixed/default candidates, explicit
focus override, and parser changes. No source region was omitted merely
because its earlier review passed. Relevant unchanged stock code includes
`scripts/test-check.py` and its actual bare `elan which lean` call.

Formal candidate changes, runtime binaries and caches, prior evidence,
tracker/status, review records, and provenance records are outside this authored
helper diff. They remain relevant context with their own obligations. This is
not an assertion that the whole workspace or formal workstream is accepted.

I read the full dispatch, the retained `session/reviews/direct-toolchain.md`,
and the complete r7 Standards report. Earlier incomplete rounds remain
incomplete; the complete r7 result does not retroactively approve them.

## Governing standards and saved requirements

Applicable guidance is the candidate's `AGENTS.md`, README development and
build/audit guidance, implementation skill, shared review-loop procedure,
code-review skill and heuristics, TDD guidance and its tests/mocking references,
and the applicable ADR and architectural-quality guidance already identified
in this loop. No separate root `CODING_STANDARDS.md` or `CONTRIBUTING.md`
contributes a conflicting rule. The same unchanged guidance supports retained
analysis of the original operational files.

The controlling rules are: match validation to the changed artifacts; preserve
the exact Lean/Lake/dependency inputs and actual compiler behavior; retain clean
immutable candidates and complete independent reviews; rely on successful
checks only for matching inputs and coverage; preserve failed and partial
evidence; and keep operational smoke tests distinct from formal acceptance.
The stock first fresh check and immediate final verification remain required
for mathematical acceptance. The source does not alter formal declarations,
so a new mathematical statement review is not an artifact gate for this diff.

I checked the current contents and hashes of all six saved requirements against
the exact manifest:

| Requirement | SHA256 |
| --- | --- |
| `session/requirements/REQUEST.md` | `b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499` |
| `session/requirements/REQUEST-union-v2.md` | `3336bed1154438b3683aeb5a1c63fee44e87aff190f5ff69e34705a780b9d22c` |
| `session/requirements/REQUEST-direct-toolchain-041.md` | `16845edec15c311e0cfd5ed5d4f5c4feb61e7ad96545653d5b872309d26464bc` |
| `session/environment/direct-toolchain-implementation-scope-041.md` | `05c125ee129eafc8f45f9367be16259c3239c7b3945c32f62effba1f1b4c922c` |
| `session/requirements/REQUEST-environment-handoff-042.md` | `200789123c60ae137967f881207194412eecea72ba2fc80247978075bd6a4602` |
| `session/requirements/REQUEST-native-toolchain-042.md` | `d76dc8dcf771a227779628de91e75c4b63a2898b95e7b30035de83537dae5195` |

The user's exceptions authorize local tracking/checkpoints and exact tooling
without Nix, and later prefer native execution over slow emulation. They do
not waive pins, source policy, proof auditing, clean candidate isolation,
independent review, final verification, chapter order, or durable handoff.
The existing public CLI seams are already authorized. No new permission or
GitHub operation is required for this assessment.

## Retained findings and regression assessment

### DTS-001 — Required fresh route and mode-bound verification

- Original severity: **Medium**.
- Original basis: documented README/ADR 0010 validation requirement.
- Disposition: **Fixed with round-2 review evidence; no regression in r9**.

Both controllers retain `full RUN_ID --fresh` and produce the unchanged stock
`./check.sh --candidate HEAD --fresh --jobs 1` command. Retained full evidence
binds the result to the actual fresh/incremental mode, exact full candidate,
dependency identities, clean input snapshots, terminal result, and saved log
and stock verification digest. The native controller additionally requires
`runtime: native`. Verify reads the retained mode and invokes stock
`./check.sh --verify-candidate HEAD` without adding fresh/jobs flags. The
parser refuses `--fresh` outside full mode. The recovery guide still directs
the new runtime's first full invocation through fresh mode.

The original eight sources are unchanged from their approved correction;
the native controller and its four public refusal tests are unchanged from
approved r7. Their exact matching evidence and the original r2 red/green
history remain applicable. Neither the new Elan appendix nor restoration of
two executable bits changes this contract. No actual formal full-pass result
is inferred from the controller tests.

### DTS-002 — Cold-recovery temporary-parent creation

- Original severity: **Medium**.
- Original basis: concrete recovery/fixture setup failure.
- Disposition: **Fixed with round-2 review evidence; no regression in r9**.

Both smoke helpers explicitly create `session/tools` before creating their
temporary projects. The native contract runner creates its owned fixture
directory with parents. Their bytes are unchanged. Earlier actual absent-parent
CLI/Lake tests and the r6 cold native Lake result still match these inputs.
The r6 evidence includes `lake_temporary_parent_absent: true` and genuine
compilation, linking, and output `42`.

The original failed r2 aggregate remains failed and retained. The separate
index-only reconciliation narrowly permits reuse of runtime checks whose
inputs did not depend on the repaired review index. It is not a clean-state
waiver for a formal gate. The recovery guide continues to warn against carrying
temporary `GIT_INDEX_FILE` into worktree construction.

## New finding

### DTS-003 — The regression command does not select the verified Elan first

- Severity: **Medium**.
- Status: **Unresolved on r9**.
- Type: operational robustness and validation-coverage judgment; this is not
  a new project Elan version pin or a claim that Lean's kernel is weakened.
- Candidate location: `session/environment/RECOVER-ELAN-REGRESSIONS.md:111–116`,
  specifically `PATH="$PATH:$PFDS_ELAN_PACKAGE"` at line 114.
- Related unchanged code: `scripts/test-check.py:372` invokes
  `subprocess.check_output(["elan", "which", "lean"], ...)`;
  `run-native-toolchain.py` prepends only the native profile's `bin` directory
  and then retains the incoming PATH order.

**Applicable standard.** `AGENTS.md` requires artifact-appropriate validation;
code-review section 3 permits relying on successful checks only where their
coverage and inputs match the candidate behavior. The operational handoff must
make its genuine selected tools reproducible through the documented public
interface. The concrete concern is the unresolved command-selection dependency,
not a stylistic preference about PATH construction.

**Evidence and consequence.** The appendix verifies and invokes an absolute
workspace Elan executable during setup, but its regression command appends
that package directory to ambient PATH. An earlier directory containing an
`elan` executable still wins the stock script's bare-command lookup. The native
profile has no Elan entry to override it. Thus even after successful verified
setup, the documented regression command may use a different or unsuitable
ambient Elan and fail to use the recovered interface. The appendix has no
preflight proving that its later bare lookup selects the recorded artifact.
This is an analytical consequence of command lookup and the inspected source;
I did not execute a synthetic substitute or the regression suite.

The r8 cold record's setup and `which lean` checks all invoke the package Elan
by absolute path. Its regression-command block received only `bash -n`.
Those genuine successful observations remain valid for their stated scope,
but they do not resolve the later PATH selection. The record explicitly says
the stock regression suites did not run, and this review preserves that limit.

**Remedy.** Put `"$PFDS_ELAN_PACKAGE"` before the ambient PATH in the documented
regression invocation, or otherwise explicitly bind the stock child's bare
Elan lookup to that verified executable. This package contains the real
`elan` entry and installer, not Lean/Lake proxies, so prepending it need not
displace the native profile's Lean/Lake commands. Validate the actual bare
selection and real `elan which lean` under the same native-launch environment,
including a pre-existing earlier PATH entry if necessary to establish the
ordering property. Do not edit the stock test, invent Elan output, alter
timeouts, or claim a complete regression-suite pass from that narrow check.
Freeze any correction as a new candidate and retain this r9 finding.

The Spec reviewer independently reported the same operational issue under its
own identifier. This Standards finding was independently identified before
that notification and is retained separately; no Spec severity or disposition
is imported into this report.

## Assessment of the remaining complete source scope

The original QEMU helpers remain a documented fallback. Their profile staging,
regular byte-identical compiler copies, quoted wrappers, receipt checks,
read-only description, and scoped environment match the retained review. The
new handoff does not reclassify emulation as the preferred native route.

The native adapter still delegates to the next `readlink` implementation first.
It preserves successful results and failures other than `ENOENT`. Fallback
requires an exact own-process executable-link spelling, nonempty absolute
per-exec marker equal to `AT_EXECFN`, canonical path, and readable regular ELF.
It preserves bounded-buffer/non-NUL semantics and does not add a raw-syscall
path or permission change. Resolver initialization and its reentry protection
remain intact. The source and guide clearly limit support to frozen direct
ELF execution and exclude scripts, direct-loader/descriptor execution, mutable
images, invalid pointers, signal-handler calls, other ABI/entry points, and
general procfs equivalence. A marker is explicitly not authentication.

The native profile still checks the three original executable digests, stages
construction before rename, refuses replacement, records compiler/source/library
identities, and verifies them on description. Intended compiler wrappers set
their own exact marker; unrelated child execution cannot reuse a mismatched
marker. Inherited preload entries retain precedence and order. Unexpected
Lean/Lake selectors are refused rather than silently substituting a compiler.

The contract tests exercise public readlink and actual launcher behavior with
independent expected paths, buffer sentinels, child/fork/constructor/concurrent
cases, and controlled downstream results. Their controlled success and
`EACCES`/`EPERM`/`EIO`/`ENOENT` cases are explicitly fixtures, with instrumentation
establishing the layer was reached. They are not purported observations of
protected host files. This unchanged test design remains consistent with the
TDD guidance's public behavior and explicit boundary substitutions.

The validation controllers preserve exclusive evidence creation, separate
nonblocking full/focus locks, exact clean heads and dependency pins, source and
runtime snapshots, real terminal status, and cancellation limited to their
owned child process group. The native focus override accepts only a full
lowercase 40-digit commit, still checks actual clean HEAD in the fixed focus
checkout, and cannot override full/verify. Before/after hashes retain their
documented frozen-input assumption; they are not asserted to be a hermetic
proof of every external condition.

The main recovery guide retains exact acquisition/dependency recipes, native
launch limits, private real project `.lake`/build directories, and separate
candidate records. Its checks reject project `.lake` and build symlinks. The
checkpoint generator's complete source is in scope; its archive/restore logic
is unchanged from the preserved predecessor apart from the previously reviewed
README/restore-success directions. A later actual checkpoint still requires
its own archive integrity and restoration result. The current report cannot
pre-approve that future action.

The comparison guide distinguishes authenticated Ubuntu package acquisition
from an unexecuted alternative runtime, and labels the limited measured native
timing observations and I/O inference without claiming a general speedup. It
does not substitute the supplied guide's other workstream or Library references
for this PFDS history.

The new appendix otherwise gives concrete official Elan provenance, refuses
existing package/state/archive locations, validates archive and executable
bytes, permits only the expected single regular tar member, and keeps state
inside the workspace. The supported `elan` symlink/argv-zero entry is backed
by the retained tagged upstream README and actual real CLI evidence. It does
not modify the active profile, project pins, stock tests, or timeouts. Its
distinction between ordinary audit fixture outputs and a fresh check's private
temporary outputs is explicit. DTS-003 is the remaining reproducibility gap.

## Validation applicability and evidence reuse

I independently checked these retained record hashes and read their relevant
contents. I did not rerun successful mechanical checks.

| Record | SHA256 |
| --- | --- |
| r9 aggregate | `a86be8c447403d0947e7542461471e47570b69e484e4464522c3a12661221ddc` |
| r8 actual appendix validation | `d8d99e2f557223af3f61c5ab39854ca696f4d4ef1d0fd5da4cd594e6296f766a` |
| r7 manifest | `257e31713ec28c4c12cafb7635ad14098f09d8bc765c79d541b7ff30d27ac593` |
| r7 artifact validation | `e142a541377e59027008d2299fc19dcb9b5a1613cc460409ffbf90c9ae3b8176` |
| r7 final delivery verification | `0359e0ef2cbf8da38d0382cfffa9efc84d4c02dc9e22e03f490bd442c466c206` |
| Complete r7 Standards report | `3b143b5b92f51efaa8aecfc86de2fa7a3316ce1cc320a490c81ffc2af064ca0e` |
| Main Elan setup record | `1241921bc37935dd4706cecd0d762afc830d7987dfe3d093a9e875e39fee1a16` |

The r7 aggregate reuses six individually named records for the r6 cold native
profile/CLI, Lake build and 18-case contract suite, plus the r2 reconciled
original-helper evidence and final delivery check. All six current record
hashes match that aggregate. The complete prior Standards assessment and
matching source identities support retaining those actual runtime outcomes.
The r7-specific four controller refusal tests, documentation syntax checks,
and two existing-state verification branches remain applicable to unchanged
source. This reuse is not a rerun or a broader formal acceptance claim.

For the new appendix, r8 retains three successful shell syntax checks and an
actual cold setup using its exact captured recipe with only `PFDS_ROOT`
substituted. The record contains the official download, exact size/digest
checks, safe extraction, real Elan version, custom-toolchain link, real
`which lean`, and selected Lean version through the unchanged native launcher.
The selected path resolves into the cold native profile. All commands recorded
for that limited setup returned zero. The cold setup used the separately
constructed profile, not a mutation of the active formal runtime.

The retained release JSON's official Linux asset agrees with the recipe:
4996571 archive bytes and SHA256
`42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63`.
The recipe and setup identify the 13452832-byte extracted executable with
SHA256 `e0f4b30b29c565625189744847dfef5f132b6322c5e452dbebfeae780c9749e5`.
Retained release metadata and tagged README hashes match the retrieval record.
The real output is `elan 4.2.4 (227caca13 2026-08-25)`; selected Lean reports
4.35.0 and the pinned full compiler commit. These are retained observations,
not output synthesized by the helpers or by this reviewer.

Reuse from r8 to r9 is valid for those observations: all 19 blobs and relevant
runtime inputs match; neither restored-mode validation controller is invoked
by the cold Elan setup. r7 supplies the approved original 18 modes. The
pre-review r8 discrepancy remains preserved instead of being rewritten away.
None of that reuse covers the unresolved bare-command selector identified in
DTS-003, nor does it establish a stock regression-suite result.

The current full 901 native run is a different workstream and is not needed
to settle this narrow operational source finding. I did not wait for, inspect
process state for, or alter it. Its eventual genuine terminal result and all
formal source/audit/review/final-verification gates remain separate.

## Final record

- **Standards outcome:** Findings-present.
- **Base and merge base:** `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
- **Candidate:** `ff3f709723e5c49e5ba40798abbed7d36141a6fb`.
- **Full scope:** 19 files, 3456 insertions.
- **Retained findings:** DTS-001 Medium, fixed with evidence; DTS-002 Medium,
  fixed with evidence; neither regressed.
- **New findings:** 1, DTS-003 Medium.
- **Unresolved findings:** 1.
- **Worst unresolved severity:** Medium.
- **Evidence-access blockers:** 0.
- **Validation limitation:** Actual setup/selection-by-absolute-path succeeded;
  the documented bare-Elan selection remains unresolved. Stock regression
  suites and formal full/chapter acceptance are not established by this review.

This report is complete and frozen for r9-043. Any correction requires a new
immutable candidate and reassessment of DTS-003 while retaining the existing
finding history and exact-input evidence.

# Direct toolchain helpers — Spec review, round 1

**Outcome: Findings-present.** Two unresolved findings: **DTP-001 (High)** and
**DTP-002 (Medium)**. The recorded artifact checks pass for their stated
coverage; they do not resolve these source-level orchestration and recovery
defects. This report grants no formal candidate or chapter acceptance.

Reviewer: `/root/lean_native_path_options/spec_direct_toolchain_r1`.
Review date: 2026-11-03. This is the independent Spec axis in the existing
implementation loop, not another implementation or review loop.

## Immutable scope

| Item | Identity |
|---|---|
| Base | `76d77a107deb37c30e0b061c30b03a3f8c6aa12c` |
| Candidate | `f010b5d0fdbef9c9f007c56531c326e738557f9d` |
| Merge base | `76d77a107deb37c30e0b061c30b03a3f8c6aa12c` |
| Isolated checkout | `/workspace/scratch/b566cace4ed6/pfds/review-direct-toolchain-041` |
| Retained base ref | `refs/pfds-review/direct-toolchain-base-041` |
| Retained candidate ref | `refs/pfds-review/direct-toolchain-r1-041` |
| Commit list | `f010b5d chore(toolchain): restore exact Lean and Lake without Nix` |

I independently resolved the refs, confirmed the merge base, inspected the
nonempty three-dot diff, and observed the isolated checkout at the candidate
with an empty Git status. The comparison was:

```text
git diff 76d77a107deb37c30e0b061c30b03a3f8c6aa12c...f010b5d0fdbef9c9f007c56531c326e738557f9d
```

All eight added files were reviewed in full:

- `session/environment/README-direct-toolchain.md`
- `session/environment/make-direct-toolchain-profile.py`
- `session/environment/run-direct-toolchain.py`
- `session/environment/test-direct-toolchain.py`
- `session/environment/test-direct-lake-build.py`
- `session/validation/direct-validation-runner-notes.md`
- `session/validation/run-direct-validation.py`
- `session/validation/test-direct-validation.py`

Formal candidate sources, prior evidence, runtime distributions/caches,
tracker/status files and review/provenance records are excluded from this
authored-helper diff. Their separate requirements remain. The review did not
inspect or accept the PFDS theorem statements as new formal work.

## Requirements used

The full operational requirements were read from the preserved session files
outside the isolated source diff. The user permits development without Nix
while retaining exact compiler/dependency pins, genuine checks, isolated
candidate validation, reviews, final verification and durable local recovery.
The implementation scope requires reproducible profile/launcher helpers,
public-interface smoke checks, and recorded validation through the stock
project command. It explicitly excludes formal acceptance by smoke tests.

| Requirement file | SHA256 read for this review |
|---|---|
| `session/requirements/REQUEST-direct-toolchain-041.md` | `16845edec15c311e0cfd5ed5d4f5c4feb61e7ad96545653d5b872309d26464bc` |
| `session/environment/direct-toolchain-implementation-scope-041.md` | `05c125ee129eafc8f45f9367be16259c3239c7b3945c32f62effba1f1b4c922c` |
| `session/requirements/REQUEST.md` | `b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499` |
| `session/requirements/REQUEST-union-v2.md` | `3336bed1154438b3683aeb5a1c63fee44e87aff190f5ff69e34705a780b9d22c` |

I also read candidate `AGENTS.md`, the environment/build/audit sections of
`README.md`, `.agents/skills/code-review/SKILL.md`, and
`docs/agents/review-loop.md`. Related unchanged code inspected included
`check.sh`, the candidate/record/compiler/full-check paths in
`scripts/check.py`, and the unchanged `lake-manifest.json`. The user exception
overrides Nix invocation only; it supplies no exception to the fresh-check
rule in the candidate README.

## Findings

### DTP-001 — The validation runner excludes the required fresh full-check path

**Severity: High. Status: Unresolved.**

**Requirement.** `REQUEST-direct-toolchain-041.md` preserves all build and
verification requirements. Candidate `README.md:204` requires a fresh project
rebuild after changing build tooling, toolchain, or dependency configuration.
`docs/agents/review-loop.md` requires the fresh candidate check where README
requires it. This change introduces a new compiler execution profile and
validation tooling. The implementer confirmed through the coordinator that
there is no saved exemption and no already-established alternative fresh
recording route for this transition.

**Candidate evidence.** `session/validation/run-direct-validation.py:244`
constructs the full command as `./check.sh --candidate HEAD` with no fresh
option. The CLI at line 352 exposes only the three mode choices, run ID and
full-record reference. At line 150, `validate_stock_record` accepts only
`mode == "incremental"`; `full_evidence` at line 173 also requires the exact
incremental command. A genuine fresh success record would therefore be
rejected by the helper's subsequent verification path. The handoff note at
`session/validation/direct-validation-runner-notes.md:42` documents only this
incremental full mode.

**Consequence.** The planned full-run/verification workflow cannot record and
retain the required first fresh validation under the new runtime. Following
the current documented runner commands gives incremental evidence even when
the governing acceptance requirements call for a cache-independent project
rebuild. The runner's `acceptance: false` field correctly avoids an automatic
acceptance claim, but does not make this missing gate disappear.

**Required correction.** Provide an explicit full fresh route and preserve
the exact command and actual stock record mode in its evidence. Bind final
verification to the successful recorded mode. Invoke the stock verifier as
`./check.sh --verify-candidate HEAD` without `--fresh` or `--jobs`, as required
by the stock interface. Record that the first full check after this runtime
transition uses fresh mode with the existing serial/resource policy. Preserve
historical incremental evidence without relabeling it. Update the handoff
instructions and relevant public refusal/argument validation checks for the
new route. The actual formal full gate remains a separate subsequent task.

### DTP-002 — Smoke tests require an undeclared transient directory after recovery

**Severity: Medium. Status: Unresolved.**

**Requirement.** The original request requires recovery without the previous
workspace or chat. The operational scope expressly makes the profile and
public smoke checks reproducible while excluding downloaded/reproducible
runtime material. A restored workspace need not contain the transient
`session/tools` directory. The implementer also confirmed that cold recovery
omits this directory.

**Candidate evidence.** `session/environment/test-direct-toolchain.py:42`
passes `root / "session/tools"` directly as `TemporaryDirectory`'s parent.
`session/environment/test-direct-lake-build.py:30` does the same with
`mkdtemp`. Neither creates that parent first. The documented profile creation
and environment launcher create the toolchain profile and runtime-cache
directories, not `session/tools`.

**Consequence.** Starting from recovered authored files and correctly restored
official distributions, either public smoke test can fail with a missing
temporary-parent directory before it reaches a compiler or Lake probe. The
retained passing tests ran in the existing workspace, where earlier download
and investigation work had already created that directory; they do not cover
the cold-recovery precondition.

**Required correction.** Create the workspace-local temporary parent before
allocating each test project, or use a documented existing workspace-local
parent whose creation the test ensures. Preserve the current cleanup and
failure-evidence behavior. Validate that the public test path reaches its
genuine probes with the transient parent initially absent; no substitute
compiler output or fabricated successful formal evidence is appropriate.

## Requirement coverage and semantic assessment

The profile generator preserves the original distribution. It copies the
three wrapped executables to regular files, compares copy hashes, quotes the
emulator/program paths, and uses a shell `exec` with the original argument
vector. Other release files remain references to the original installation.
The environment launcher compares recorded executable identities, scopes the
required paths and thread setting to the child, and uses `execvpe` rather than
rewriting compiler output or success status. The documentation requires
official archive/package digest verification before extraction; the generator
treats that as a precondition rather than independently reauthenticating a
distribution. No contrary source behavior was found in the reviewed scope.

The public CLI tests check actual expected Lean and Lake outputs, valid
theorem acceptance with no axioms, and a genuine type-mismatch rejection.
The Lake test checks the selected compiler and a compilation/link/execution
path producing `42`. These are useful operational checks with appropriately
limited claims. DTP-002 concerns their recovery setup, not the validity of the
already observed successful runs.

The validation runner invokes the unchanged stock check and does not skip its
source policy, coverage, compiler-version checks, build or axiom audit. It
pins the intended prerequisite and focused candidate SHAs and manifest;
requires clean matching dependency revisions; records source/controller and
environment identities before and after execution; and refuses input changes.
Its fresh-mode restriction is the exception described in DTP-001.

New evidence paths are created exclusively, terminal results are distinguished
from interrupted/unknown outcomes, and successful full evidence is tied to its
log digest and the saved/live stock verification bytes. Verify mode rejects
unfinished evidence and changed inputs. Every record remains
`acceptance: false`. Separate nonblocking locks cover full/verify and focused
jobs, and normal cancellation targets the owned process group. These controls
remain subject to the explicitly retained frozen-input/no-conflicting-writer
discipline; they are not a claim of hermetic validation or protection against
hard interruption followed by unmanaged surviving processes.

No additional Spec defect was identified in the eight-file scope. No formal
source changes or weakened proof logic were present in this candidate.

## Validation evidence and limitations

I inspected and reused the following completed evidence, without rerunning
tests, compilers, cache commands or builds:

| Evidence | Result and scope |
|---|---|
| `session/validation/direct-toolchain-candidate-validation-r1-041.json` | Candidate `f010b5d…`; all three artifact test commands exit 0; snapshot/delivered source match recorded; clean snapshot. |
| `session/validation/direct-toolchain-candidate-cli-r1-041.json` | Exact Lean 4.35.0 and bundled Lake 5.0.0-src+eb6cafb; valid theorem accepted/no axioms; false theorem rejected with type mismatch. |
| `session/validation/direct-toolchain-candidate-lake-r1-041.json` | Lake selects the exact compiler, compiles and links the tiny native executable, and its actual execution prints `42`. |
| `session/validation/direct-cache-bootstrap-041.json` and `.log` | Cache executable bootstrap completed with exit 0. |
| `session/validation/direct-cache-get-041.json` and `.log` | Ordinary pinned cache retrieval completed with exit 0; retained parent evidence records 9,031 files. |
| `session/environment/direct-dependencies-after-cache-041.json` | All nine actual revisions equal manifest pins, all source checkouts clean. |

The aggregate artifact record has SHA256
`f2266f8d4cc2340a34cdd3309830ebd542e8dc3470e5f938fed573b8995f4e01`.
The CLI and Lake detail records have SHA256
`e8e07998319c3e72f50f648b57aec5bd4919a6753e586e9f692d66e5083ad9d3`
and `6517e33e61aed56beaf701590803e3ed1e6e262a604c5332a2b913c3efebc300`.
The post-cache dependency record has SHA256
`12054d8a6fd75348ccba9d454c3807a6268d0f6bc29375b2dd80b2f22fd212f8`.

The initial scope manifest's pending-validation text is historical; the later
exact-candidate aggregate records completion of the artifact checks. The
coordinator separately recomputed all eight snapshot and delivered-file
hashes against that manifest and found them matching. No proof/chapter
acceptance follows from this operational evidence, and no full/focused formal
candidate run was claimed to have completed under these helpers.

## Final disposition

**Base:** `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
**Candidate:** `f010b5d0fdbef9c9f007c56531c326e738557f9d`.
**Spec outcome:** Findings-present.
**Unresolved findings:** 2; worst severity High (DTP-001).
**Validation status:** recorded artifact checks passed within their stated
coverage; cold recovery and fresh-mode orchestration corrections remain.

Keep DTP-001 and DTP-002 in the retained finding record across correction
rounds. Re-review the complete corrected candidate against the same base;
reuse unaffected evidence only where the relevant inputs still match.

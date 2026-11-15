# Operational toolchain — independent Spec continuation, round 9 (043)

**Outcome: Findings-present.** One new Medium finding, `DTP-003`, remains
unresolved: the checker-suite recipe appends the verified Elan package to
ambient PATH, so the stock test's bare `elan` lookup can select an earlier
installation instead. DTP-001 (High) and DTP-002 (Medium) remain fixed with
their original closure evidence. No regression was found in the unchanged
18-file implementation.

The supplied artifact checks genuinely succeeded within their recorded scope.
They validate cold Elan acquisition/linking and selected Lean execution through
explicit paths, and syntax-check the suite recipes. They do not validate which
Elan the suite's bare-name lookup selects in an inherited environment, and no
stock regression suite is claimed to have run. This report supplies no formal
candidate, chapter, or whole-union acceptance.

## Role, independence, and review boundary

Reviewer: `/root/chapter02_continuation_plan`, 2026-11-03. Coordinator:
`/root/direct_toolchain_validation_plan`, continuing the existing operational
loop in `session/reviews/direct-toolchain.md`.

I confirmed before dispatch that I authored neither
`session/environment/RECOVER-ELAN-REGRESSIONS.md` nor its Elan command recipe.
My prior authored outputs are independent review reports, outside this
implementation scope. I read the full dispatch and retained finding record,
all six saved requirement/scope files, the complete new appendix, relevant
unchanged interfaces, and the recorded validation/provenance. I retained my
complete round 7 analysis of the other 18 files only after independently
matching their bytes and modes and the relevant guidance and evidence.

I performed only read-only file, hash and Git inspection. I ran no compiler,
build, test, audit, verifier, network request, protected-path probe, process
control, or runtime/profile setup. I did not modify a source, controller,
dependency, cache, tracker, shared finding record or earlier report, and did
not spawn another agent or review loop. This assigned report is my only write.
The separate full901 run was not inspected or controlled.

All paths below are relative to `/workspace/scratch/b566cace4ed6/pfds` unless
explicitly identified as paths inside the candidate checkout.

## Immutable candidate and complete scope

| Item | Independently checked identity |
| --- | --- |
| Base and merge base | `76d77a107deb37c30e0b061c30b03a3f8c6aa12c` |
| Candidate / isolated HEAD / retained ref | `ff3f709723e5c49e5ba40798abbed7d36141a6fb` |
| Ref | `refs/pfds-review/native-toolchain-r9-043` |
| Isolated checkout | `/workspace/scratch/b566cace4ed6/pfds/review-native-toolchain-043-r9` |
| Commit | `ff3f709 docs(toolchain): preserve modes in real Elan recovery snapshot (#10000)` |
| Complete three-dot diff | 19 files, 3,456 insertions; one snapshot commit |
| Isolated cleanliness | Empty `git status --porcelain=v1 --untracked-files=all` |
| Approved predecessor for analysis reuse | `af2c53dce68ebb122c81175312d6bb30df9aac05` |
| Superseded round 8 snapshot | `d95518fde8cfc877da9d2bfc720ed4fd1f4698ba` |

The full comparison is
`git diff 76d77a107deb37c30e0b061c30b03a3f8c6aa12c...ff3f709723e5c49e5ba40798abbed7d36141a6fb`.
The file set exactly equals the manifest. All 19 committed, isolated and
delivered content hashes and executable modes match it. All original 18 blobs
and Git modes match approved round 7. The exact r7-to-r9 endpoint difference
adds only `session/environment/RECOVER-ELAN-REGRESSIONS.md`, mode 100644,
SHA256 `b76abf471a5546faa191dd9d7dbf7639341b0028457a01c36494f54bd108d769`.

The reviewed scope is the complete original eight direct-toolchain helpers and
documentation files; full recovery and route-comparison documents; checkpoint
generator; native metadata adapter and launcher; three native contract-test
files; native validation controller and refusal tests; and the new Elan
appendix. The manifest retains the exact 19-path enumeration and hashes.
Formal sources, historical evidence, requirements, runtime binaries/caches,
trackers/status and reviews/provenance remain excluded from the authored-helper
diff and retain their separate obligations.

| Binding record | Checked SHA256 |
| --- | --- |
| `session/reviews/direct-toolchain-dispatch-r9-043.md` | `2e47bd80da2e7f52faefa88cc6f18c23ce1623b2a73b8f941e1e21eb0b7574a1` |
| `session/validation/native-toolchain-candidate-r9-043.json` | `af74d3d1ab35c9a26dd1034bf223d2479232d6e82732c05ac72b701c7f0e09ec` |
| `session/validation/native-toolchain-candidate-validation-r9-043.json` | `a86be8c447403d0947e7542461471e47570b69e484e4464522c3a12661221ddc` |
| `session/validation/native-toolchain-coordinator-dispatch-r9-043.json` | `d4ac3310ba40cf5a93d8b4a352fbbafacdc9c14a4e460e827210c16726c3549f` |

These independent identity checks support review and scoped evidence reuse;
they are not a mechanical execution test or formal stock verification.

## Requirements and applicable guidance

All six saved requirement/scope hashes match the manifest and the versions
used for round 7:

| File under `session/` | SHA256 |
| --- | --- |
| `requirements/REQUEST.md` | `b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499` |
| `requirements/REQUEST-union-v2.md` | `3336bed1154438b3683aeb5a1c63fee44e87aff190f5ff69e34705a780b9d22c` |
| `requirements/REQUEST-direct-toolchain-041.md` | `16845edec15c311e0cfd5ed5d4f5c4feb61e7ad96545653d5b872309d26464bc` |
| `environment/direct-toolchain-implementation-scope-041.md` | `05c125ee129eafc8f45f9367be16259c3239c7b3945c32f62effba1f1b4c922c` |
| `requirements/REQUEST-environment-handoff-042.md` | `200789123c60ae137967f881207194412eecea72ba2fc80247978075bd6a4602` |
| `requirements/REQUEST-native-toolchain-042.md` | `d76dc8dcf771a227779628de91e75c4b63a2898b95e7b30035de83537dae5195` |

The original request and union clarification preserve chapter order, source
coverage, local tracking and immediately delivered durable checkpoints. The
Nix exception changes the launcher requirement only. Exact Lean/Lake/dependency
identity, genuine compiler behavior, frozen isolated checks, source policy,
audits, both review axes and final verification remain required. The handoff
request requires a self-contained reproducible recovery procedure, with actual
observed behavior distinguished from alternatives and unfinished work. The
native request preserves historical outcomes and treats runtime transitions
as distinct runs.

I read the current AGENTS, implement and code-review skills, review heuristics,
TDD guidance, README development/build/audit section and shared review procedure.
Their relevant pinned files match round 7. Architectural/domain guidance,
language direction, glossary and ADR index also match the earlier reviewed
versions. The existing authorized public toolchain seams and the new real-Elan
selection interface support the applicable artifact checks; no additional
approval request or private test seam is introduced. User exceptions for Nix
and local tracking continue to override the repository defaults.

The complete prior Spec report is
`session/reviews/direct-toolchain-spec-r7-042.md`, checked SHA256
`c7df56778cba429b9d2c8c67e5a5f1e52f35e6a106a9ac36a2ecb0f89ac81b04`.
I read it in full. The retained Standards r7 report has checked SHA256
`3b143b5b92f51efaa8aecfc86de2fa7a3316ce1cc320a490c81ffc2af064ca0e`;
that axis's findings and severities remain separate. No incomplete or
superseded earlier round is turned into approval.

## Whole-task assessment and retained dispositions

The following assesses all 19 files, using the independently matched round 7
analysis and evidence for unchanged behavior and inspecting the new interface
connections directly.

| Scope | Current Spec assessment |
| --- | --- |
| Original direct profile/launcher, public Lean and Lake tests, direct controller/refusal tests and notes | All eight files retain approved round 2/round 7 bytes and modes. Exact release identities, genuine valid/false proof checks, Lake compilation/link/execution, mode-bound stock verification, owned evidence paths and resource controls are unchanged. The appendix does not replace or alter them. |
| Native adapter and profile launcher | Same pinned Lean/Lake/leanir copies, per-exec marker, delegated-readlink-first contract, limited missing-own-link fallback, frozen canonical ELF requirement, profile identity checks and explicit limits. Same clean-selector refusal, inherited preload ordering, one-thread/cache settings, and child-local environment. Elan adds a separate version-manager interface; no native-profile or active-controller mutation is part of its recipe. |
| Three native contract-test files | Same public/owned fixture coverage and same 18-case evidence, including buffer/delegation boundaries, inactive/stale markers, child execution, concurrency, cwd/argv independence and inherited layer preservation. Nothing in the appendix broadens the metadata adapter to musl installer behavior or general procfs emulation. |
| Native validation controller and its tests | Same full/fresh/verify machinery and exact full901 binding. Focus-only explicit 40-hex candidate selection remains separate. Matching input/record/log checks, acceptance false, terminal-result requirements and refusal behavior are unchanged. Restored executable modes match the approved source; no controller is invoked by the cold Elan setup. |
| Main recovery runbook and route comparison | Same official release acquisition and hashes, native and QEMU routes, nine pinned dependencies, isolated output ownership, relocatability limitations, honest alternative/performance comparisons, fresh-check requirement, lost-run handling and formal/source availability boundaries. The new appendix's setup prerequisites correctly refer back to this runbook. Its suite PATH selection has the single new defect below. |
| Complete checkpoint generator | Same reviewed generator and README/restore-pointer task delta. The appendix is additional session documentation. Checkpoint generation, restore validation, final delivered identity and immediate upload remain root-owned actions; this review does not assert that a new archive has been created or tested. |
| Elan appendix | Correct bounded need, official pinned acquisition, real argv0 CLI entrypoint, workspace-local state and link, relocation refusal, selected Lean identity checks, and explicit separation between setup and stock-suite/full/audit acceptance. The actual checker recipe does not ensure selection of that verified Elan. |

### DTP-001 — High — Fixed with review evidence; no regression

The original fresh-full route and mode-bound verification correction remain
unchanged. The native controller still adds `--fresh --jobs 1` only to the
full stock check as appropriate, retains the actual recorded mode, and invokes
stock verify without fresh/jobs flags. Focus cannot change the fixed full or
verify candidate. Both recovery paths retain the required fresh validation
after a tooling/runtime transition. The appendix specifically warns that a
fresh success record does not populate ordinary project outputs or replace
the other suites. No successful formal record is synthesized or copied.

The original r2 closure and the matching r6/r7 controller/artifact evidence
remain applicable. The new document does not reopen this High finding.

### DTP-002 — Medium — Fixed with review evidence; no regression

Both unchanged smoke tests still create their workspace-local temporary parent.
The original absent-parent r2 evidence and matching cold-profile/Lake r6 evidence
remain applicable. The new Elan creation recipe creates its download parent,
refuses existing package/state/archive paths (including dangling symlinks), and
relies on the explicitly required pre-existing native profile. It does not add
an undeclared dependency on an excluded `session/tools` directory to the
published recovery recipe. No regression of this finding was found.

DTS-001 and DTS-002 retain their historical Medium severities and r2/r7 fixed
dispositions in the separate Standards record. This Spec report does not close
or rerank that axis's findings.

## New finding

### DTP-003 — Medium — Unresolved: actual checker recipe can bypass the verified Elan

**Requirements.** `REQUEST-environment-handoff-042.md` requires self-contained,
reproducible takeover using the current verified tooling and clear observed
behavior. The direct-toolchain scope requires genuine public interfaces and
recorded input identity. The new appendix itself chooses and verifies the
official Elan 4.2.4 executable, describes its supported CLI entrypoint, and
intends the stock version-mismatch fixture to use that entrypoint without
changing the test or compiler (`RECOVER-ELAN-REGRESSIONS.md:3–11`, 15–41,
and 109–123).

**Candidate locations and mechanism.** The checker-suite command at
`session/environment/RECOVER-ELAN-REGRESSIONS.md:113–116` assigns
`PATH="$PATH:$PFDS_ELAN_PACKAGE"`, placing the verified package last.
The unchanged native launcher prepends only its native profile's bin to this
inherited PATH (`session/environment/run-native-toolchain.py:138`, 174–182).
The unchanged stock version-mismatch test uses
`subprocess.check_output(["elan", "which", "lean"], ...)` at
`scripts/test-check.py:372`, so its Elan executable is chosen by ordinary PATH
search, not by the absolute path used in the setup checks.

**Concrete consequence.** On a restored host that already has an `elan` in an
earlier PATH directory, that installation wins. For example, an existing
`/usr/bin/elan` remains selected when the inherited PATH contains `/usr/bin`
and the recipe appends the new package directory. A clean Bash launch does not
remove ordinary installed executables. The command therefore need not use the
4.2.4 binary whose archive, argv0 behavior and local setup were just verified.
A compatible pre-existing Elan may happen to work, but its identity and host
behavior are not established by the appendix's captured checks; an incompatible
one can fail before the intended version-mismatch assertion. I am not claiming
that this failure occurred on the current host. The selection dependency is
visible directly in the recipe and stock caller.

The supplied cold evidence uses `"$PFDS_ELAN_PACKAGE/elan"` explicitly for
version/link/which, then invokes the selected Lean path explicitly through the
native launcher. The suite block itself was only syntax checked. Those results
do not exercise or bind its ambient bare-name Elan lookup, so they cannot
resolve this interface discrepancy.

**Required correction.** Put the verified package directory ahead of ambient
PATH in the checker suite's child environment, or otherwise explicitly bind
the unchanged stock test's Elan lookup to the verified executable. Prepending
is a small appropriate fix: this package contains no Lean/Lake proxies, and
the native launcher continues to supply its own compiler bin first. Preserve
the child-local `ELAN_HOME` and `ELAN_TOOLCHAIN` settings and the stock scripts,
timeouts, pins and actual evidence requirements.

Retain applicable evidence that, under the same documented child environment,
the effective Elan executable resolves to the verified package and its genuine
`which lean` result resolves to the pinned native wrapper. This correction can
be assessed through the existing public selection/version interface without
claiming or requiring a successful full stock regression suite merely to
validate the appendix. The suites themselves keep their separate remaining
obligations. Return the corrected immutable candidate through this same loop;
this finding is not closed by a proposed fix.

The actionable finding was sent to the coordinator before report freeze.

## Provenance, cold reconstruction and validation meaning

The new appendix records official Elan release 4.2.4, a 4,996,571-byte archive
with SHA256
`42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63`,
and a 13,452,832-byte `elan-init` executable with SHA256
`e0f4b30b29c565625189744847dfef5f132b6322c5e452dbebfeae780c9749e5`.
I checked the retained official release metadata and tagged README against
their retrieval hashes. The release API names the exact archive URL, size
and matching digest. The README explicitly documents that `elan-init` is also
the real CLI and demonstrates the `elan` symlink entrypoint. This supports the
documented entrypoint choice without fabricating version-manager output.

| Retained provenance | Checked SHA256 |
| --- | --- |
| `session/environment/elan-4.2.4-provenance/release.json` | `6aa4607308cfa7b576a317ad93bb56d84196e18eae665cf4e92058b3eae37f57` |
| Tagged upstream `README.md` in that directory | `6778277cc096b30fbd7132ac420a85184a39a7f5b2b863b1841efee13de84d44` |
| `retrieval.json` in that directory | `0f33d41da0416e42a506425e54130d40c4beb5385b39e0d43c21bca351a3444b` |
| `setup.json` in that directory | `1241921bc37935dd4706cecd0d762afc830d7987dfe3d093a9e875e39fee1a16` |

The creation block checks sizes and both digests, accepts exactly one regular
archive member with the expected name, reads it as bytes rather than extracting
arbitrary archive paths, creates the executable and CLI symlink under the
workspace, and creates a genuine Elan custom link to the already approved
native profile. Existing package/state/archive paths are refused. State is
selected through command-local environment variables; HOME, global defaults
and startup files are untouched. The native profile and custom link must be
regenerated after relocation because their paths are absolute. These behaviors
fit the stated recovery contract in the trusted, clean acquisition shell.

The main setup record reports actual Elan version, link and which commands
returning zero and actual selected Lean 4.35.0 commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. It explicitly reports no regression
suite run. The appendix correctly distinguishes those observations from
acceptance and does not claim that the glibc metadata adapter repairs the
Elan installer.

### Reused round 8 appendix evidence

I read the complete
`session/validation/native-toolchain-candidate-validation-r8-043.json`, SHA256
`d8d99e2f557223af3f61c5ab39854ca696f4d4ef1d0fd5da4cd594e6296f766a`.
It records six commands, all exit zero: syntax checks of all three shell
blocks; execution of the cold creation block; explicit genuine Elan selection;
and selected Lean version execution through the unchanged native helper.

I independently extracted the three appendix shell blocks as text and compared
them with the captured syntax-check inputs. They match exactly. The executed
cold setup is the first block with only `PFDS_ROOT` changed to the recorded
existing cold reconstruction workspace. Its output contains actual Elan
4.2.4 version/which output and the official download. The later command returns
the actual exact Lean identity above. The receipt hash, helper hash and C-source
hash match the cold native profile and current candidate. The selected link's
resolved path matches the recorded native wrapper. These were read-only
comparisons of retained files and link identities; I did not rerun the commands.

The r8-to-r9 difference is exactly the two mode restorations of
`session/validation/run-native-validation.py` and
`session/validation/test-native-validation.py` from 100644 to 100755. All
19 blobs match r8, and the appendix mode is unchanged. Neither restored-mode
controller participates in the cold recipe. Thus reuse of the actual r8 setup
and syntax results is justified for their limited coverage. Round 8 remains
superseded before axis review/approval; its metadata discrepancy is preserved,
not retroactively called an approved candidate.

### Matching original 18-file evidence

I reconfirmed the retained hashes used in my round 7 assessment:

| Evidence under `session/` | Checked SHA256 |
| --- | --- |
| `validation/native-toolchain-candidate-validation-r7-042.json` | `e142a541377e59027008d2299fc19dcb9b5a1613cc460409ffbf90c9ae3b8176` |
| `validation/native-toolchain-final-verification-042.json` | `0359e0ef2cbf8da38d0382cfffa9efc84d4c02dc9e22e03f490bd442c466c206` |
| `validation/native-toolchain-candidate-validation-r6-042.json` | `6f784d8cae601cd843964d2775f03499fd410b2e57a22ca0c15aafabe48d5951` |
| `validation/native-candidate-lake-r6-042.json` | `72127febfd75144b90e124d886eba73bcdff017bb6d306a46c0ef3adb5fba949` |
| `validation/native-candidate-contract-r6-042.json` | `d2b75abc87b8ddc9b4e22492281bbc20f25749a4faf641aa3af1bd9b838f7b36` |
| `environment/native-cold-profile-r6-042.json` | `61a59e98bf1f88af14fce69ef3f84b7c175522ffaae59206cccfef51446bd642` |
| `validation/direct-toolchain-candidate-validation-r2-reconciled-041.json` | `998a2fb578d337f92174c0d4343fa8bd593f32c91f7cf753d8a033e3981c9916` |
| `validation/direct-toolchain-final-verification-041.json` | `a441a4555b1b5ed05ef42ef81e5fc82525b4e506f2aae68d062a0f962260435d` |

This preserves the earlier exact-version, genuine valid/false proof,
Lake compile/link/run, 18-case metadata contract, cold-profile, controller
refusal and recovery-recipe evidence with its original source-specific limits.
The earlier failed r2 aggregate and index-only reconciliation remain separate;
the unchanged sources permit reuse of applicable actual results, not relabeling
of historical failure. No earlier compiler or test command is described as
newly run on r9.

### Stock-suite and formal boundary

The three stock regression scripts and README interfaces are unchanged from
the prior reviewed candidate. The appendix correctly reflects their distinct
setup needs: test-check creates its own fixtures and requires genuine Elan for
its version-mismatch selection; the roots fixture needs no ordinary full
project build; test-proof-audit imports the ordinary ProofAudit output and
iterates the ordinary Applications output directory. I read those unchanged
call sites and fixture setup. A fresh full check uses and deletes private
outputs and therefore does not itself prepare the last suite's ordinary tree.

The appendix requires genuine terminal outcomes and separate command/environment
records, preserves failures/timeouts, prohibits sharing writable build trees
and copying another verification record, and describes any future output reuse
as separately reviewed. Those limitations are appropriate. No existing output
reuse protocol, suite pass, full901 result or formal acceptance is inferred.

**Validation status:** the supplied cold-setup and syntax evidence passed within
its stated coverage; the original 18-file matching artifact evidence remains
applicable. DTP-003 identifies behavior outside that coverage which requires
correction and relevant selection evidence. There is no evidence-access
blocker, and the absence of unrelated formal results is not being used to block
this distinct operational review. The overall Spec outcome is Findings-present
because the one current recipe discrepancy remains unresolved.

## Final disposition and freeze

| Spec item | Disposition |
| --- | --- |
| Base | `76d77a107deb37c30e0b061c30b03a3f8c6aa12c` |
| Candidate | `ff3f709723e5c49e5ba40798abbed7d36141a6fb` |
| DTP-001 | High; fixed with retained review evidence; no regression |
| DTP-002 | Medium; fixed with retained review evidence; no regression |
| DTP-003 | Medium; new and unresolved |
| New findings | 1 |
| Unresolved findings | 1 |
| Worst unresolved severity | Medium |
| Overall Spec outcome | **Findings-present** |

The complete report is frozen when its hash is delivered to the coordinator.
Root owns the correction, applicable evidence, new immutable candidate, final
delivered identity and checkpoint publication. This assessment changes no
status of full901, signed-potential3cf, either prerequisite review, a chapter,
or the book/thesis union.

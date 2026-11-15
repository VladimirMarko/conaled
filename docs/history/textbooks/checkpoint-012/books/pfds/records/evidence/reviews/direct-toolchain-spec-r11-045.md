# Operational toolchain — independent Spec continuation, round 11 (045)

**Outcome: Passed for the complete 20-file operational scope.** There are no
new or unresolved Spec findings. DTP-001 (High), DTP-002 (Medium) and DTP-003
(Medium) retain their documented closures, with the scope qualifications below.
This outcome does not accept any formal candidate, stock regression suite,
chapter or the book/thesis union.

Reviewer: `/root/operational_review/spec`, 2026-11-03. Coordinator:
`/root/operational_review`, continuing the existing `direct-toolchain.md` loop.
I authored none of the scoped implementation, supplied kit or setup evidence.
I performed read-only source, Git, archive, record and hash inspection, and
wrote only this report. I ran no compiler, test suite, build, audit, verifier,
network command, runtime setup or process-control operation. I did not start
another review loop or agent.

## Immutable full scope and requirements

| Item | Independently checked identity |
| --- | --- |
| Fixed base and merge base | `76d77a107deb37c30e0b061c30b03a3f8c6aa12c` |
| Candidate, isolated HEAD and retained ref | `4f15ff6f5bc8091104a3572ca8ce3716ed8e78f0` |
| Ref | `refs/pfds-review/native-toolchain-r11-045` |
| Isolated checkout | `/workspace/scratch/09cf0de22282/pfds/review-native-toolchain-045-r11` |
| Full comparison | `git diff 76d77a107deb37c30e0b061c30b03a3f8c6aa12c...4f15ff6f5bc8091104a3572ca8ce3716ed8e78f0` |
| Full diff | 20 files; 3,805 insertions; two snapshot commits |
| Previous approved candidate | `060e6b877b8db57a30f947b996b7dfe34a5401a1` |

The commit range contains the preserved r10 snapshot and
`4f15ff6 feat(toolchain): resume common candidate with unified native kit (#10000)`.
The full diff file set exactly matches the manifest. I independently matched
all 20 committed, isolated and delivered hashes and executable modes, the exact
ref/base/candidate identities, and empty isolated porcelain. Sixteen previous
files retain their r10 bytes and modes. The other four are the changed
`session/checkpoint.py`, `session/validation/run-native-validation.py`,
`session/validation/test-native-validation.py`, and the new
`session/environment/RECOVER-INTEGRATION.md`.

I read all eight requirements enumerated in
`validation/native-toolchain-candidate-r11-045.json` and independently matched
their hashes. They comprise the original request, book/thesis union, direct
toolchain exception, direct implementation/test scope, environment handoff,
native execution request, common-candidate requirements from 044, and current
recovery requirements from 045. The candidate's AGENTS, README acceptance
interfaces and retained review procedure remain applicable. The current user
instruction selects the supplied unified native kit and requests smaller
current-work recovery archives. The documented 045 interpretation changes the
runtime selection and omission of reproducible upstream history accordingly;
it preserves exact pins, the task-owned source/review bases, local tracking,
chapter order, genuine gates, independent reviews and immediate delivery.

Formal sources and their acceptance decisions, requirements, historical
evidence, trackers/status, review records, runtime binaries and caches remain
outside the authored source diff. The complete supplied kit is an unchanged,
identified external input. Its use does not make the kit's historical PFDS
candidate/scheduling notes override the later checkpoint 044 requirements.

## Whole-task assessment and retained analysis

I read the complete r7, r9 and r10 Spec reports, retaining their analysis only
where the current source identity and context match. Their checked SHA-256s are:

| Report | SHA-256 |
| --- | --- |
| `direct-toolchain-spec-r7-042.md` | `c7df56778cba429b9d2c8c67e5a5f1e52f35e6a106a9ac36a2ecb0f89ac81b04` |
| `direct-toolchain-spec-r9-043.md` | `1651fad484a6c01c68e3038a980e2edce9cbe309f9fef84b1a8167731fd60526` |
| `direct-toolchain-spec-r10-043.md` | `d7dfee97019b9df1f61e59ba2b9951f750fe235faa2290b87dca2f341a3e91d0` |

R9 remains Findings-present on its old candidate. The retained corrections
and analyses do not turn a historical failed, superseded or partial run into
success, nor establish approval of a different runtime's formal results.

| Complete scope group | Current Spec assessment |
| --- | --- |
| Original eight direct-profile/launcher/public-test/controller files | Their exact r10 bytes and modes remain. The prior genuine CLI, valid/false proof, Lake build/link/run, fresh-mode and evidence/refusal analyses remain applicable to those historical tools. |
| Legacy native adapter, launcher and three contract-test files | All five are unchanged. Their bounded missing-own-executable metadata contract, exact executable copies, selector handling and 18-case historical evidence retain their stated scope. The new integration route does not silently replace a legacy run's runtime identity. |
| Existing environment recovery/comparison documents and Elan appendix | All three are unchanged. The new entrypoint directs current recovery to the supplied kit while preserving the old routes as documented historical/fallback procedures. The Elan PATH correction remains present. |
| Native validation controller and refusal tests | Full source inspected, including all existing machinery and the new scope, kit-provider, clean-directory and serial-lock paths. The fixed full/verify bindings and genuine evidence conditions remain intact. |
| Complete checkpoint generator | Full source inspected. The new declared upstream prerequisite removes duplicated public baseline data while preserving task commits/refs, patches, records and actual restore checks. The offline limit is explicit. |
| Integration recovery appendix | Full source inspected. It provides exact setup/candidate/command layout, separate runtime and dependency checks, current evidence paths, immediate verify sequence, lost-session handling and separate formal acceptance obligations. |

### Fixed candidate selection and evidence binding

`run-native-validation.py:32–39` defines the prerequisite and integration
bindings separately. The default still selects exact 901 in
`import-correction-r3` with the historical native launcher. Explicit
`--scope integration` selects exact 3cf in `validation-pfds-integration` with
the supplied kit. Focus is rejected with the integration selector; its existing
explicit 40-hex correction option cannot alter full or verify selection.

The early HEAD/cleanliness checks reject a wrong fixed candidate before runtime
construction. Integration additionally requires a real checkout, `.lake` and
private `.lake/build`. The manifest hash and all nine dependency pins/clean
statuses remain checked. Sharing is limited by the documented PFDS single-writer
discipline to the exact dependency store, while project outputs remain private.
The general kit's refusal of symlinked package layouts is not disabled: this
route uses runtime-only doctor and the controller's existing dependency checks.

The retained full-evidence reader now binds the requested scope, candidate,
checkout and runtime, as well as actual successful terminal result, stock
command/mode, clean final identity, equal queued/start/final snapshots, log hash
and saved stock-record hash. An absent historical scope marker is interpreted
only as the legacy prerequisite scope. It cannot authorize integration.
Verification additionally compares current inputs and live stock-record bytes
with that same successful full record and rechecks them after the actual stock
verifier. No arbitrary full path/SHA or retrospective acceptance of old 901
from a 3cf run is introduced.

### Supplied runtime and child ownership

The integration route fixes the sibling kit directory and its manifest digest,
runs the supplied kit verification, checks the imported runtime location, and
uses the kit's project pin check and `environment(native-state, 1)` API.
`unified_identity` retains profile configuration/hash, the bounded full doctor
result, selected environment controls and the kit manifest identity. Only the
observational `free_bytes` field is removed from equality. The controller also
captures the supplied archive and current 044/045 requirement hashes.

I inspected the actual kit provider and runtime functions. The provider used
here is the same environment function used by kit `run`: it verifies the
profile, clears stale selectors, selects the pinned profile on PATH, supplies
one Lean thread and the recorded library/cache/state paths, and leaves `LEAN`
unset. Lake/checker-generated inner paths are preserved by the runtime layer.
The supplied kit and official executables are not edited by this adoption.

The controller accurately records this API selection and the direct stock argv.
It launches that argv with the constructed environment and
`start_new_session=True`; the stock `check.sh` then `exec`s its Python checker.
It does not nest kit `run`, which would create a second session. Thus the
existing owned-child process-group cleanup still targets the checker tree
rather than only an outer kit logger. Exceptions and cancellation retain
observed/unknown terminal distinctions; failed postchecks cannot become a
successful full record.

All modes acquire both legacy cooperative lock files in the same fixed order,
nonblockingly, before entering their run. This implements the current serial
compiler schedule and excludes a concurrent older caller holding either lock.
As the documentation states, frozen-source and no-external-writer discipline
remain operational requirements; the controller is not an artifact-tampering
certificate or a universal scheduler for unrelated launch commands.

### Compact recovery semantics

The generator retains local branches and `refs/pfds-review/`, along with the
needed baseline remote refs. It checks each included task tip descends from the
fixed original base and requires the bundle's sole prerequisite to be that
exact base. It neither silently substitutes a moving branch nor discards a
current task candidate or full review base to achieve the size reduction.
Unrelated upstream remote-tracking history is omitted.

Restore checks every retained member digest, initializes a fresh repository,
fetches the exact baseline at depth one from the original public remote or a
specified local source, checks its identity, verifies/unbundles the task bundle,
restores the recorded refs and branch, applies index/worktree patches and
untracked files, restores session records and disables the push URL. The
generator still compares recovered source, index/worktree state, included
ignored artifacts and refs, and refuses unstable capture or an existing archive.

The actual checkpoint045 restore test uses the local repository as an object
server but fetches only the exact baseline into the initially empty repository
before importing task data from the bundle. The completed log records that
sequence and `restore_test: passed`; it is not a clone of the already completed
task tip. This establishes the local baseline-dependent source recovery route.
It does not claim to have tested future GitHub availability. The README and
current runbook state the network/local-baseline dependency and do not claim
that all third-party inputs are included for completely offline recovery.

I independently inspected checkpoint045's bytes and manifest: 9,486,734 bytes,
SHA-256 `8eb968d0ac3e5776b5d2a80075042c5cc552565cf3e8218eb5dc93f3938b771d`,
45 retained refs and 1,208 session records. Its 20 source files match this
candidate, and its supplied-kit archive matches the recorded
`45edfb844068f93b26ea5469572473f8c07e5a63e2bc294eed6de543cb3d5bf2` digest.
The old main, Chapter 2, common-candidate and operational review identities
survive. Runtime caches and manuscripts remain reproducible or separately
required source inputs, as documented. This recovery result is not a Lean gate.

## Retained Spec findings

| Finding | Original severity | Current disposition and scope |
| --- | --- | --- |
| DTP-001 | High | Fixed; no regression. Full fresh adds only `--fresh --jobs 1`, verify uses the same successful record's mode and receives neither flag. Both fixed scopes retain matching stock-record checks. The new runbook requires a genuine fresh baseline for the new runtime and distinguishes temporary fresh outputs from ordinary regression prerequisites. |
| DTP-002 | Medium | Fixed; no regression. The unchanged legacy smoke helpers retain their owned temporary-parent creation and earlier absent-parent evidence. New kit setup and actual checkpoint restoration supply their own genuine cold/current recovery evidence; excluded temporary directories are not treated as pre-existing inputs. |
| DTP-003 | Medium | Fixed in the unchanged historical Elan recipe. Its verified package still precedes ambient PATH and the r10 selector evidence retains its original meaning. This closure does not assert that a stock suite has run under the new unified runtime; those selections/outcomes remain separately required. |

No new DTP identifier is allocated. The Standards findings and their severities
remain a separate axis; this report does not close or rerank them.

## Applicable validation and remaining boundaries

The current aggregate is
`validation/native-toolchain-candidate-validation-r11-045.json`, SHA-256
`13a3a8ed9731235fa6c10cdc3692f2fd2ba7b478c70c66476ed6c0be60ad1b25`.
Its post-dispatch additions preserve actual fixture and restore receipts;
source and requirement identities did not change. The dispatch receipt's older
aggregate hash remains a historical observation, not a contradictory source
approval.

| Evidence | Assessed meaning |
| --- | --- |
| `native-controller-r11-isolated-045.log`, SHA-256 `8881c4c4e861231743eef0925acf5f500f4f03de5a3ede9c7e1efabbfc65e2ec` | All eight public CLI refusal tests passed on the isolated candidate. They cover old evidence refusal, interrupted evidence, original/focus lock behavior, explicit integration selection, cross-scope/wrong candidate refusal, fixed checkout routing and cross-mode exclusion. Incomplete fixture records are explicitly marked and cannot constitute a real full success. |
| Retained scope/binding/selection red and green logs | Demonstrate the requested behavior was missing before its implementation and passed afterward; they are controller fixture evidence only. |
| Current aggregate runtime/syntax/source checks | Repeated runtime identity agrees; intended selectors and four shell blocks were checked; all 20 live/isolated source hashes agree. No compiler gate was run for these artifact checks. |
| `environment/unified-native-setup-045.json`, SHA-256 `2346adeceaeaa5990785876457b0f427a9532672daf865056c6de6de087d3549` | Actual terminal setup exit zero; exact distribution and nine clean dependency pins; 9,031 cache files; all ten expected smoke outcomes. I inspected retained version, valid/false proof, Lake-child, native-run and Mathlib logs and the true/false theorem fixtures. The false theorem genuinely fails and the native executable prints 42. |
| `validation/checkpoint045-create.log`, SHA-256 `07a8b1e74c002e9dcb228c3cbbc0a5f0571485f604454a355d8ac61a7ef3edbe` | Actual compact checkpoint creation and restoration passed with the declared baseline prerequisite. The complete supplied kit is included. |

The source manifest hashes to
`235eab36d688b059c8861bef0675accd04ee6ccc79e51f601d90b99adf88ffaa`.
The supplied kit manifest currently matches the fixed
`72ba31d697b09e71cd21edbf6a46340f1fef6380585df86eb0320e1b05b737b6` digest.
The profile's 47+8 checks are bounded subsequent verification, not a new
whole-distribution attestation; the original archive acquisition supplies its
separate complete initial digest. These limitations are represented accurately.

**Applicable operational artifact validation is established.** No missing
formal full result is being used as a circular prerequisite for approving this
compiler-free controller extension. Conversely, these artifact checks do not
supply the common candidate's required actual fresh full build, exhaustive
audit, matching success record, stock regressions, two formal review axes,
dependency-ordered acceptance or immediate final verification. The appendix
preserves those obligations and Chapter 2's unaccepted frontier.

## Final disposition

Spec outcome: **Passed**, for the complete operational task on fixed base
`76d77a107deb37c30e0b061c30b03a3f8c6aa12c` and candidate
`4f15ff6f5bc8091104a3572ca8ce3716ed8e78f0` with the eight saved requirements.
**New findings: 0. Unresolved findings: 0. Worst unresolved severity: none.**

This report is frozen when its digest is sent to the coordinator. Root must
read both independent outcomes, verify exact delivered identity and preserve
the resulting review evidence before using the new integration route. Any
later source change needs the applicable continuation of this same loop.

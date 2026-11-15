# Operational toolchain — independent Spec review, round 7 (042)

**Outcome: Passed for the complete operational-toolchain scope.** There are
no new or unresolved Spec findings. DTP-001 and DTP-002 retain their round 2
closures, with no regression found. This outcome does not accept a formal
candidate, chapter, or the book/thesis union.

Reviewer: `/root/chapter02_continuation_plan`, 2026-11-03.
Coordinator: `/root/direct_toolchain_validation_plan`, continuing the existing
`session/reviews/direct-toolchain.md` loop. I authored none of the reviewed
implementation. My earlier assignments were read-only continuation/source
analysis and comparison of the user-supplied environment guide.

## Immutable scope and identity

| Item | Identity |
| --- | --- |
| Base | `76d77a107deb37c30e0b061c30b03a3f8c6aa12c` |
| Candidate | `af2c53dce68ebb122c81175312d6bb30df9aac05` |
| Merge base | `76d77a107deb37c30e0b061c30b03a3f8c6aa12c` |
| Retained ref | `refs/pfds-review/native-toolchain-r7-042` |
| Isolated checkout | `/workspace/scratch/b566cace4ed6/pfds/review-native-toolchain-042-r7` |
| Commit | `af2c53d feat(toolchain): bind corrected focused native candidates explicitly` |
| Complete diff | 18 files, 3,308 inserted lines |

The comparison is:

```text
git diff 76d77a107deb37c30e0b061c30b03a3f8c6aa12c...af2c53dce68ebb122c81175312d6bb30df9aac05
```

I independently resolved HEAD and the retained ref, confirmed the merge base
and single commit, and observed an empty isolated checkout status. I recomputed
all 18 isolated and delivered file hashes against the manifest; all match.
I also checked the saved requirement hashes and the six reused evidence hashes.
This is source/evidence identity inspection, not a repeated compiler or test run.

The full source scope comprises:

- The original eight files: `environment/make-direct-toolchain-profile.py`,
  `environment/run-direct-toolchain.py`, `environment/test-direct-toolchain.py`,
  `environment/test-direct-lake-build.py`, `environment/README-direct-toolchain.md`,
  `validation/run-direct-validation.py`, `validation/test-direct-validation.py`,
  and `validation/direct-validation-runner-notes.md`.
- `environment/RECOVER-ENVIRONMENT.md` and
  `environment/environment-route-comparison-042.md`.
- The complete `checkpoint.py` generator.
- `environment/native-own-exe.c` and `environment/run-native-toolchain.py`.
- `environment/test-native-own-exe.c`, `environment/test-native-own-exe.py`,
  and `environment/native-readlink-fixture.c`.
- `validation/run-native-validation.py` and
  `validation/test-native-validation.py`.

These paths are relative to the candidate's `session/` directory. I reviewed
the complete intended behavior, retaining the prior independent analysis and
matching validation of the unchanged eight files, rather than restricting the
assessment to the latest corrective lines. I read the native controller in
full and compared it with the complete original controller; the difference
preserves the prior full/fresh/verify machinery while changing the runtime
identity and adding the explicitly bound focused candidate.

Formal sources, prior records, runtime binaries/caches, trackers, requirements,
reviews and provenance records remain excluded from the authored-source diff
and retain their separate obligations. No formal proof statement changes are
part of this candidate. No new implementation/review loop was started.

## Requirements and applicable guidance

I read the candidate's `AGENTS.md`, README development/build/audit sections,
`.agents/skills/code-review/SKILL.md`, its heuristics and invocation reference,
and `docs/agents/review-loop.md`. The user's saved Nix exception overrides only
the Nix launch requirement. It leaves exact pins, genuine checking, isolated
frozen inputs, proof audits, independent reviews, final verification, local
tracking and durability requirements intact.

The complete saved requirement versions used here are:

| File under `session/` | SHA256 |
| --- | --- |
| `requirements/REQUEST.md` | `b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499` |
| `requirements/REQUEST-union-v2.md` | `3336bed1154438b3683aeb5a1c63fee44e87aff190f5ff69e34705a780b9d22c` |
| `requirements/REQUEST-direct-toolchain-041.md` | `16845edec15c311e0cfd5ed5d4f5c4feb61e7ad96545653d5b872309d26464bc` |
| `environment/direct-toolchain-implementation-scope-041.md` | `05c125ee129eafc8f45f9367be16259c3239c7b3945c32f62effba1f1b4c922c` |
| `requirements/REQUEST-environment-handoff-042.md` | `200789123c60ae137967f881207194412eecea72ba2fc80247978075bd6a4602` |
| `requirements/REQUEST-native-toolchain-042.md` | `d76dc8dcf771a227779628de91e75c4b63a2898b95e7b30035de83537dae5195` |

The supplied guide is comparison data, preserved at
`session/references/conaled-environment-guide-from-user-042.md`, SHA256
`ef85039f6097a1a646bb2b980178a2285e23124e5881686f68020acfa2f5d4f1`.
It does not authorize reading other Library sources or replacing the PFDS
history. Its different checkpoint 039 and ADWH continuation branch are
explicitly distinguished in the candidate documentation.

## Retained finding dispositions

### DTP-001 — Required fresh full-check path

**Original severity: High. Disposition: Fixed with review evidence; no regression.**

The original eight helper files exactly match approved round 2 candidate
`822cb7adeed4943acaf10454e9facfc2e3ee8ceb`. The native controller preserves
the same correction. `run-native-validation.py` adds `--fresh --jobs 1` only
to the full stock candidate command, records its actual verification mode,
requires matching successful stock evidence, and sends only
`./check.sh --verify-candidate HEAD` in verify mode. A saved fresh result
cannot be relabeled incremental or vice versa. Both recovery documents retain
the requirement for a fresh full check after the runtime/tooling transition.

The native record additionally requires `runtime: native`, the fixed full
candidate 901, complete successful terminal evidence, identical queued/start/
final inputs, matching log and verification digests, and matching live stock
verification bytes. The focused override cannot change the full/verify pin.
The earlier red/green and r2 closure evidence remains valid for the unchanged
original files; current controller refusal evidence covers the new public
argument and lock behavior. No successful formal record was synthesized.

### DTP-002 — Missing cold-recovery temporary parent

**Original severity: Medium. Disposition: Fixed with review evidence; no regression.**

Both unchanged public smoke tests create their workspace-local `session/tools`
parent before allocating test projects. The original r2 absent-parent evidence
remains applicable. The native r6 cold-profile evidence also records
`lake_temporary_parent_absent: true` and a successful genuine Lake build/run
after the test created that parent. The native contract runner independently
creates its owned fixture directory with parents. No excluded temporary
directory is an undeclared prerequisite for these public test paths.

No new DTP identifier is allocated in this round.

## Complete requirement assessment

### Native execution and genuine compiler behavior

`run-native-toolchain.py` pins the original Lean, Lake and leanir executable
hashes, requires regular nonsymlink inputs, makes identical regular copies,
and generates per-entrypoint wrappers. It builds the small metadata library
from the included source, records the C compiler and command, stages a new
profile and renames it into place. Existing profiles are refused. Its
read-only `--describe` checks source, library, originals, copied executables,
wrapper and receipt identities, including the profile location and helper hash.
Relocation requires regeneration, as the handoff explicitly explains.

The adapter in `native-own-exe.c`, especially `launch_path` and `readlink`,
implements the stated bounded contract. It resolves and calls the next
`readlink` implementation first. Successful results and errors other than
`ENOENT` are returned unchanged. Fallback is restricted to the exact current
process executable links, a nonzero valid buffer, and an absolute per-exec
marker equal to the process's own `AT_EXECFN`. Canonical-path, regular-file
and ELF-magic checks reject unsupported launch descriptions. It does not infer
identity from `argv[0]`, redirect unrelated paths, manufacture compiler output,
or turn permission errors into successful lookups.

The launcher preserves the order and precedence of inherited preload entries,
rejects unexpected Lean/Lake selectors, sets explicit workspace caches and one
Lean thread, and removes stale caller markers before dispatch. Compiler
wrappers set their own markers; directly launched canonical workspace ELF
commands receive their own marker. An unrelated exec inherits a mismatched
marker and therefore cannot use the fallback. The documented frozen-image
and directory-binding assumption is necessary: this is not authentication,
general procfs emulation, arbitrary-libc equivalence, or support for scripts,
descriptor/direct-loader execution, invalid pointers or async signal handlers.
Those are explicit scope boundaries, not claimed functionality.

The exact official release, its libraries, stock check scripts and proof
policy are not replaced or modified by this candidate. The native path removes
CPU emulation; the retained performance comparison appropriately qualifies
its single timing pair and substantial import-I/O variability rather than
promising a universal speedup.

### Tests and evidence meaning

The tests exercise genuine public interfaces. The Lean/Lake checks require
the actual exact versions, acceptance of a valid theorem without axioms,
rejection of a false theorem with a type mismatch, Lake compilation/linking,
and execution yielding `42`. The cold r6 proof pair uses implicit Init, with
the source strings retained; broader earlier import-Lean results and formal
project checks are not silently replaced by that smaller fixture.

The three native contract-test files cover buffer/truncation behavior,
ordinary delegated paths, argv and cwd independence, fork, constructor and
concurrent first calls, stale-marker exec and a child's own launch, inactive
markers, controlled downstream success/ENOENT/permission/error behavior, and
preservation of an inherited upstream layer. The expected paths come from
the test caller. Controlled outcomes are explicitly owned fixtures and are
not represented as observations of protected host resources. The records
retain commands, actual output, input identities and unsupported cases; all
18 recorded cases passed with unchanged inputs.

### Native evidence controller and formal boundary

The controller preserves the unchanged stock full gate, source policy,
coverage, build, audit, version and final-verifier interfaces. It checks clean
exact project/dependency identities and the fixed manifest; records source,
runtime and controller identity before/start/after; refuses old evidence
paths; uses exclusive creation and atomic record updates; and retains the
one-full/one-focused nonblocking lock discipline and owned-child cancellation.
Unknown or interrupted terminal results cannot support successful verification.

The new `--focus-candidate` accepts only a lowercase 40-hex commit in focus
mode. `run_locked` checks the actual HEAD against the requested/default pin
before launching the eleven retained targets and checks it again afterward.
The requested value and resolved project identity are recorded. Full and
verify remain fixed to 901. No focus result grants full or chapter acceptance.
Every result retains `acceptance: false`.

Before/after checks do not prove absence of transient edits or make shared
writable project outputs safe. The existing isolated, frozen-input discipline
remains a documented operational precondition. A change of runtime has its
own record and cannot be presented as completion of the interrupted QEMU run.

### Recovery, comparison and durable checkpoint entrypoint

The complete recovery guide supplies the authoritative PFDS archive/history
identity, prerequisites, exact Lean and fallback-QEMU acquisition and hashes,
native creation/inspection/version steps, all nine pinned dependency recovery
steps, and candidate checkout setup. Existing dependency sources are verified
rather than reset. The private-output recipe refuses symlinked `.lake` and
build directories; only package sources are shared.

The cache recipe correctly gives the cache executable its own native marker
inside the Lake environment. Pinned Lake's target resolver searches workspace
targets, supporting the documented `lake build cache` selection. No new cache
retrieval is claimed by reviewing that recipe. Public smoke and metadata tests,
fresh full/focused/final verification commands, new evidence names, lost-run
handling, current candidate limits and source-availability limits are all
covered. Chapter 2 remains the earliest unaccepted chapter; introductory
accounting is not represented as whole-union proof completion.

The comparison distinguishes the same Lean bytes from the different QEMU
packages, observed local behavior from the guide's reports, atomic creation
from idempotent setup, read-only inspection, leanir coverage, inherited
selectors and explicit cache paths. Its stronger Ubuntu authentication claim
is supported by the retained actual acquisition record, including successful
gpgv output, the attributed installed public keyring, signed index/package
hashes and selected executable identity. It explicitly does not claim that
the Ubuntu emulator was selected, run or proven faster. I inspected this
retained evidence; I did not rerun authentication or access external links.

The entire checkpoint generator was reviewed. Comparing it with retained
predecessor SHA256
`617c14ed63170ee39a8ac1df2eb4cc20b1b509ebd5f1d4c16ae4e469b7ed51ab`
shows exactly the README and restore-success pointer updates. The generator
continues to preserve Git refs/history, patches, task records and checksums,
test restoration, refuse conflicting archives, and exclude reproducible
tool/cache inputs. Its generated entrypoint now routes takeover to the durable
runbook and explicit Nix exception. Creation, restoration testing and immediate
delivery/upload of the next actual archive remain separate required actions;
this review does not assert that an uncreated archive has been tested or saved.

## Validation status and reuse

**Applicable operational artifact evidence: Passed.** The r7 aggregate was
created after its manifest's historical `Pending` field. I checked its actual
commands, results and identity rather than treating that earlier field as a
final status.

| Evidence under `session/` | SHA256 and scope |
| --- | --- |
| `validation/native-toolchain-candidate-r7-042.json` | `257e31713ec28c4c12cafb7635ad14098f09d8bc765c79d541b7ff30d27ac593`; complete scope and requirements |
| `validation/native-toolchain-candidate-validation-r7-042.json` | `e142a541377e59027008d2299fc19dcb9b5a1613cc460409ffbf90c9ae3b8176`; four public refusal tests, shell syntax checks, two existing-state recovery recipes, exact delivered identities |
| `validation/native-toolchain-candidate-validation-r6-042.json` | `6f784d8cae601cd843964d2775f03499fd410b2e57a22ca0c15aafabe48d5951`; cold native profile, actual versions and valid/false proofs, linked artifact checks |
| `validation/native-candidate-lake-r6-042.json` | `72127febfd75144b90e124d886eba73bcdff017bb6d306a46c0ef3adb5fba949`; profile compiler, C compilation/linking, executable output 42 |
| `validation/native-candidate-contract-r6-042.json` | `d2b75abc87b8ddc9b4e22492281bbc20f25749a4faf641aa3af1bd9b838f7b36`; 18 cases passed, before/after input identity equal |
| `environment/native-cold-profile-r6-042.json` | `61a59e98bf1f88af14fce69ef3f84b7c175522ffaae59206cccfef51446bd642`; constructed native profile identity |
| `validation/direct-toolchain-candidate-validation-r2-reconciled-041.json` | `998a2fb578d337f92174c0d4343fa8bd593f32c91f7cf753d8a033e3981c9916`; original eight files' applicable checks and explicit index-only reconciliation |
| `validation/direct-toolchain-final-verification-041.json` | `a441a4555b1b5ed05ef42ef81e5fc82525b4e506f2aae68d062a0f962260435d`; approved original helper delivery identity |

All 14 r6 files claimed unchanged in the r7 reuse record match both r6 source
maps and the r7 manifest. All original eight files match the approved r2
manifest. The native adapter, launcher, fixtures, original executables and
profile inputs relevant to the reused cold checks are unchanged. R7 separately
checked its changed native-controller public behavior and documentation.
Accordingly, this is justified input-specific evidence reuse, not a claim
that r6 approval exists or that its complete candidate equals r7.

The earlier failed r2 aggregate remains failed and preserved; its index-only
repair and limited artifact-test reuse remain explicitly reconciled. The
incomplete/superseded r3–r6 review states supply no inferred approval. The
successful documentation recipes took existing-state verification branches;
they do not claim a new end-to-end network acquisition or complete checkpoint
restore. Prior provenance and the actual cold profile checks establish their
stated narrower coverage.

No completed full native 901 proof/audit result or formal acceptance is supplied
by this artifact evidence. The failed d24/956 focused evidence is preserved;
the corrected formal candidate 3cf3de4f has its own source review and genuine
run obligations. None of these states is promoted by this tooling outcome.

I ran no compiler, test suite, build, cache command, network request or protected
surface probe; I changed no source, runtime, controller, tracker or shared
finding record. A brief read-only exec transport outage was followed by a
successful retry, so no evidence-access blocker remains. This report is my
only written file for the review and is frozen when delivered.

## Final disposition

- **Base:** `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`.
- **Candidate:** `af2c53dce68ebb122c81175312d6bb30df9aac05`.
- **Spec outcome:** Passed for the complete operational-toolchain scope.
- **Retained findings:** 2; DTP-001 and DTP-002 fixed with review evidence.
- **New findings:** 0. **Unresolved findings:** 0. **Worst unresolved:** none.
- **Validation:** applicable artifact evidence passed with the scoped reuse
  above; formal candidate/chapter/union gates remain separate and unaccepted
  by this review.

Approval applies only to this immutable candidate and these saved requirements.
The coordinator must retain both independent outcomes and verify final
delivered identity before operational acceptance. Later source changes require
the existing loop's applicable new candidate review.

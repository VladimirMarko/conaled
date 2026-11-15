# Native environment — independent Standards review

**Outcome: Passed for the bounded environment/recovery implementation.**
Unresolved Standards findings: **0**. Worst Standards issue: **none**.
This does not approve Chapter 1, a project verification run, or any formal claim.

## Immutable scope and continuity

- Snapshot repository: `/workspace/scratch/6bb268f9336f/environment-review-0068`.
- Fixed base and confirmed merge base:
  `900614e27f7d3dfffd9a29139884a8f1a4fce8d3`.
- Reviewed candidate: `9f673480206912d7df4a1dcc2b09ca7527bb0275`.
- Previous environment candidate: `5fe6d4f7cdac2761c7c3622d26479282cfb7fa1b`.
- Full comparison: `git diff BASE...CANDIDATE`; all eleven paths in
  `environment-native-snapshot.json`, with no task-diff exclusion.
- Formal source remains separate at
  `07e480f6ec9958d4975bb90151005b84f2907614`, original formal review base
  `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.

The snapshot was clean. All eleven immutable-snapshot file digests were
independently matched against the snapshot manifest and corresponding actual
control files, including the compiled compatibility library. The entire new
native adapter, C source, test harness sources, recovery guide and request/
checkpoint-text delta were read. The prior five-path source analysis remains
applicable where unchanged; its historical report is preserved separately.

Applicable standards remain conaled's AGENTS, README environment/build/audit
rules, shared review procedure and review heuristics, together with the user's
explicit exact-version Nix exception. The new user request rejects the slow
emulated route and asks for alternatives; it does not alter formal scope or
acceptance. The frozen request correctly records that distinction.

## Runtime boundary and source assessment

The native adapter preserves the official Lean and Lake executable bytes and
checks their digests, the compatibility source digest, and its compiled-library
digest before execution. It rejects an unexpected existing LD_PRELOAD or
LD_AUDIT setting, keeps the change local to the invoked command and descendants,
clears inherited Lean selectors and supplies the original release libraries.
It resolves the first executable to an absolute pathname and does not rewrite
the caller's arguments as shell code.

The compatibility component is a disclosed additional runtime dependency.
Its source and recorded exported-symbol inventory supply one global function,
`readlink`. The actual syscall is always attempted first. Successful results
and errors other than ENOENT return directly. A fallback is considered only
for the exact own-PID executable path or `/proc/self/exe`; other paths keep
the original syscall result and errno. The fallback requires AT_EXECFN to be
absolute, resolves the existing path, verifies ELF magic and copies at most
the caller's capacity without adding a NUL. Failed fallback checks restore the
original failure errno; successful fallback restores the incoming errno.

The Linux manual's [getauxval description](https://man7.org/linux/man-pages/man3/getauxval.3.html)
identifies AT_EXECFN as the launch pathname supplied through ELF startup data.
The [readlink interface](https://man7.org/linux/man-pages/man2/readlink.2.html)
specifies byte-count returns, truncation and absence of an appended NUL. These
primary references support the interface interpretation; actual host behavior
is established by the retained local tests, not by documentation alone.

The supported domain is deliberately narrower than a general proc filesystem:
normal launches of stable ELF executables at absolute paths. Relative launch
paths and interpreted scripts are rejected by the fallback. Explicit dynamic-
loader launches and replaced/deleted executables remain outside this contract.
The recorded absolute first-command, Lake-child and explicit cache paths fit
the supported domain. No mount, permission, tracing or process-isolation
control is changed, and no other process's executable is synthesized.

The source does not intercept proof checking, axiom collection, object loading/
serialization, compiler identity or process exit reporting. This observation
does not constitute a proof of arbitrary binary equivalence. The limited
compatibility function remains part of the trusted runtime used for subsequent
checks, and the guide says so explicitly. Stable source and executable files
during a check remain required.

## Provenance and recovery completeness

`native-library-build.json` records the actual successful C compiler command,
GCC version, source hash, 15984-byte binary hash and dynamic-symbol inventory.
Both source and binary are included in the checkpoint's control tree. The
guide gives the matching rebuild command and refuses to normalize a changed
build by silently replacing the expected hash. Different compiler/host output
requires its own preserved evidence and review.

The official release acquisition recipe, exact Lean/Lake versions and all nine
manifest dependency revisions are preserved. The adapter changes no project
source, pin, build command, output-integrity algorithm or proof policy. The
new recovery text points to the self-contained native guide, while the earlier
QEMU guide and complete adapter remain available as the recorded fallback.
Relocation follows the documented repository/control layout without carrying
old generated absolute-path QEMU launchers into the native route.

The native guide correctly limits setup claims, documents the extra runtime
component, retains both independent formal review axes and immediate candidate
verification, and directs continued chapter-by-chapter work. The checkpoint
generator changes only recovery prose in this scope, not its source/history/
control capture algorithm. Actual checkpoint creation and upload remain the
caller's delivery obligations; this review does not assert they occurred.

## Validation reconciled

The final native smoke binds the exact adapter/source/library digests to this
candidate and records ten zero exits: description, compiler version/commit/
prefix, Lake identity and child selection, two actual theorem compilations,
and native cache-tool startup. Both 6824-byte theorem outputs match each other
and the earlier QEMU output digest
`fbf279c5128799661a3f3087d27f139d4da4944e9061ae0c522fce3af38bb980`.
Both compilers report no axioms for these smoke declarations. The smoke record
also checks clean exact formal source and all nine clean pinned dependencies.
These examples demonstrate the relevant execution paths; they do not replace
the exhaustive project build/audit or establish a whole-project speed claim.

The checked boundary harness compares unaffected readlink paths/errors against
the raw syscall, checks both own-executable forms, small-buffer truncation,
zero capacity and untouched guard bytes. Separate recorded launch probes
exercise absolute ELF success, relative ELF rejection, interpreted-script
rejection and the normal check.sh shell/Python startup path. The actual test
sources and matched digests are retained. No duplicate tests or compilers were
run by this reviewer.

Native cache retrieval completed with actual exit 0 in 70.790899 seconds and
records all 9031 files downloaded/decompressed. Its closed 14180-byte log was
independently checked against the recorded SHA-256
`0d8d4438cf46da7f099a5db77a32a67ae05121e2e8656481449afcca320e405f`.
The command retains the normal cache origin/scope and no unsafe option. The
recorder reports the same clean formal candidate and no verification record.

The formerly pending QEMU cache build r2 also has an actual exit 0, in
161.539630 seconds, and matching closed 588-byte log SHA-256
`ebaf6dc29a83d012474cc6c70c9f9e9f97c6d5be1bc11049d619499d8ce73dac`.
It ran the corrected recorder and supplies the previously missing ordinary
success-path evidence. The earlier matched progress-failure test remains the
focused error-path evidence; the recorder is unchanged in this native delta.
ENV68-SPEC-001's resolution remains owned by the independent Spec report.
No earlier interrupted or unknown outcome is relabeled by these later passes.

## Next full Chapter 1 check: mode determination

**The complete ordinary guarded `--candidate HEAD` route is applicable in this
specific recovered checkout.** This determination is limited to the evidenced
environment and cold project outputs; it is not a waiver of README's fresh-mode
triggers for later changes.

The compiler release, dependencies, project compilation configuration, checker,
guard and exhaustive audit are unchanged. The added component adapts a missing
host pathname query; it does not change the project's build/verification
algorithm or compilation directives. At the bounded review inspection the
project `.lake/build` directory was absent. Consequently the first ordinary
run has no old project outputs to reuse, and every integrated project module
must compile under the selected native environment. External pinned dependency
cache reuse is permitted in both normal and fresh modes.

The required run must still execute source-policy/public-coverage checks,
candidate/compiler/dependency checks, both output-integrity phases, the complete
integrated build and exhaustive transitive-axiom audit. It must retain its true
terminal result and matching verification record. A hash-helper or post-build
integrity failure remains an incident to preserve and investigate, never a
reason to bypass the guard. Later stale-output suspicion, compiler/pin/project
tooling change, or changed compatibility implementation requires reassessment
under the unchanged README and incident procedure.

No second cache-independent project rebuild or unrelated validator fixture
suite is introduced by this environment-only review. The prior formal-change
fixture applicability ruling is retained, with its original limits. Full
Chapter 1 success, both formal review axes on the original full scope, and
immediate `--verify-candidate HEAD` remain outstanding separate gates.

The concrete remaining disk-capacity issue is operational and is being handled
by root. This report does not promise sufficient storage or a successful future
run. No formal source, cache output, pin or implementation artifact was changed
by this reviewer; this report is the sole new write.

## Final disposition

Environment/recovery Standards: **Passed**, zero unresolved findings, on exact
candidate `9f673480206912d7df4a1dcc2b09ca7527bb0275` against fixed base
`900614e27f7d3dfffd9a29139884a8f1a4fce8d3`.

Chapter 1 and all other chapters/appendices/shared units remain unaccepted.
SPEC-001/002/003/V001, their requirements, the original formal base and repaired
candidate remain unchanged. Actual source acceptance is not supplied by a
native environment, dependency cache or recovery checkpoint.

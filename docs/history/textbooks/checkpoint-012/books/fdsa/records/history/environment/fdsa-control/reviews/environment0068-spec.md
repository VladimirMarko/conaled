# Environment/recovery tooling 0068 — independent Spec review

**Current Spec outcome: Passed for environment candidate
`9f673480206912d7df4a1dcc2b09ca7527bb0275`, with zero unresolved Spec findings.**
This is the native continuation of the same environment review loop. Status
statements within earlier rounds below are preserved historical outcomes.
No Chapter 1 or whole-book acceptance is granted by this report.

## Round 1

**Outcome: Findings-present.** One unresolved moderate source finding;
matching terminal evidence for the live recorder exercise is also pending.
This is an environment/control-artifact review, not a final Chapter 1 review
or formal acceptance.

### Immutable scope and requirements

- Snapshot repository: `environment-review-0068`.
- Fixed base and merge base: `900614e27f7d3dfffd9a29139884a8f1a4fce8d3`.
- Candidate: `b8ce485c872ee4c1b227b318b5b5854a13d11b83`.
- Full diff: `git diff BASE...CANDIDATE`; five paths:
  `ENVIRONMENT.md`, `REQUEST.md`, `checkpoint.py`,
  `tooling/pinned_toolchain.py`, `tooling/record_command.py`.
- Commits: `9eb543e` (environment recovery) and `b8ce485`
  (foreground-recorder correction). The working snapshot was clean.
- Independently recomputed hashes of all five live control artifacts and all
  five snapshot files match `environment0068-snapshot.json`.

The reviewed requirements are the full frozen `REQUEST.md`, the explicit
user environment exception, and the retained user request/complete supplied
setup guide under `provenance/qemu-environment-20261103/`. The current request
is to apply that working exact-version environment route, include equivalent
self-contained instructions in the next checkpoint, then resume the FDSA
formalization. The guide's unrelated checkpoint 039 is not a prerequisite or
source input for this task and was not accessed.

The implementation uses conaled's existing code-review/shared review rules.
The Nix exception changes environment selection only. The exact official
compiler/library pins, full source and axiom checks, fixed FDSA scope,
independent final review and immediate candidate verification remain required.
The unchanged formal candidate is `07e480f6ec9958d4975bb90151005b84f2907614`,
with original base `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.

### ENV68-SPEC-001 — Progress bookkeeping can abandon the owned child

**Severity: moderate. Status: unresolved.**

Candidate `tooling/record_command.py`, lines 64–75, performs
`save(progress.json, ...)` and `log.stat()` outside an exception guard before
each `child.wait`. If either secondary progress operation raises, the recorder
exits without waiting for its already-started child and never reaches the
primary exit recording at lines 76–81. This conflicts with the requested robust
preservation of the actual outcome and the documented separation of command
exit from secondary bookkeeping.

This matters concretely for this task: its prior validation encountered disk
exhaustion. A full disk or transient failure writing the progress sidecar can
abandon an otherwise live command, or lose an exit available immediately after
that failed write. Correctly calling the missing outcome unknown avoids a false
success, but does not fix the avoidable loss of command ownership and evidence.

**Required remedy:** make nonterminal progress updates best-effort, retaining
the same owned child and continuing to wait after an ordinary progress I/O
failure. Preserve a compact diagnostic if possible. Keep primary actual exit
recording ahead of optional final Git/log/verification bookkeeping and preserve
the no-retry/no-overwrite behavior. A permanent inability to write the primary
result can still leave an explicitly unknown durable outcome; no impossible
guarantee against total storage loss is requested.

A narrow exercise that fails the progress-sidecar write while the owned child
returns a known nonzero exit is appropriate evidence for this correction.
It should show the real exit retained and no second invocation. No additional
project build or broad unrelated fixture suite is needed for this failure path.

### Other requirements assessed

No other concrete Spec finding was identified in this round:

- The adapter is the supplied complete implementation with only the documented
  FDSA directory-layout adaptation. It derives paths from its own file, hashes
  the exact QEMU/Lean/Lake executables, uses byte-identical Lean/Lake payload
  copies in one overlay, and supplies explicit launchers for both parent and
  child compiler routes. It refuses unexpected existing overlay contents.
- The overlay leaves the official distribution and all repository pins alone,
  clears inherited Lean selectors, preserves library/source/tool links and
  places writable runtime/cache state in the task directory. The guide explains
  relocation and why copied payloads and explicit cache execution are needed.
- The recovery instructions contain exact acquisition URLs/digests, a complete
  included adapter, safe dependency-source acquisition without resets, the
  matching source candidate, and the actual cache command form. The QEMU signed
  release/index/package/executable chain and original trust input are retained.
- `REQUEST.md` preserves the full FDSA authority and scopes the environment
  exception. `checkpoint.py` changes only generated recovery guidance; its
  existing complete control-directory copy includes the new recipe/tooling and
  evidence. No chapter, proof policy, source pin or audit-guard change is part
  of this diff.
- The guide distinguishes environment smoke, cache work, complete candidate
  verification and final acceptance. It keeps local tickets/no GitHub writes,
  all four open C1 Spec findings, both independent final axes and immediate
  `--verify-candidate HEAD`. It does not present the supplied guide's other
  checkpoint as part of this recovery lineage.
- The foreground recorder fixes the specifically observed detached-launch
  limitation and explicitly records missing outcomes as unknown. Its final
  successful-process state is command evidence, not an acceptance decision.

### Validation and remaining limits

`launcher-smoke.json` records twelve actual zero exits using the exact reviewed
adapter hash `8bc54deea672a0ff7928d1de8f839ee97963349c4d97cae13e4ac2257b06ec3f`.
It includes the exact Lean 4.35.0/Lake 5.0.0 identities, bare and Lake-child
routes, and two real compilations of the same Init-only theorems. Both proof
outputs have the same SHA-256 and report no axioms. The authentication and
post-smoke records retain unchanged original/copy executable digests and all
nine exact clean dependency revisions. These results support the environment
adapter; they are not a whole-project proof audit.

The real cache-tool build through the reviewed foreground recorder is recorded
under `provenance/qemu-cache-build-20261103-r1/`. At this round's inspection,
`start.json` and live progress/log existed but `result.json` did not. No cache
pass, recorder terminal pass or complete environment readiness is inferred.
The earlier detached attempt remains separately preserved without a terminal
claim. The running invocation must finish without modification or duplication;
a successor recorder requires its own matching evidence.

The full guarded all-module/audit command remains the later Chapter 1 gate.
Missing C1 full validation does not itself prevent an environment-only review,
but no conclusion here closes C1 or SPEC-001/002/003/V001. Factual current-status
bookkeeping is outside these five immutable implementation paths and must agree
with the actual outcomes included in the eventual checkpoint.

Only this review report was written. No compiler/cache operation, source edit,
Git mutation, external write or extra review agent was started by this reviewer.

## Round 2 — corrected recorder

**Current outcome: Blocked only on the pending real cache/recorder terminal
evidence. Concrete unresolved Spec findings: zero.**

Candidate: `5fe6d4f7cdac2761c7c3622d26479282cfb7fa1b`, against the unchanged
fixed base `900614e27f7d3dfffd9a29139884a8f1a4fce8d3`. The complete five-path
scope remains unchanged. The snapshot is clean and the base remains its merge
base. The five live artifacts again match the candidate's recorded hashes.
The round-1 whole-scope assessment is retained; its only subsequent changes
are the recorder correction and an explicit `gpgv` prerequisite in the guide.

**ENV68-SPEC-001 is fixed with review evidence.** The progress-save and log-stat
operations are now inside an exception guard. At most five diagnostics are
retained, and execution then continues to the same owned child's wait. Neither
the command nor the subprocess creation is retried. The actual exit is still
written to the primary result before final optional bookkeeping, now with the
bounded progress-error evidence included. This directly fixes the failure
identified in round 1 without changing acceptance policy.

The narrow actual exercise is retained under
`provenance/environment0068-recorder-progress-failure/`. I read the assessment,
result, full log and the exact executed heredoc body saved as `harness.py`.
The harness's provenance explicitly states that its source was saved after the
execution and was not rerun. Its independently recomputed SHA-256 is
`a187331db7e79160df0d7e2ac709fd0266f92e449c2c63b2c0014d38807c0f69`.

The harness loads the actual corrected recorder, replaces only `save` for
`progress.json` with an `OSError`, and invokes one child with a create-exclusive
marker and exit 7. It checks that injection occurred, `execute` returned 7,
the durable result recorded exit 7/state failed, one progress diagnostic was
retained, the expected marker/log contents exist, and the formal candidate
remained clean. The recorded source SHA-256 is exactly the candidate recorder's
`f84384210851b0fd1999a323aa693eab8d464fa82f344446bd04b9e61d78c686`.
The read 28-byte closed log matches its recorded SHA-256
`ad324837620c36a7160a3daaf1424e68b3920e349ea01b8ef83b70b8f356b492`.
This is a targeted failure-path test, not formal-project validation.

No additional concrete defect was found on the full corrected scope.
The unchanged adapter's prior actual smoke evidence remains matched by hash.
The real cache build already underway uses its previously loaded recorder;
its future result must be attributed to that invocation, not described as
running the corrected source retroactively. Its terminal evidence remains
pending, so this round does not yet declare the complete environment scope
Passed. No command was rerun by this reviewer.

## Round 3 — native environment continuation

**Outcome: Passed for the bounded environment/recovery-tooling scope.**
New concrete Spec findings: **0**. Unresolved Spec findings: **0**.
ENV68-SPEC-001 remains fixed with the round-2 evidence and unchanged recorder.

### Candidate, request and complete scope

- Fixed base and independently confirmed merge base:
  `900614e27f7d3dfffd9a29139884a8f1a4fce8d3`.
- Candidate: `9f673480206912d7df4a1dcc2b09ca7527bb0275`.
- Previous candidate: `5fe6d4f7cdac2761c7c3622d26479282cfb7fa1b`.
- Snapshot repository: `environment-review-0068`, observed clean.
- Full scope is the eleven paths in `environment-native-snapshot.json`: the
  original five artifacts, `tooling/native_toolchain.py`, compatibility C source
  and shared library, and the three retained native-check harness sources.
- All eleven live artifact hashes and immutable candidate blob hashes were
  independently compared with the snapshot manifest and match.

The native request in `provenance/native-environment-20261103/user-request.json`
asks for an alternative to the slow emulated route. Frozen `REQUEST.md` and
`ENVIRONMENT.md` correctly preserve that steering while retaining the full
FDSA task, exact official compiler/dependencies, local recovery workflow and
every formal acceptance gate. QEMU is now historical fallback, not the
preferred route. Its self-contained guide is actually retained at
`provenance/qemu-environment-20261103/ENVIRONMENT0068.md`; its recomputed hash
matches the former reviewed guide's
`b420a676acd44d47ae78f10d5923bcc9397affeecae811993a3bd7f1a64d461f`.

I reviewed the complete new eleven-path scope from the fixed base, retaining
the unchanged prior source/evidence assessments and examining the entire native
adapter, shim, harnesses and documentation. No unrelated source or draft branch
is silently included or discarded.

### Native behavior and its stated domain

The C library attempts the real `SYS_readlink` first. Successful calls and
errors other than ENOENT return directly. Fallback is limited to the literal
`/proc/self/exe` or the current process's exact numeric executable-link path.
It obtains the current process's `AT_EXECFN`, requires an absolute path that
can be canonicalized and opened with ELF magic, and returns at most the caller's
capacity without adding a NUL. Other process paths and unrelated queries retain
their actual syscall behavior. The callback does not replace file-open,
serialization, theorem/kernel, axiom, process-exit or build-result functions.

The documented domain is consequential and appropriate: normal absolute
launches of stable ELF files. Relative startup paths and interpreted scripts
are explicitly rejected by fallback; the source also excludes explicit loader
invocation and does not claim a general `/proc` implementation. The normal
adapter launch resolves an absolute executable, while retained tests establish
the actual Lake-child compiler, explicit cache and check-script entry routes.
No claim of universal syscall transparency or safety for arbitrary invalid
C-call arguments is needed to approve these defined trusted tool invocations.

`native_toolchain.py` checks Linux/x86-64 and the exact official Lean/Lake,
shim-source and shim-binary digests on every invocation. It clears inherited
Lean selectors, sets the official prefix/libraries and native PATH, preserves
the preload for descendants, and refuses an unexpected existing preload or
audit-library setting. The additional runtime dependency is explicit in source,
documentation and execution evidence. The official executable bytes remain
unchanged; no fabricated compiler identity, kernel bypass or source-policy
exception is introduced.

The native guide includes the complete source and exact 15984-byte library,
compiler/build command, source and binary digests, exact official distribution
reacquisition, all nine pinned dependency-source acquisitions, native cache
commands, relocation layout and full formal acceptance sequence. A different
compiler/target producing different library bytes requires its own reviewed
evidence, rather than an unnoticed digest replacement. `checkpoint.py` now
points recovery to that native guide and retains the QEMU fallback.

### Matching actual evidence

- `native-library-build.json` records successful compilation from source
  `80c1d0e92d7c5c258f32ce3709736bf969c6a24148287f99b238324d7bfbcfb6`
  to the exact binary
  `65910335cb5a2a4359e9ebf7dae4de1da7a48cdbf9dee5eabe82c3e4b02d88a9`,
  using the documented GCC invocation. Its dynamic-symbol evidence identifies
  `readlink` as the sole defined global function export.
- I read the executed boundary-harness source and retained results. Tests
  compare intercepted and raw syscall observations for unaffected symlinks,
  regular/missing files, another process and own cwd; exercise both own-exe
  forms, three-byte truncation, guard bytes and zero capacity; and distinguish
  absolute ELF, relative ELF and interpreted-script launches. The evidence
  accurately identifies which output is a retained summary of an actual run.
- `run_native_smoke.py` and `native-smoke-results.json` match the exact reviewed
  adapter and shim hashes. All ten commands exited zero, including official
  version/hash/prefix observations, Lake-child path/preload propagation, real
  bare and Lake-child theorem compilations, and native cache startup. Both
  actual proof files independently recompute to the same 6824-byte SHA-256
  `fbf279c5128799661a3f3087d27f139d4da4944e9061ae0c522fce3af38bb980`
  as the prior QEMU outputs. The reported theorem axioms are empty. All nine
  dependency revisions and the formal candidate remained clean and exact.
- The historical QEMU cache build r2 has actual exit 0 after 161.54 seconds,
  with the corrected recorder and a complete 588-byte successful log. I read
  that log and independently verified its matching SHA-256
  `ebaf6dc29a83d012474cc6c70c9f9e9f97c6d5be1bc11049d619499d8ce73dac`.
  This closes the earlier pending real recorder/cache-build evidence without
  rewriting r1's separately retained interruption and unknown child outcome.
- Native cache retrieval has actual exit 0 after 70.79 seconds. I read its
  full 14180-byte log, which ends with all 9031 requested files decompressed,
  and independently verified SHA-256
  `0d8d4438cf46da7f099a5db77a32a67ae05121e2e8656481449afcca320e405f`.
  The result records clean formal candidate `07e480f` and no verification
  record. It uses the default pinned Mathlib cache scope and no unsafe flag.

These concrete executions establish the requested usable native environment
and the bounded external recorder behavior. Their timings describe those
executions, not a whole-project performance guarantee. No repeated compiler,
cache command or test was started by this reviewer.

### Formal acceptance remains separate

The full project gate has not run in the supplied native evidence and receives
no acceptance credit from environment or cache success. The official compiler,
repository pins, checker and proof policy are unchanged; cold project outputs
can be validated through the full ordinary guarded route, with both integrity
phases and exhaustive audit retained. Actual new integrity evidence or a changed
validator still invokes the existing runbook and applicable README checks.

Original formal base `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`, candidate
`07e480f6ec9958d4975bb90151005b84f2907614`, fourteen-path chapter scope,
requirements and SPEC-001/002/003/V001 remain untouched. Both independent final
Chapter 1 reviews and immediate candidate verification are still required.
The caller must bind the eventual checkpoint's delivered environment files to
this reviewed candidate and keep factual status bookkeeping truthful. This
environment-only Passed outcome authorizes no chapter closure or scope reduction.

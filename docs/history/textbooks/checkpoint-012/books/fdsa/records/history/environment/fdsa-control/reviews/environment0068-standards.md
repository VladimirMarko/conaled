# Environment 0068 — independent Standards review

## Round 1: source assessment, validation pending

**Outcome: Blocked on matching recorder terminal evidence.** Independently
identified Standards findings: **0**; worst Standards issue: **none**. This is
not Chapter 1 acceptance or a final review of any Lean formalization.

- Snapshot repository: `/workspace/scratch/6bb268f9336f/environment-review-0068`.
- Fixed base and confirmed merge base:
  `900614e27f7d3dfffd9a29139884a8f1a4fce8d3`.
- Candidate: `b8ce485c872ee4c1b227b318b5b5854a13d11b83`.
- Comparison: `git diff BASE...CANDIDATE`, all five paths: `ENVIRONMENT.md`,
  `REQUEST.md`, `checkpoint.py`, `tooling/pinned_toolchain.py`, and
  `tooling/record_command.py`. No task artifact in that scope is excluded.
- Commit list: `9eb543e` (environment recovery), `b8ce485` (foreground recorder).
- Unchanged formal candidate:
  `07e480f6ec9958d4975bb90151005b84f2907614`, original formal review base
  `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.

The snapshot checkout was clean. All five file hashes were independently
compared against `environment0068-snapshot.json` and the actual control files;
all matched. Candidate source was read through its immutable Git snapshot.

## Standards and authorization applied

Read conaled's AGENTS, README development/build/audit rules, shared review loop
and code-review heuristics. The retained Chapter 1 Standards report supplies
the earlier artifact-matched regression and routine-mode applicability ruling.
The complete frozen request and retained supplied setup guide were consulted.

The user's explicit Nix exception permits acquisition of the exact required
program versions separately. The added request paragraph preserves that
limited exception, the FDSA source lineage, and all formal acceptance rules.
It does not import the other book's checkpoint or acceptance state. Local
tracking and recovery checkpoint delivery continue to replace GitHub writes.

## Source assessment

The external adapter checks the exact QEMU, Lean and Lake executable digests
before preparing its overlay. The Lean/Lake copies retain official bytes;
the shell launchers quote executable paths and forward arguments without a
shell reconstruction of the caller command. The original distribution is
read-only input to this helper. Remaining entries use relative links, while
the guide correctly requires regeneration of absolute-path launchers after
relocation and documents refusal to overwrite unexpected existing entries.

The wrapper clears conflicting inherited selectors, supplies Lake's supported
installation override, and selects the official shared libraries. It wraps
both the parent's bare Lean path and Lake's child invocation. Its task-local
cache/configuration/temporary paths and explicit post-adapter concurrency
override agree with the actual described layout. No Lean source, compiler
bytes, proof policy, manifest or project build script is modified.

Acquisition instructions retain the official Lean archive hash, QEMU package
and executable hashes, and the complete authenticated Ubuntu metadata chain.
The source guide, complete adapted helper and provenance are all included in
the control directory that the unchanged checkpoint copy operation captures.
No hidden previous-checkpoint dependency remains in the operative instructions.
The checkpoint generator's changed text points at CURRENT and ENVIRONMENT;
its source/history capture algorithm is unchanged in this diff.

The recorder is explicitly process accounting, not an acceptance certificate.
It creates a unique invocation directory, checks the exact clean candidate,
captures the complete child stream, records the actual wait result before its
post-run Git/hash/verification-copy work, and distinguishes missing terminal
evidence from a pass. Foreground execution addresses the observed detached
worker failure without rewriting that earlier evidence. This source assessment
does not establish untested error handling or a complete current invocation.

One editorial prerequisite gap was sent to the coordinator: the guide invokes
`gpgv` but does not list it in its supporting-tool paragraph. It is not a new
test gate. The independent Spec axis separately owns its recorder-error-path
finding; this Standards report neither duplicates nor closes that finding.

## Validation inspected

`provenance/qemu-environment-20261103/launcher-smoke.json` binds the executed
adapter hash to this candidate's adapter. Its twelve recorded commands all
exit zero. They check QEMU and exact Lean/Lake versions, commit identity,
overlay prefix and Lake's child selection, plus actual theorem compilation
through both bare Lean and `lake env lean`. Both 6824-byte proof artifacts
were independently hashed and match the recorded identical digest
`fbf279c5128799661a3f3087d27f139d4da4944e9061ae0c522fce3af38bb980`.
The theorem runs print no axioms for the two smoke declarations. This is
environment/kernel-startup evidence, not the project audit.

`post-smoke-source-verification.json` preserves clean exact formal candidate,
unchanged toolchain/manifest/configuration hashes, all nine exact clean Git
dependency revisions, and matching official/overlay Lean and Lake bytes.
`qemu-acquisition.json` retains the successful signed-release verification,
matching package-index and package hashes and exact extracted QEMU digest.

At this review's bounded read, the real cache build under the new foreground
recorder had start/progress/log records but no `result.json`. The partial log
was at task 29/42; this is not terminal success. The project `.lake/build`
directory did not exist at that observation. The actual exit and closed log
remain required to complete recorder validation. No duplicate smoke, cache
build, compiler, project checker or fixture was started by this reviewer.

## Applicability of the next formal check

The intended next acceptance run is the complete ordinary guarded candidate
command through the external adapter, followed by the retained two-axis
review and immediate candidate-record verification. This environment recipe
does not change the formal compiler version, dependency pins, source/audit
implementation, root selection or integrity algorithm. The recovered project
outputs are cold, so there is no reused project cache from the old environment
whose validity this route would assume. All integrated project modules must
compile and the exhaustive audit must still run.

Under these observed conditions, the ordinary route is appropriate; no extra
full fresh run or unrelated validator regression suite is created merely by
the external executable-path adaptation. A later concrete stale-output or
integrity incident, configuration/pin/validator change, or explicit requirement
must still trigger the applicable README and incident procedure. This ruling
does not waive either integrity phase, any integrated module, the exhaustive
audit, immutable-candidate evidence, independent final reviews or immediate
`--verify-candidate`.

All Chapter 1 requirements and SPEC-001/002/003/V001 remain open. No chapter,
appendix or shared unit receives acceptance credit from this environment review.

## Round 1 disposition

Await the corrected immutable candidate requested by the independent Spec axis
and matching validation for that correction, plus the actual cache-build exit
and closed log. Retain this complete scope and fixed base in the next round.
Current status bookkeeping outside this implementation snapshot must describe
only observed setup/cache/review outcomes and cannot expand this approval scope.

## Round 2: corrected recorder and prerequisite

Fixed base remains `900614e27f7d3dfffd9a29139884a8f1a4fce8d3`. The corrected
candidate is `5fe6d4f7cdac2761c7c3622d26479282cfb7fa1b`; the complete five-path
scope is unchanged. The diff from round 1 adds `gpgv` to the prerequisites and
makes optional progress observation best-effort. Both the progress save and
its log-size query are inside the exception handler; up to five errors are
retained for the final result. The owned-child wait remains outside this
optional observation and the actual exit still precedes post-run bookkeeping.

The matched failure-injection evidence under
`provenance/environment0068-recorder-progress-failure/` identifies recorder
SHA-256 `f84384210851b0fd1999a323aa693eab8d464fa82f344446bd04b9e61d78c686`.
It injects an OSError into every progress save while permitting result writes.
The actual one-shot child exits 7, the recorder returns and preserves 7 with
state `failed`, the log contains its expected marker, and final formal source
remains clean at `07e480f`. This is a narrow meaningful check of the reported
failure path; it grants no project-validation credit. Spec owns the formal
disposition of ENV68-SPEC-001.

The previous identical adapter/authentication/smoke evidence remains relevant;
the helper, official bytes and pins did not change. No new independent Standards
finding arose. **Standards remains Blocked only on the pending actual cache-build
terminal evidence and reconciliation**, not on additional compiler fixtures or
the unperformed Chapter 1 acceptance check. The current real cache run uses the
already-loaded pre-fix recorder; its unchanged successful observation path can
support the adapter/cache command while the focused check above covers the new
error handler. It must not be relabeled as an execution of the new recorder bytes.

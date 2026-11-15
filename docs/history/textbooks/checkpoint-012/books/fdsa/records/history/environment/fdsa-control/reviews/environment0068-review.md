# Environment and recovery tooling review — checkpoint 0068

## Scope and fixed identities

This is the implementation/review loop for the user-authorized exact-version
environment recovery and its self-contained checkpoint instructions. It is
separate from final Chapter 1 review and grants no formal acceptance.

- Snapshot repository: `/workspace/scratch/6bb268f9336f/environment-review-0068`.
- Fixed base and confirmed merge base:
  `900614e27f7d3dfffd9a29139884a8f1a4fce8d3`.
- Round 1 candidate: `b8ce485c872ee4c1b227b318b5b5854a13d11b83`.
- Diff: `git diff BASE...CANDIDATE`, all five task paths:
  `ENVIRONMENT.md`, `REQUEST.md`, `checkpoint.py`,
  `tooling/pinned_toolchain.py`, `tooling/record_command.py`.
- Included commits: `9eb543edce6d3c2ae5395adc31462b15f7286a9f` and
  `b8ce485c872ee4c1b227b318b5b5854a13d11b83`.
- Exact file hashes and retained snapshot bundle: `environment0068-snapshot.json`.
  The coordinator verified all five snapshot bytes and live control-file hashes
  against that record before dispatch. The snapshot checkout was clean and its
  diff nonempty. No task artifact in this five-path implementation is excluded.

The formal project remains at candidate
`07e480f6ec9958d4975bb90151005b84f2907614`, original review base
`7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`. Source, dependency pins,
compiler bytes, checker, guard and proof-audit policy are outside this change
and must remain unchanged. SPEC-001/002/003/V001 remain open. All source drafts
and the full-book objective remain preserved.

## Requirements and supporting evidence

The frozen `REQUEST.md`, governing conversation instruction recorded in
`provenance/qemu-environment-20261103/user-request.json`, and complete original
`user-supplied-setup-guide.md` supply the intended requirements. The supplied
guide authorizes separately acquired exact tool versions when Nix is unavailable.
The user's requested adaptation must be independently reproducible from the
next FDSA checkpoint, without its unrelated checkpoint039 or a prior chat.

The environment must run the authentic pinned Lean/Lake through both bare and
child invocation paths, preserve all source/pins/acceptance rules, document its
authentication and workspace layout, and retain real command outcomes without
converting missing terminal evidence into success. Recovery instructions must
describe actual state and retain the local-ticket/no-GitHub constraints.

Evidence supplied before dispatch includes authenticated QEMU acquisition,
official Lean acquisition, exact clean dependency revisions, adapter-layout
provenance, twelve successful startup/path/kernel checks and equal real proof
artifacts through bare Lean and Lake's child Lean. These are environment checks,
not the Chapter 1 full build/audit. The relevant evidence files are listed in
`environment0068-snapshot.json`.

The corrected foreground recorder is being exercised by the real cache-tool
build in `provenance/qemu-cache-build-20261103-r1/`. Its start record establishes
the actual owned command at the clean formal candidate. At review dispatch
its terminal result was pending. The earlier detached launch's lack of
start/result evidence is preserved and is not reclassified as a successful run.

`CURRENT.md`, `STATUS.md`, `tickets/FDSA-ENV.md`, `tickets/FDSA-001.md` and
`tickets/INDEX.md` are associated factual execution bookkeeping outside the
five-path implementation snapshot. Root may update their current state only
from actual subsequent outcomes. They do not change the frozen implementation
scope or override the formal acceptance gates.

## Independent review round 1

Both axes were dispatched on the exact same immutable candidate and full
requirements, using the repository's `code-review` and shared review procedure.
The coordinator reconciles their findings and does not perform a third axis.

| Axis | Reviewer | Outcome |
| --- | --- | --- |
| Standards | `/root/chapter1_recovery_review/environment0068_standards` | Pending |
| Spec | `/root/chapter1_recovery_review/environment0068_spec` | Pending |

Reports: `environment0068-standards.md` and `environment0068-spec.md`.
Findings, corrections and final validation evidence will be retained here;
neither a pending outcome nor missing validation counts as approval.

### Round 1 findings relayed for correction

- **ENV68-SPEC-001 — moderate, unresolved:** nonterminal `progress.json`
  bookkeeping and the accompanying `log.stat()` run unguarded before each
  `child.wait`. An ancillary I/O failure can terminate the recorder while its
  owned command continues, losing observation of the actual exit. The Spec
  reviewer requests best-effort progress bookkeeping while preserving the sole
  owned wait, no command retry, and exit recording before optional final
  bookkeeping. Root received the finding and the justification for one targeted
  progress-write-failure check; this is not an unrelated fixture gate.
- The Standards reviewer noted the guide's `gpgv` invocation despite omission
  from its supporting-tool prerequisites. This minor completeness observation
  was relayed with the recorder correction; the axis will record its final
  disposition independently.

The ongoing cache-tool build remains separate actual evidence. No source pass,
successful terminal outcome or final environment approval is inferred here.

## Independent review round 2

Correction candidate: `5fe6d4f7cdac2761c7c3622d26479282cfb7fa1b`.
The fixed base remains `900614e27f7d3dfffd9a29139884a8f1a4fce8d3` and
both independent axes retain the full five-path review scope. The snapshot
checkout is clean and the base is still its merge base. Only the guide's
`gpgv` prerequisite and the recorder's optional progress handling changed
relative to round 1.

Root accepted ENV68-SPEC-001. The corrected recorder continues the same owned
child wait after a progress/stat bookkeeping exception and retains bounded
diagnostics in its terminal result. A targeted actual exercise is preserved in
`provenance/environment0068-recorder-progress-failure/`: every progress-sidecar
write raises an injected `OSError`, the single child emits its marker and exits
7, and the recorder returns and preserves exit 7 with the closed-log digest.
Its source identity is
`f84384210851b0fd1999a323aa693eab8d464fa82f344446bd04b9e61d78c686`, matching
the corrected snapshot. The result records `failed`, never success, and the
formal candidate remains clean. The coordinator read the assessment, actual
result and complete closed log, then forwarded them to both retained reviewers.
Finding closure remains for the independent Spec reviewer to determine.

The ongoing real cache-tool build uses its already-loaded earlier recorder;
it is not restarted, and its eventual evidence must identify that distinction.
Its terminal outcome is still pending at round 2 dispatch. Both independent
reviewers were asked to reassess the full corrected candidate, retaining the
earlier analysis and pending terminal-evidence boundary.

### Round 2 finding disposition

The independent Spec reviewer closed **ENV68-SPEC-001: fixed with review
evidence** on `5fe6d4f`. It read the retained exact executed harness, its
post-execution retention provenance, source identity, one-execution marker,
actual/recorded nonzero exit and matching complete-log hash. The harness SHA-256
is `a187331db7e79160df0d7e2ac709fd0266f92e449c2c63b2c0014d38807c0f69`.
No rerun or repeated child was introduced to supply this evidence.

Standards independently confirmed no new finding, the repaired progress-error
boundary and the explicit `gpgv` prerequisite. Both axes retain zero unresolved
source findings at the correction candidate. Their overall outcomes remain
**Blocked** only on the actual real cache-build/recorder terminal evidence;
the running pre-fix loaded recorder is attributed separately from the corrected
error-path exercise. The ordinary full guarded formal-check route remains the
retained Standards disposition, without additional unrelated test gates.

## Current disposition for checkpoint 0068 capture

The implementation candidate is frozen at
`5fe6d4f7cdac2761c7c3622d26479282cfb7fa1b`, against fixed base
`900614e27f7d3dfffd9a29139884a8f1a4fce8d3`, covering all five implementation
paths. Both axes have completed their corrected source assessment:

| Axis | Unresolved source findings | Worst unresolved issue | Current outcome |
| --- | --- | --- | --- |
| Standards | 0 | None | Blocked on actual cache-build/recorder terminal evidence |
| Spec | 0; ENV68-SPEC-001 fixed with reviewed evidence | None | Blocked on actual cache-build/recorder terminal evidence |

The verified runtime identity, authentic binary provenance, actual bare/Lake
theorem checks and corrected recorder's targeted nonzero-exit exercise are
preserved. The real cache build remains an owned running invocation; its
partial task counter is not a successful terminal result. No full project
gate has started in this recovered environment, and no environment completion
or Chapter 1 acceptance is claimed.

Checkpoint 0068 may preserve this truthful unfinished state. Saving it is a
durability action, not review approval or formal acceptance. This coordinator
record and the two current conditional reports are held unchanged during
capture; later terminal evidence must be reconciled explicitly after saving.

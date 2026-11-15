# Facade author record

The assigned task is the paired journal trial. This submission uses the permitted
facade and generic baseline definitions. No other submissions, private oracle,
preparation evidence, or orchestration records were inspected. No delegation or
external assistance was requested or received.

The implementation retains `E` in `change E := ⟨nativeMap, E⟩`. The helper
`carrier_eq` proves equality of carrier equivalences by their forward maps,
using `codeIso_action`; it does not identify contraction witnesses. The
`length_preserved` and `sum_preserved` helpers use whole-record extensionality
and `Preserves.of_eq`. All helper versions are retained with the submission.

Statement review: both universal preservation results compare complete packages
with the independently defined targets. Reversal preserves length and sum;
reversing an append of 1 gives prepend of 1. Dependent proof fields are retained
through record equality and proof irrelevance. Each native object uses the
original supplied contraction. Section exactness is definitional; section
recovery uses the facade's native recovery theorem. Path recovery uses the fixed
structure-identity equivalence. Rejection tests the invariant at `([1],[])`,
where the source invariant is false and the proposed target invariant is true.

The retained examples use the decoded-target theorems to check the requested
transition and the two pairs separating length from total. Their expectations
come from direct list calculations. The supplied task and the existing public
calibration already expose the relevant construction requirements; no artificial
failing mathematical obligation was added.

Attempt 01 contains the initial complete submission. Validation uses the exact
serialized, CPU-pinned, low-priority environment wrapper from `validation.md`.
The queue timestamp precedes lock acquisition; the first compiler-log timestamp
records acquisition. Full output and exit status are retained per attempt.

Model identity, token usage, and sampling configuration are unavailable in this
author session. No heartbeat limit was changed. Host load and temperature were
not measured. No interruption has occurred. This trial's focused checker does
not replace the coordinator's private replay or later integrated proof audit.

Coordinator clarification during attempt 01: the shared lock is occupied by an
integration audit. The coordinator instructed retaining the current attempt and
waiting; this is queue/host wait, not an author-performance measure or trial
blocker. No mathematical guidance or task change was supplied.

Attempt 01 failed with default-heartbeat timeouts while elaborating both path
constructors (then cascading unknown path names and recovery timeouts). The two
concrete separating examples also failed to synthesize Decidable through the
opaque target definitions. Attempt 02 supplies explicit source/target arguments
to the facade path and recovery constructors, and simplifies the concrete target
definitions instead of asking `decide` to unfold them. Heartbeats remain default.
The preservation helpers, section declarations, decoded equalities and rejection
produced no compiler errors in attempt 01.

Attempt 02 still timed out checking facade path construction against the native
result annotation; explicit endpoints did not repair that conversion. The
concrete examples now passed. Attempt 03 infers the path definition's result
type from the fully applied facade constructor (as public calibration does),
and states recovery using the native equivalence's `symm_apply_apply` directly.
The prescribed interface checker will still check the exact native path types.

Attempt 03 constructed the inferred facade paths, but using them as native
paths in recovery statements still timed out during conversion. Attempt 04
constructs paths through the baseline `uaStructureIdentity.symm` using the same
preservation witnesses. Facade section construction, recovery, and transport
remain in use. This avoids the costly facade/native path type conversion at the
required boundary without changing the mathematical contract or limits.

Attempt 04 passed all three commands with exit status 0: compilation of
`TrialTask.lean`, compilation of `AuthorSubmission.lean`, and checking
`ExpectedInterface.lean`. Its complete compiler log contains no Lean errors or
warnings. The final source is identical to the retained attempt 04 snapshot.

The initial author attempt is complete after four compiler passes. There is no
remaining mathematical or interface blocker. The observed facade/native path
conversion timeout is retained as an author-usability limitation; baseline path
construction supplies the required native objects without a heartbeat increase.
Private acceptance replay and integrated audit remain coordinator work under
the trial validation instructions. No source/API/task files were modified.

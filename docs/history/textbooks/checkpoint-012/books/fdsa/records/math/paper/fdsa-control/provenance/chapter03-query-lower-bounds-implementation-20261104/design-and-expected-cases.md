# Coordinate sensitivity and query lower bounds — source preparation

Author: `/root/chapter03_query_lower_bounds`. Allocated base is accepted Chapter 2
`2da5708478a1d943a9214b5b386ec2db16cd9eca`; branch
`work/fdsa-ch03-query-lower-bounds` in the existing `conaled-ordinary-merge`
worktree. The coordinator's starting-state and allocation-result records remain
unchanged. This is one assignment in the existing full-book implementation and
review loop.

## Exact intended scope

The frozen 83-row Chapter 3 inventory has SHA-256
`eda51a6cd8bac41df1f97ab03386b003e1cae5ed0db5320414265027074360ed`.
The assigned rows are C03-052 and C03-081–083. The July 27, 2026 PDF identifies
Exercise 3.4 on printed pages 33–34 and the optimality discussion on page 32.
The relevant source text and the complete assigned inventory rows were read.
The source theorem is zero-based integer-list coordinate sensitivity; it is
separate from the additional deterministic coordinate-query model.

New source is restricted to `Applications/Selection/CoordinateSensitivity.lean`,
`Applications/Selection/CoordinateQueries.lean`, and matching `Examples` files.
No shared root, mapping, control status, review report, dependency, compiler,
cache, or runtime input is being edited. The existing accepted `RankedAt`,
`ordered`, `ranked_iff_index`, and `ranked_strict_counts` are the semantic API.
No unaccepted CountRank, pivot, or randomized-execution module is imported.

## Mathematics chosen before source implementation

For a distinct integer list, let a be the selected value. If the coordinate
being replaced is at most a, replace it with a fresh integer greater than every
input entry. The number of values strictly greater than a increases by one.
Otherwise replace it with a fresh integer below every input entry; the same
strict count decreases by one and was positive. The replacement stays distinct,
so the already accepted exact strict-rank count contradicts preservation of a.
Lean's standard `List.countP_set` and `List.Nodup.set` provide the update laws;
the finite upper and lower witnesses use elementary integer max/min induction.
The externally stated sensitivity conclusion does not assume a distinct
replacement or require callers to supply an adversarial value.

The query operation is a function from the prior index/value transcript to
either a returned value or a next `Fin n` coordinate. History is newest first;
the completed run records its queries chronologically. `Runs` is an inductive
finite execution relation whose query constructor obtains the answer only from
the requested coordinate. The operation itself never receives the input.
Termination on every input and correctness of every terminating run are separate
laws. Replay follows by induction when another input agrees at all coordinates
in the actual transcript. Correctness on all integer inputs plus the actual
sensitivity theorem forces coordinate coverage on each distinct input.

Every occurrence in the query trace is charged, including repeated coordinates.
A positive per-query tariff yields at least n charged work, and an explicit
resource contract may transfer that lower bound to another observation. The
actual median-of-medians implementation's read/source-tariff correspondence is
not available in this assignment: C03-083 will remain partly open until that
separate actual-algorithm bridge is proved. No physical-runtime, free-bulk-call,
or randomized-competitor lower bound is claimed.

## Independently expected examples and connections

- For `[8,1,5]`, changing any valid coordinate can change the middle value 5;
  both the zero-based book observation and one-based public selector consume the
  general sensitivity theorem.
- The singleton case must remain sensitive, and an out-of-bounds rank must not
  be included in the injection or sensitivity claim.
- A one-coordinate protocol asks its sole coordinate then returns that answer.
  It terminates and is correct for every integer input, making the model's
  correctness and totality assumptions demonstrably satisfiable.
- A value-dependent one-coordinate protocol repeats its query on a negative
  answer, but returns immediately on a nonnegative answer. Thus negative inputs
  take two charged queries and nonnegative inputs one; repeated queries are
  not collapsed into a set-size cost.
- A two-coordinate minimum protocol reads coordinates zero and one and returns
  their minimum. Its actual transcript consumes the universal correctness,
  coverage, and lower-bound results on a distinct input.
- Changing an unqueried coordinate preserves an already terminating transcript
  and output by replay; for a correct selector on distinct input the sensitivity
  result makes that situation impossible.
- A family of correct total protocols has, at every positive size, an actual
  distinct-input execution with at least n queries. A uniform worst-case query
  bound therefore has the usual linear asymptotic lower-bound consequence.

All Lean claims and examples are currently proposed source. Root alone will
compile immutable candidates in the qualified one-thread environment and
capture actual expanded types. No successful elaboration, audit, review or
acceptance is inferred from this preparation.

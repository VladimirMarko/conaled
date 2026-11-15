# Chapter 1 first-hit and rank-terminating iteration

The extension provides invariant preservation, uniqueness and a first-hit
characterization using Mathlib's standard `f^[n]` iteration. `runUntil` follows
the source equations under an explicit natural-valued rank that strictly
decreases whenever the loop continues. `runWhile` applies the complementary
guard convention. The rank supplies totality and is independent of the returned
state; it does not establish an operation count, a complexity class or measured
runtime.

`UntilSpec.map` transports any finite execution through a state interpretation
that preserves guards and commutes with continuing steps. It requires neither
injectivity nor a rank. `runUntil_map` combines that law with uniqueness for two
total executors. These direct function laws let ordinary callers use the shared
construction without packaging their state space into a new hierarchy.

## Source identity and declaration correspondence

The source is the user-supplied `adwh-checkpoint-335` compact recovery archive,
SHA-256 `9e8bee022149e8456c9c4ab318f3be0d5d7f8361c25e7409cfe1c12bf8eb812c`.
The payload member is `project/adwh-lean/ADWH/Chapter01/Iteration.lean`,
SHA-256 `869286b90db05b9ba8ca82e1b407bada42ce85de7e0c83b405776a8cf35c1c7d`.
It agrees with the previously recorded checkpoint-233 inventory. This
development reads the supplied successor and makes no new book-PDF claim.

Source names below are relative to `ADWH.Chapter01.Iteration`; destination names
are relative to the existing `Iteration` namespace.

| Source declaration | Destination and disposition |
| --- | --- |
| `UntilSpec`, `UntilSpec.stopping` | Existing conaled definitions/statements retained unchanged. |
| `UntilSpec.invariant` | Adapted under the same suffix; preservation is needed only when the guard is false. |
| `UntilSpec.first_hit` | Adapted with standard `f^[n]` in place of the source-local `apply`. It retains an exact finite iterate and all prior failed tests. |
| `UntilSpec.unique` | Adapted under the same suffix and reused by old-domain and new-loop clients. |
| `runUntil`, `runUntil_spec`, `runUntil_stops`, `runUntil_invariant` | Adapted into the existing owner with the same totality premise and independent first-hit relation. |
| `runUntil_first_hit` | Adapted with standard function iteration in its conclusion. |
| `runUntil_rank_independent` | Adapted; equality follows from shared first-hit uniqueness, not rank equality. |
| `runWhile`, `runWhile_spec`, `runWhile_stops`, `runWhile_invariant` | Adapted with the source complement-guard convention. |
| `fixed_point_requires_stop`, `identity_loop_has_no_rank`, `identity_loop_has_no_result` | Adapted; a supplied inhabitant witnesses the impossibility, avoiding an empty-domain conclusion. |
| `apply`, `applyTail`, `apply_spec`, `apply_succ_right`, `applyTail_eq`, `apply_add`, `apply_invariant` | Source-local fixed-count wrappers are not imported by this slice. Mathlib's standard iterator and its two successor equations are used directly for first-hit semantics. This is not an assertion of declaration-level replacement of every source wrapper. |
| No source counterpart | `UntilSpec.map` and `runUntil_map` are new shared interpretation laws, consumed by the pair-accumulator projection. |

The scope is the first-hit relation and rank-terminating loop family. Other
Chapter 1 partiality, lazy/infinite behavior, resource models and fixed-count
wrapper correspondence remain outside this slice. Arbitrary Haskell loops are
not asserted to admit a decreasing natural rank.

## Checked development cases

The initial missing connection was explicit: the existing shared relation
provided only the final stopping guard. It did not yet expose invariant
preservation, first-hit iterates, uniqueness, total execution or interpretation
transport. The examples use those new public results rather than independently
reducing the proposed loop outputs.

The cases are in `Examples.RankedIteration`:

| Case | Independent expectation and public results |
| --- | --- |
| `countdown_eq_zero` | Repeated predecessor stops at zero. Its strict-decrease proof is supplied, and `runUntil_stops` determines the result. |
| `countdown_other_rank` | Ranks `n` and `2*n+7` satisfy the same progress obligation and give the same result by `runUntil_rank_independent`. |
| `threshold_trace`, `threshold_first_result`, `threshold_first_hit` | From six, the states six/five/four fail the test `n ≤ 3` and three succeeds. An independently written finite trace and `UntilSpec.unique` determine the exact result, while `runUntil_first_hit` records all preceding failed tests. |
| `threshold_initial_stop` | Starting at two returns two immediately; uses uniqueness against the stop constructor. |
| `transfer_remaining` | Projecting the pair `(remaining, accumulated)` to its first component commutes with countdown; `runUntil_map` and the countdown result establish zero remaining work. |
| `transfer_conserved`, `transfer_result`, `transfer_example` | The invariant `remaining + accumulated = initial total` is preserved on continuing steps. `runUntil_invariant` plus the projection result yields `(0,n+total)`, concretely `(0,11)` from `(4,7)`. |
| `transfer_while_eq`, `transfer_while_conserved`, `transfer_empty` | The complementary while guard agrees by shared uniqueness; `runWhile_invariant` independently transports the conserved sum. An initial zero remainder returns `(0,7)`. |
| Divergent identity cases | A constantly false stopping test and identity transition have neither a decreasing natural rank nor a finite result. Both use the public impossibility laws on inhabited natural states. |
| `dijkstra_successful_results_unique` | Two successful executions of the actual existing Dijkstra target search, with possibly different fuels, return equal states. It composes `Dijkstra.Target.untilTarget_spec` with shared `UntilSpec.unique`, without changing that executor or assuming its fuel is a rank. |

## Statement review and validation scope

The stopping condition is tested before stepping; a zero-step execution is
valid exactly at a successful guard. First-hit quantification is existential
over a finite number of steps and universal over every smaller index. It makes
no conclusion about an infinite execution. Uniqueness compares executions with
the same initial state, deterministic transition and guard.

The executor's rank hypothesis is global on continuing states. Clients may use
an invariant subtype when their rank is meaningful only on a restricted domain;
this change does not silently assume that all raw states are valid. In the
retained clients the proofs cover the stated full domains. The pair
interpretation preserves the guard exactly, so projection cannot skip a source
stopping event. Its step equation is required only for continuing states.

Loop equality under distinct ranks is extensional equality of returned states,
not equality of execution costs or termination proof terms. While negates the
guard once, and its result satisfies the original while guard being false.
The divergent identity cases demonstrate why the rank premise cannot be omitted.

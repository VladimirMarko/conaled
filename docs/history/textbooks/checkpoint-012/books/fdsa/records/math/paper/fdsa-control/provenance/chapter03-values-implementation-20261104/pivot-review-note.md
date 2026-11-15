# Median-of-medians value handoff

This is the first uncompiled immutable development candidate for C03-021–026.
It remains within the existing 83-row Chapter 3 implementation/review loop.
The exact candidate and file identities are recorded in `pivot-candidate1.json`.
No focused compilation, elaborated-type inspection, complete candidate check,
audit, independent review approval, or Chapter 3 acceptance is claimed here.

## Intended mathematics and public connection

| Scope | Proposed public witnesses and connected cases |
|---|---|
| C03-021 | `lowerMedianValue` is the lower sorted occurrence on a proof-carrying nonempty list; its rank, membership, optional-adapter, and duplicate-aware count laws connect to the accepted selection interfaces. `chunkMedians` maps directly to payloads through standard `List.attach`. `medianOfMedians` is the existing optional lower median of those payloads. Its rank equivalence, exact failure law, membership and positive-size `PivotValid` theorem expose the specification pivot. The even pair `[2,7]`, two full chunks, duplicate chunks, empty input and size zero exercise these interfaces. |
| C03-022–023 | `chunkMedianGroups` filters attached chunks by a Boolean predicate on their medians and its Boolean complement, then projects the chunk payloads. Permutation, multiset sum, length sum and related-group count correspondence retain repeated chunks. The greater-oriented two-chunk case has one related and one complementary chunk. Six equal inputs retain a full chunk and a singleton chunk in the complementary multiset. |
| C03-024 | `medianOfMedians_median_counts` proves a non-strict natural half bound in both orientations. The source-error example uses `List.range 10`: chunk medians `[2,7]`, pivot `2`, one strictly greater median, and natural half-count one. `strict_half_is_false` states the actual failed strict inequality, and `corrected_non_strict_half` uses the universal corrected result. |
| C03-025 | `chunk_count_lt_of_median_ge` and `chunk_count_gt_of_median_le` bound a complementary chunk's strict contribution by `d/2`, including a short final chunk. The ordinary total contribution uses `List.countP_le_length` and the existing chunk-length bound. Size-five universal consumers expose the constants two and five. A private finite-sum lemma combines the two contributions without deduplicating either values or chunks. |
| C03-026 | `medianOfMedians_count_bounds` gives both strict-side bounds `q*m + (d-q)*(m/2)`, for `q=d/2`, `m=ceilDiv(n,d)` and positive `d`. `size_five_count_arithmetic` and `medianOfMedians_five_count_bounds` yield `ceilDiv(7*n+30,10)`. `ceil_nat_div` and `size_five_ceiling` prove exact correspondence to `ceilNat(7*n/10+3)` in an ordered floor field; the final theorem and Real consumers preserve the source rounding. Empty counts are zero for arbitrary pivot independently of optional failure. |
| C03-057 reuse | The positive general-size bound remains public, including rounding and a short final chunk. A size-one consumer recovers the half bound. No general-size execution-cost or cutoff result is claimed. |

## Statement review and limitations

The source statements and both private derivations were inspected in full
(tool readback `6cbea8`); the exact public-name list is in `pivot-precommit.json`.
There are 28 proposed core declarations, 27 consumer declarations, and two
private proof helpers. `MedianOfMediansStatements.lean` requests all 55 public
types with the pinned supported detailed pretty-print options. Its results
remain pending actual root-owned execution. The earlier 75 public declarations
and four source-file identities are unchanged.

Counts use strict comparisons and preserve occurrence multiplicity. There is
no `Nodup`, `Inhabited`, positive-parity, or full-final-chunk premise. The payload
median requires a nonempty proof; only members of the already proved nonempty
chunk list supply those proofs. The outer pivot retains `Option`, with failure
exactly at zero group size or empty input. Existence for every nonempty input
at positive group size is a separate public claim. Both universal side bounds
are conditioned on a successful pivot, and an independent empty-count consumer
covers the source's empty-input observation.

The mathematical pivot uses sorting through the accepted median specification.
This introduces no fast nested selection algorithm and no cost claim. The future
fast realization must prove that its recursive payload median computation has
this value and must account for its own traversals. The `List.attach` adapter
does not map to `Option` payloads and then silently discard failed elements.

The ceiling correspondence uses only ordered-field and floor-ring APIs in the
core; the Real instance is imported by the consumer. The generic quotient
correspondence is used immediately by the exact size-five theorem.

## Root-owned next actions

Build `Applications.Selection.MedianOfMedians` and `Examples.MedianOfMedians`
serially in the qualified environment when available; preserve actual terminal
results and diagnostics. Correct any real elaboration or lint findings without
weakening these statements. Run the 55-name type program before full statement
qualification. These development checks give no full Chapter 3 acceptance credit.

When integrating the complete chapter, add both new module imports to the
appropriate public root and map the witnesses above in the reconstruction
documentation. Those shared files have deliberately not been edited by this
author; they remain under root coordination. The full 83-row review, complete
candidate validation/audit, independent Standards and Spec outcomes, immediate
verification, and exact accepted fast-forward remain mandatory.

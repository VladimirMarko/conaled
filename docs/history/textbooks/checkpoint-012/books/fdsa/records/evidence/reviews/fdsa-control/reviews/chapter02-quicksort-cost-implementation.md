# Chapter 2 deterministic quicksort costs — implementation record

## Status and ownership

2026-11-04: **resource module focused pass; corrected examples awaiting recheck;
not accepted.** Latest immutable author candidate:
`df67f1cc9c0f4fb51d317ff4a2957ab047c179b9`.
This is a bounded continuation of the existing complete Chapter 2 loop, not a
new acceptance workflow. The complete chapter review base remains accepted
Chapter 1, `07e480f6ec9958d4975bb90151005b84f2907614`. All 112 current Chapter 2
obligations, including both C02-024 probability claims, remain in the full scope.

The author owns only new `Applications/Resources/QuickSort.lean`,
`Examples/QuickSortCosts.lean`, this handoff and dedicated provenance. Existing
checked quicksort values remain unchanged at their original bytes. Root owns
the shared private compiler slot, public roots, coverage, tickets, full checks,
independent reviews and acceptance. **No local compilation is authorized.**
Root will compile supplied immutable development commits in its cache worktree.

The original checked value candidate is
`840252e63026bba5eab109f2b16468deef7670ec`. Root explicitly authorized retaining
the exact pending foundation `f17cc6b1a2bf44215b16202ed0fcee2b5c130761` for the
existing `Resources.ListCalls.filterRun` implementation. The development-only
merge is `fdd4d4796fe8201cecfa8a53930a391b6e50f401`, with those two parents in
that order. It completed without conflicts, with clean statuses before and
after, and unchanged value-file hashes. The dependency is **still unaccepted**;
its separate full gate is running. No accepted integration reference or
foundation worktree was modified. If the dependency candidate changes, root
must reconcile and validate the resulting development candidate.

The immutable merge receipt is
`provenance/chapter02-quicksort-cost-foundation-merge-20261104/result.json`.

## Source, existing interfaces and semantic boundary

The pinned July 27, 2026 PDF has SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The current reading copy is outside the checkpoint payload, under
`/workspace/scratch/b4a17a285e23/research-source/`.

The actual source was read with the complete current chapter requirements,
`research/quicksort-average-proof-plan.md`, the accumulator readiness records,
the existing checked value implementation and the applicable repository
implementation, architectural and example-driven-development instructions.

- Printed p. 5 explicitly states that append associates to the right.
- Section 2.3, printed pp. 16–17, selects the first element as pivot, filters
  the tail with strict less and its nonstrict complement, then evaluates
  `left @ ([pivot] @ right)`. Both append occurrences must remain measured.
- Exercise 2.2, printed p. 28, requires equality for **every** accumulator
  suffix. It prints no numerical cost formula for the accumulator variant.
- Exercise 2.4, printed pp. 28–29, gives empty count 1 and nonempty count
  `T(left) + T(right) + 2*Tfilter(unit)(tail) + 1`. Append is uncharged in
  that exercise observation.
- Appendix B.1, printed pp. 347–348, gives `Tappend xs ys = length xs + 1`
  and unit-predicate filter count `2*length xs + 1`.

Reuse is concrete: `Resources.Measured` and `bind`, the accepted
`Resources.ListReversal.appendRun`, the exact pending foundation's
`Resources.ListCalls.filterRun`, and the checked `Applications.Sorting`
quicksort definitions/erasure and length laws. No new carrier, generic cost
framework, filter algorithm or append algorithm is needed. The ordinary
standard product `Nat × Nat` separates the two observations on one execution.

## Concrete implementation plan, recorded before source changes

1. Define an actual measured first-pivot execution. Each nonempty call performs
   the left filter and recursive sort, the complementary right filter and
   recursive sort, then `appendRun [pivot] right` followed by
   `appendRun left` on that returned list. A unit predicate callback is charged
   in each filter. The first observation records recursive/filter calls under
   Exercise 2.4; the second records only the two append executions and their
   descendants. Empty returns `([], (1, 0))`.
2. Prove erasure to the existing value sorter and exact derived recurrences.
   With tail length `m`, partition lengths `l,r`, and observations `T,A`,
   the intended laws are `l+r=m`,
   `T = Tleft + Tright + 4*m + 3`, and
   `A = Aleft + Aright + l + 3`.
   The literal append-inclusive observation is `F = T + A`.
   The append charge `l+3` follows from the returned left value's proved
   length, the inner singleton append charge 2 and outer charge `l+1`.
3. Define the actual cons-based suffix worker using the same two filters.
   Its right recursive result becomes the suffix of the left recursive call.
   Prove erasure to the existing worker for all suffixes, plus an independent
   recursion proof of identical exercise count and zero append count. This is
   a declared extension of the source tariff to the actual Exercise 2.2
   worker, not a numerical claim quoted from that exercise.
4. Prove law-free universal bounds from complementary partition lengths:
   `T ≤ 2*n^2 + 2*n + 1`, `3*n ≤ A`, `2*A ≤ n^2 + 5*n`, `A ≤ T`, and hence
   `T ≤ F ≤ 2*T` and `2*F ≤ 5*n^2 + 9*n + 2`. Establish the corresponding
   natural-division bound only with its exact integer justification.
5. Prove generic one-sided partition cases before source specializations.
   An all-right pairwise predicate gives
   `T = 2*n^2 + 2*n + 1`, `A = 3*n`, and `F = 2*n^2 + 5*n + 1`.
   Nondecreasing source keys, including duplicates, satisfy that predicate.
   A strict all-left pairwise predicate gives the same `T`,
   `2*A = n^2 + 5*n`, and `2*F = 5*n^2 + 9*n + 2`.
   Strictly decreasing keys satisfy this predicate. Weak descent with mixed
   equal keys does **not** justify that exact one-sided append formula.
6. Retain the all-equal family as a quadratic counterexample to unrestricted
   distinct-key average claims. Provide a strictly descending natural range
   specialization to witness attainability of the full-cost upper bound.
7. Define the deterministic partition statistic `Q` on exactly the same
   pivot/partition recursion, with tail-length toll, and prove
   `T = 4*Q + 4*n + 1`. This is not a claim that the literal two-filter
   implementation performs only `Q` comparisons, and does not establish any
   probability distribution correspondence.

All algorithmic permutation, erasure and raw numeric bounds require no order
or equality class on payloads. Source-key wrappers use only the comparison or
order structure actually needed by their statements. The suffix is universally
quantified and need not be sorted. No probability law, distinctness hypothesis,
expected-case assumption or changed pivot algorithm will be invented here.

## Independently fixed connected cases

The missing connection at this stage is the measured execution and its public
theorems. No compiler failure has been asserted: builds are deliberately held.
The expected values below come from direct substitution in the source tariff
and both Appendix B append charges, before implementation.

| Input | Returned value | T | A | F | Q |
|---|---|---:|---:|---:|---:|
| `[]` | `[]` | 1 | 0 | 1 | 0 |
| `[x]` | `[x]` | 5 | 3 | 8 | 0 |
| `[0,1,2]` | `[0,1,2]` | 25 | 9 | 34 | 3 |
| `[2,1,0]` | `[0,1,2]` | 25 | 12 | 37 | 3 |
| `[2,2,2]` | `[2,2,2]` | 25 | 9 | 34 | 3 |
| `[1,0,2]` | `[0,1,2]` | 21 | 10 | 31 | 2 |
| `[2,1,2,3,0]` | `[0,1,2,2,3]` | 45 | 18 | 63 | 6 |

The worker on the final input with the deliberately unsorted suffix `[4,0,2]`
must return `[0,1,2,2,3,4,0,2]`, with observation `(45,0)`.
The empty worker preserves every suffix at `(1,0)`.
An append-association boundary case with left length 2 must distinguish cost 5
for the source's right association from cost 7 for left association, despite
equal list values. Generic payload and arbitrary-suffix specializations will
exercise the public laws, not private proof reductions alone.

## Authored API and static statement review

After checkpoint 0084, root released the source hold. The new resource module
contains 475 lines and the new connected example module 193 lines. No existing
source path was edited. The source readback receipt is
`provenance/chapter02-quicksort-cost-draft-20261104/source-readback.json`.

The scoped immutable draft is
`e4c152e62271725abe6e71ac52e4756316208b24`, parent
`fdd4d4796fe8201cecfa8a53930a391b6e50f401`. Its worktree is clean and staged
whitespace validation exited 0. This is source validation, not a Lean check.
`candidate.json`, `diff-check.log` and `commit.log` in the same provenance
directory retain the exact transition. The resource SHA-256 is
`d4d3efecce795e70bc8c4a41ef4f63591d9e438a7cd0de8c46e6c9340d318d78`;
the example SHA-256 is
`8ef4641517938d5004a172badce122ec5f69ad0749558431c060bea94f5b064b`.
`Statements.lean` supplies 83 public definition/theorem readbacks with explicit
arguments and universes for the coordinated post-build statement review.

### Pre-compiler namespace repair

The independent random-pivot preparation identified two consecutive
`end Resources.QuickSort` lines at the exact original draft's end. Readback
confirmed one opening namespace and two terminators. Root authorized a narrow
repair, committed as `6122dd02c0a5b7ab4435e442e27d641e763f58f5`, directly after
the preserved original `e4c152e62271725abe6e71ac52e4756316208b24`.

The source diff deletes exactly one final redundant terminator. All other
resource bytes, all definitions/statements/proof bodies/expected cases and the
entire example file remain unchanged. The resource now has 474 lines and SHA-256
`e98024f6b741e1aba1fb1e38b419eee2e1acad76a8a40e669752f54775783263`.
The worktree is clean; whitespace validation and commit both exited 0.
`provenance/chapter02-quicksort-cost-namespace-repair-20261104/` preserves the
start/result identities, exact `source.diff`, namespace-count readback and logs.
**This was a pre-compiler source repair. No failed or successful compiler attempt
occurred**, and the 83-readback input remains unchanged and unexecuted.

### Actual central focused result and minimal proof-name correction

Root's six-target check at composed candidate
`8ec1d9cb93e4c38168dc357e8b6f254f8fe83668` closed with actual **exit 1**.
The terminal record preserves an unchanged HEAD and clean final status. Its
complete log and result are
`provenance/chapter02-measured-sorting-focused-20261104-attempt1/full.log` and
`result.json`; the closed log SHA-256 is
`fd65b65eab6a5cc03a6252895665864a16ac7c3724b9539b938f8800a5c8a44e`.
Readback verified that both quicksort files in that composed candidate exactly
matched the author candidate `6122dd02`.

`Applications.Resources.QuickSort` built successfully, including the complete
474-line deterministic resource module. `Examples.QuickSortCosts` failed at
line 73 because the bare `bind` in the left-associated comparison example's
simp list was ambiguous between `Resources.bind` and `Bind.bind`. The printed
remaining goal already identified the actual operation as `Resources.bind`.
Other six-target failures belong to their separate source owners; this handoff
does not claim that the combined check passed.

Root released exactly that correction. Successor
`df67f1cc9c0f4fb51d317ff4a2957ab047c179b9`, directly after preserved
`6122dd02c0a5b7ab4435e442e27d641e763f58f5`, changes only the proof simp
argument from `bind` to `Resources.bind`. The theorem statement, expected value
`([0,1,2,3],7)`, all other examples and the entire resource file are unchanged.
The updated example SHA-256 is
`9d61ea34342e2f5d961c3d2962630f2ed853939802057dbfc2aca65ee1e9f999`;
the resource remains
`e98024f6b741e1aba1fb1e38b419eee2e1acad76a8a40e669752f54775783263`.

The author worktree is clean; whitespace validation and commit exited 0.
`provenance/chapter02-quicksort-cost-bind-repair-20261104/` retains the exact
source diff, before/after identities, matching central source/log readback and
commit logs. No local build or cache activity occurred. The successor still
requires root's immutable focused recheck and the existing statement readback.

The implementation uses namespace `Resources.QuickSort`. Its seven definitions
are `appendPivotRun`, `run`, `exerciseCost`, `appendCost`, `literalCost`,
`accumulatorRun` and `partitionMass`. They implement the recorded plan without
introducing another carrier or generic observation framework.

| Public claim family | Intended meaning and assumption review | Connected uses |
|---|---|---|
| `appendPivotRun_exact`, `run_cons`, `run_value`, `run_length`, `run_exact` | Two actual right-associated append calls use the recursively returned values; erasure is exact ordered list equality; length follows from the checked occurrence permutation. No comparator laws or payload instances. | Empty and singleton sources, mixed ordered duplicate value, the 5-versus-7 append association boundary. |
| `exerciseCost_cons_source`, `exerciseCost_cons_on`, `appendCost_cons`, `literalCost_cons` | The actual measured execution yields the exercise tariff and the separate append tariff. The keyed source equation explicitly identifies complementary filtering with nonstrict comparison under a linear order. | Mixed source strict/nonstrict split, measured primitive filter charges, mixed `(45,18)` and full count 63. |
| `accumulatorRun_cons`, `accumulatorRun_exact`, `accumulatorRun_eq_append`, `accumulatorRun_cost_independent` | Actual cons worker, with the right result fed into the left call; value and costs proved together by recursion. Suffix is arbitrary and never measured as a traversed input. | Arbitrary empty/singleton suffixes, unknown payloads, mixed unsorted overlapping suffix, duplicate family. |
| `exerciseCost_le`, `appendCost_lower`, `appendCost_double_le`, `appendCost_le_exerciseCost`, `literalCost_le_twice`, `literalCost_double_le`, `literalCost_le` | All Boolean comparators and lists; complementary occurrence lengths are the only partition hypothesis. Division appears only after the division-free bound. | Universal keyed payload bounds and both sides of the exercise/full-cost bridge; strict-descending range family attains the full upper bound. |
| `accumulator_saving`, `accumulator_cost_lt` | At least `3*n` source append calls removed for every suffix; strict improvement requires only a nonempty first input. No claim about Lean runtime or total suffix length. | Mixed worker saving with its source length five. |
| `costs_of_all_right`, `literalCost_of_all_right`, `costs_of_all_left`, `literalCost_double_of_all_left`, `literalCost_of_all_left` | Generic pairwise conditions constrain every later occurrence relative to each earlier pivot. One-sided filtering is derived, not assumed as a numerical cost recurrence. | Increasing and strictly decreasing concrete inputs, exact append/full cost distinction, all sizes via descending natural ranges. |
| `costs_of_sorted`, `costs_of_strict_descent`, `costs_replicate` | Nondecreasing keys allow duplicates; strict descent needs only the specified decidable strict relation. Constant lists have no distinctness premise. Payloads require no order/equality instances. | Sorted, strict-descending, all-equal, arbitrary-size duplicate inputs and arbitrary payload parameters sharing one key. |
| `partitionMass_cons`, `exerciseCost_eq_partitionMass` | Deterministic sum of tail lengths on the same first-pivot recursion. The law `T=4Q+4*n+1` is proved before any probability model, with repeated keys allowed. `Q` is not the literal two-filter invocation count. | Mixed mass 6 and balanced mass 2 are derived through the general bridge and measured exercise counts. |

All independently fixed values in the plan remain unchanged. Source review
found and corrected a proof-expression typo before the candidate commit; no
statement, hypothesis or expected result was weakened. The initial source-only
readback did not establish elaboration. The central result above now establishes
the resource module's focused compilation, including its well-founded
filter-result recursion; the corrected example module and exact elaborated
theorem-type readback remain pending.

## Remaining gates

Static review of this plan preserves actual first-pivot execution, strict-left
complementary partitions, occurrence lengths, duplicate behavior, source entry
charges, both terminal append calls and all-suffix quantifiers. It explicitly
separates exercise and full counts, and exact formulas from upper bounds.

No elaborated-type readback, successful combined candidate build, complete
candidate check, proof audit, or independent review pass exists yet for this
slice. The resource module's focused pass is recorded above. The corrected
examples need the next immutable focused check, followed by elaborated statement
readback and the normal complete candidate/review gates. The
complete average-input and randomized-pivot requirements, uniform-subproblem
correspondences, harmonic/logarithmic consequences and pivot selection/removal
tariffs remain mandatory subsequent work. This deterministic slice cannot
accept C02-024 or the complete chapter.

## Elaborated author readback — 4 November 2026

All83 public declarations (53 core,30 examples) passed explicit/universe-visible
inspection at clean1ffb61fc, and the original author read all actual types and
source against the original models/cases with zero concrete findings. Exact
read counts, hashes, assumptions, execution/counter/suffix distinctions and
independent expectations are retained in
provenance/chapter02-measured-sorting-types-20261104/quicksort-author-readback.md.
This is author statement assessment, not either independent final review axis
or full acceptance. Both focused modules' actual pass evidence and failed
aggregate exits remain unchanged.

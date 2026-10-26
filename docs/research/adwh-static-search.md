# Static heuristic search reconstruction

[#155](https://github.com/VladimirMarko/conaled/issues/155) retains the bounded
static A*/M* family from [checkpoint 233](../history/algorithm-design-haskell/README.md).
[Declaration provenance](adwh-search-provenance.tsv) records exact member hashes,
source declarations and local destinations. It does not close the separate
incremental search commitment [#111](https://github.com/VladimirMarko/conaled/issues/111).

## Contracts and representation choices

`Search.Heuristic.Walk` describes arbitrary graph walks and accumulated Nat
costs. `Route` validates the stored reverse path. `Minimum` compares a returned
goal path against every goal-reaching walk, independently of queue contents and
implementation candidates. `astar_correct` requires optimism and a completed
run. `mstar_correct` requires monotonicity and zero heuristic at goals. The
finite-domain termination theorems retain their explicit closure premises;
termination does not assume an optimum exists. Reopening termination uses Nat
cost decrease. Closed-mode termination has a separate finite-domain/degree
budget.

`run` retains three results: `none` for exhausted observation fuel, `some none`
for completed failure and `some (some path)` for success. The goal test precedes
the repeated-vertex test. Zero-cost edges are permitted. The mathematical costs
do not overflow; this does not implement signed or machine arithmetic.

The queue interface separates `Operations` from `Laws`, with `entries` and
`Valid` supplied as abstract observations. `Queue` packages an implementation
and those contracts for ordinary callers. Insertion may replace an occurrence
at the same key with a no-higher-priority occurrence. Removal preserves the
exact occurrence permutation and chooses a minimum. This is weaker than
requiring two queues to choose the same path among ties.

The leftist implementation preserves cached ranks, actual right-spine merge
and root deletion. The keyed list model preserves equal-key replacement and
right-fold insertion, then priority/key deletion order. No existing conaled
priority queue was found. A container substitution must prove these occurrence,
replacement and tie contracts before replacing either realization. No balanced
or logarithmic performance is attributed to the keyed list model.

Unused source imports of heap sorting and finite unweighted search were removed:
the selected modules compile from `Std` without those proofs. The imported
source dependency names were not adopted as architectural boundaries. Retained
modules separate path semantics, frontier coverage, optimum proofs, termination,
finite-result semantics and the two concrete queues.

## Composed consumer and checked cases

`Applications.Search.Interpretation` connects actual completed executions to
independent shortest-distance semantics through existing relational squares.
`Completed` contains a fuel budget whose actual execution has completed.
`completed_exists` derives an inhabitant from finite closure; its premise is not
minimum correctness. `astarSquare` produces a result satisfying `CorrectResult`.
`observeDistance` forgets stored paths and proves `DistanceResult` over arbitrary
walks. `distanceSquare` composes these operations with `Relational.compose`.
The convenience representation uses `Type` vertices; the original search and
correctness theorems retain their universe-polymorphic types.

The source optimum4 and optimum6 applications continue to use public optimum
results. New `interpreted_distance4` and `interpreted_distance6` use the composed
distance consumer with leftist and keyed queues respectively. Their expected
costs remain 9 and 17. The Figure 16.1 path is ACBD, preserving the source's
correction of the printed ABCD prose.

Checked source cases retain optimism without monotonicity and M*'s resulting
suboptimal choice, cyclic no-goal, exact leftist/keyed ties, chronological path
extraction and failure of heuristic-only priorities. The added exhaustion case
keeps zero fuel distinct from completed no-goal. These connections were the
initial obligations for the new consumer; the existing source cases already
exercised public correctness results and did not need artificial proof failures.

Statement review checked independent competitor quantification, heuristic
premises, queue occurrence versus key coverage, goal/skip order, fuel/result
nesting, finite-domain closure and the natural-cost decrease argument. New
relational composition transports those existing conclusions; it does not
assume a correct shortest distance as an interface law.

## Rational costs and incremental repair

[#159](https://github.com/VladimirMarko/conaled/issues/159) is the bounded
follow-up for a checked static finite rational/infinity adapter. It requires a
positive common scale for a finite collection of rational edge and heuristic
values, omits blocked edges with a proved graph interpretation, and transports
walk costs, heuristic premises and minimum distances in both directions. Tie
selection needs its own compatibility proof. This adapter is not implemented
here.

#111 still needs explicit edge-assignment patches, predecessor access, retained
state, initialization/repair/observation contracts, update-stable heuristics and
repair termination. Arbitrary new rational denominators can invalidate a fixed
scale. Per-instance rescaling would not preserve retained state without another
proof. Nat decrease arguments cannot be generalized silently to an order with
infinite descending chains. #113 owns generic retained-state/resource contracts;
#109 owns recursion support. A whole-search primitive is an adapter, not proof
that a compiler derived repair.

No complexity, runtime, retained-state reuse or improvement claim follows from
static correctness. The source heuristic cost modules, tree-search termination
and tree-search global-optimum extensions, large puzzle/warehouse realizations,
and the rest of Chapter 16 remain reference material under #149. The retained
finite-tree-mode execution examples do not assert general tree-mode termination.

Targeted compilation checks the selected search modules and examples. Reference
validation #150, the supervising fresh full build and exhaustive audit, and
independent reviews remain acceptance gates.

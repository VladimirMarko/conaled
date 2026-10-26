# Huffman reconstruction (#166)

For every nonempty input, `Huffman.Priority.huffman` returns a full binary tree
whose fringe contains exactly the input occurrences and whose weighted leaf-depth
sum is least among every such tree. Empty input returns `none`. Labels may repeat,
weights may be zero, and the input need not be sorted. `Examples.Huffman` connects
these public results to explicit arithmetic, two queue implementations, and the
composed tree and cost consumers.

## Semantics and reconstruction

`Huffman.Basic` uses the existing `Bracketing.Tree`, `fringeSpec` and leaf-count
`size`. The shared tree and its existing basic proofs now accept `Type u` labels.
`pathCost` independently zips the fringe with the matching traversal of depths,
starting at depth zero. `depthsFrom_length` rules out truncation by `zip`;
`pathCost_eq` proves the recursive-cost equation at every starting depth.
`Feasible` is a list permutation, so it preserves multiplicity and permits
reordering. `Optimal` quantifies over all independently feasible trees.

`Huffman.Exchange` retains the source's ordinary deepest-sibling surgery,
contraction, and forest arguments. The distinct-label argument exchanges leaf
positions using `Equiv.swap`. The general argument numbers actual occurrences
with `zipIdx`, lifts the fringe permutation to those tags, performs the distinct
exchange, and erases tags. Equal labels therefore remain distinct occurrences
during surgery. No positive-weight or global `Nodup` premise reaches the public
result. `List.eq_map_comp_perm` replaces the source's permutation-enumeration
preimage argument; no permutation enumerator is imported.

Forest feasibility means flattening a full binary shape whose fringe permutes
the supplied existing subtrees. `cost_flatten` splits its cost into the cost of
combining those atoms and the sum of their existing internal costs. The greedy
exchange constructs a no-more-expensive lift of each original competitor into
the merged forest problem. `forest_greedy_refinement` supplies these actual lifts
and the separately proved feasibility inclusion to
`Optimization.minimizer_transport`.

## Operations, observations and laws

`Search.PriorityInterface.ExactLaws` strengthens the insertion contract needed
by Huffman. It uses the existing `Operations`, a supplied occurrence observation,
and a validity predicate. Addition preserves the exact permutation of inserted
and existing entries; removal returns a minimum and deletes exactly one
occurrence. `ExactQueue.keyed` derives the weaker existing search contract for
any key, requiring only reflexivity of priority comparison. Existing A*/PSQ
interfaces and implementations are unchanged.

`exactLeftist` reuses the accepted leftist queue operations and proofs. `exactList`
stores a list, appends inserted entries, and deletes the head of standard
`List.mergeSort`, retaining its sorted tail. Both support a decidable linear
preorder; antisymmetry is unnecessary. Their laws use permutation rather than
set membership, so equal entries are retained. The list implementation makes
no runtime or asymptotic claim.

The generic cached construction performs two minimum removals and one insertion
of the combined tree and cached weight sum. `Good` separates queue validity from
cache agreement with the independent tree weight. Each productive step reduces
the observed occurrence count by one, preserves `Good`, and transports forest
optimality backwards. `loop_spec` proves that sufficient fuel reaches a singleton
and gives an `Iteration.UntilSpec` trace: the stopping test is false at every
preceding state and true at the last. For an input of length n, n−1 fuel suffices.
A singleton has depth-zero cost zero. Insufficient fuel can extract one partial
forest atom; it is not an infeasibility result.

`Huffman.SourcePriority` contains only the literal source step, loop and outer
consumer and their equalities to the leftist specialization. In particular,
`huffman_eq` preserves the source's tie-selected tree, not only its cost. The
generic internal deletion/size helpers require validity, and its singleton
extraction helper requires `Good`; the source's concrete helpers also worked on
malformed leftist heaps/caches. This internal domain change is recorded in the
ledger. The public source algorithm always establishes the invariants and its
entire behavior is recovered by the equality.

## Consumers and checked cases

`treeSquare` retains the input list and uses the independent optional result
contract: `none` exactly for empty input, otherwise an optimal tree.
`costSquare` actually composes this square with the shared
`Optimization.observationSquare`; the latter maps the set of permissible
results to its cost image. The weight function is a fixed explicit parameter of
each square. Numeric outputs use `ULift` to fit the square framework's common
universe without restricting label universes. The ordinary `costResult` returns
`Option Nat`, and `costSquare_impl` connects that output to the square.

`costResult_attained` recovers an optimal returned witness for a reported cost.
`costResult_eq` proves that any two lawful exact queues agree on costs, without
identifying their selected trees. Four unit-weight labels demonstrate this:
the leftist realization joins the `(3,4)` pair before the `(1,2)` pair, while the
list realization chooses the opposite order. Both trees have four leaves at
depth two, hence cost eight.

The initial EDD obligations were a globally optimal output for unsorted
`[10,1,2]`, occurrence-safe exchange with equal least labels, and cost agreement
between independent realizations. The old keyed insertion contract could discard
occurrences and could not discharge these obligations. The new exact law and
surgery proofs supply those missing connections. Expected costs are calculated
from leaves and depths, independently of the queue loop:

| Case | Independent arithmetic | Public connection |
|---|---|---|
| Empty | No full binary tree with empty fringe | `huffman_none_iff` |
| Singleton a | weight(a) × 0 = 0 | `huffman_singleton`, `costResult` |
| Two leaves 7,2 | 2 × 1 + 7 × 1 = 9 | `huffman_correct` |
| Unsorted 10,1,2 | 1 × 2 + 2 × 2 + 10 × 1 = 16 | Both queues; arbitrary feasible competitors |
| A worse tree | 1 × 1 + 2 × 2 + 10 × 2 = 25 | Explicit feasibility and strict cost comparison |
| Repeated labels 2,2,1 | 2 × 1 + 1 × 2 + 2 × 2 = 8 | `huffman_correct`; both 2 occurrences remain |
| Zero weights 0,0,3 | 0 × 2 + 0 × 2 + 3 × 1 = 3 | List realization's global optimum |
| Tied weights | 1 × 2 four times = 8 | Both global certificates, unequal trees, equal costs |

Further checked applications exercise generic and concrete cache preservation,
first-hit stopping, zero-fuel truncation, repeated-label greedy exchange, forest
cost decomposition, the weaker keyed-contract derivation, the source equality,
and `ULift.{1} Nat` labels through the algorithm and composed square. Queue
computations serve as hypotheses to public optimality results; they do not
replace those results with independent computations of optimum.

## Statement review

The review covered every declaration in the selected closure and all local
additions, grouped by their mathematical obligations:

- The shared tree change alters universe generality only. Existing ordered
  bracketing semantics remain intact. Fringe/depth lengths, the depth-zero
  singleton, and the positive leaf count exclude accidental empty trees.
- Weight, depth, recursive cost, cache, map and flatten claims retain their
  independent meanings. Feasibility uses permutation throughout; total weight
  equality alone never substitutes for leaf occurrence preservation.
- The distinct exchange lemmas expose their decidable equality and `Nodup`
  assumptions. The general exchange discharges them by actual occurrence tags.
  Two-least assumptions are weak inequalities, admitting zero and tied weights.
  Contraction adds back exactly the weights of the two merged occurrences.
- Forest optimality compares all feasible competitors. The transport theorem's
  admissibility and dominating-lift premises are proved by inclusion and surgery,
  not assumed as an extra optimum oracle.
- Exact queue laws distinguish executable operations, entry observations and
  validity. Minimum deletion removes one occurrence; exact insertion preserves
  every occurrence. Only invariants actually established by initialization are
  assumed in the generic algorithm proof. Each queue realization discharges the
  same law family.
- Termination counts queue entries, not distinct labels or tree nodes. The trace
  forbids skipping a successful stopping test. Empty and singleton inputs are
  covered; raw truncated loops carry no optimum or no-solution promise.
- Source equalities identify the entire selected leftist result. Cross-queue
  comparison identifies costs only. The consumer composition retains the input
  and permits exactly an image of independently specified results, including the
  empty case. The universe-lifted examples check that no Type0 restriction leaked
  into the algorithm or square.

These checks support the recorded scope; examples do not exhaust all informal
interpretations. Independent Standards, Spec and supervising intent reviews and
the fresh full build/axiom audit are integration requirements, separate from the
author's targeted checks.

## Provenance and scope

The source is the immutable
[`adwh-checkpoint-233`](../history/algorithm-design-haskell/README.md). The archive
SHA-256 `8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63`
and each selected member were checked; extracted reference bytes matched the ZIP.
The [declaration ledger](adwh-huffman-provenance.tsv) contains 140 source rows:
all 33 named declarations of `HuffmanTree`, 53 of `HuffmanExchange`, and 22 of
`HuffmanPriority`; eight selected `TreeEnumeration` helpers, eighteen previously
accepted `LeftistQueue` declarations, two `Iteration` declarations and four
replaced `Permutations` dependencies. It also records 53 local interface,
consumer, source-equality and named example declarations. Constructors/generated
names and anonymous examples are covered by their declarations and containing
example module rather than separate rows. The full source members and hashes
remain in the repository archive and manifest.

The selected scope is Huffman global optimality and exact-priority construction.
Coding words, prefix codes, other list/two-list/stack algorithms, exact operation
counts, asymptotic bounds, alphabetic trees and Garsia-Wachs are outside #166.
No tree enumeration or queue-cost module is imported to obtain a helper.

Author validation: `direnv exec . lake build Examples.Huffman Examples.Bracketing
Examples.HeuristicSearch` checks the new public cases and the existing shared-tree
and search regressions. Integration runs the repository's fresh full build and
exhaustive proof audit separately.

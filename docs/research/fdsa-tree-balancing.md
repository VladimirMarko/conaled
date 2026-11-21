# Consuming balance, shape, ordered sets and composed work

CTB-75 develops FDSA Chapter 4's consuming balancer against pinned master
`c214fb0720ffc998951255a7e4b5f2e80a299186`. The original four-module source is
the complete tree at `a8f57dbf153c19e3bad2c8136a90b566eeb35374`, containing
66 public named declarations. Its value, suffix and consumer-call contracts
are retained alongside the new shape and cross-application results.

The source correspondence is the retained [Chapter 4 obligation ledger](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter04-obligations.md)
for the July 27, 2026 manuscript. FDSA-4-47 to FDSA-4-58 cover consumption, balancing,
heights, the figure and its ordered interpretation; FDSA-4-61 is Exercise 4.9's
consumer cost. This work uses that retained source analysis and does not claim
a new reading of the PDF. The exact Exercise 4.8 constructor formula,
completeness/maximal-subtree algorithms and maximum-cache exercise have
separate owners. A sufficient shape lemma here does not discharge those items.

## One consumer and its exact domain

`Trees.Balance.bal` returns an Option containing a tree and its actual remaining
input. Request zero returns nil with the input unchanged. For a positive request
`n`, it first consumes `n/2` labels for the left tree. The returned suffix supplies
the root label and the actual input of the right recursion, which consumes
`n-1-n/2`. The implementation does not replace that sequential flow with
independently reconstructed take/drop lists, and it needs no label equality,
order or default inhabitant.

Success gives the independent decomposition `xs = inorder t ++ zs` and exact
node count `t.numNodes = n`. The prefix and suffix theorems then identify
`inorder t = xs.take n` and `zs = xs.drop n`. Existence is equivalent to
`n ≤ xs.length`; failure is equivalent to the strict reverse length inequality.
These statements preserve order and every repeated occurrence.

`balList` exposes the tree with nil as the explicit failure fallback.
`balanceList` requests the full list. `balTree` supplies canonical inorder to
the same prefix consumer; `balanceTree` requests the original node count.
Full wrappers always have sufficient input. Prefix size, inorder and requested-
size height laws keep the sufficient-input premise. In contrast, the wrapper's
almost-completeness invariant is unconditional: a failed request returns nil.

## Shape follows from existing logarithm bounds

The tree carrier, external-leaf count, height, minimum external-leaf height,
`Complete` and `AlmostComplete` keep their existing owners. Complete means a
perfect tree, including nil. Almost complete means external leaves occupy at
most two adjacent levels; it does not impose a left-packing convention.

The general shape step allows unrelated payload types. If almost-complete
trees `s,t` satisfy `s.numLeaves ≤ t.numLeaves+1`, their existing discrete
logarithm laws imply `s.height ≤ minHeight t+1`. Indeed, the standard floor-log
bound gives

\[
\ell(t)+1\le 2^{\lfloor\log_2\ell(t)\rfloor+1},
\]

and the ceiling-log upper-bound law applies to `ℓ(s)`. This cross bound in both
directions, together with each child's own almost-completeness inequality,
proves a node almost complete when its children are almost complete and their
external-leaf counts differ by at most one. These reusable shape results belong
to `Applications/Trees/Shape.lean`.

`Applications/Trees/BalanceShape.lean` follows the actual successful branches
of the consumer by strong induction. The child node counts supplied by
`bal_spec` are `n/2` and `n-1-n/2`, so their external-leaf counts satisfy the
required adjacent-size inequalities. This proves almost completeness before
using any desired balancing height formula. Success alone suffices; an extra
input-length premise is unnecessary for that theorem.

The existing Shape laws then give both exact heights:

\[
h(t)=\operatorname{clog}_2(n+1),\qquad
mh(t)=\operatorname{log}_2(n+1).
\]

The same contracts cover all four wrappers with their proper domains.
`Examples.TreeBalanceShape` consumes the existing ShapeLog bridges for the
source real-log ceiling/floor versions of the core and all four wrappers.
Real analysis is kept out of the pure consuming module. Nil has one external
leaf; replacing `n+1` by `n` would lose that boundary and other exact values.
Height optimality is an application of the existing `height_optimal` theorem
to actual balanced outputs and compared node counts. It makes no claim about
machine-time optimality or a converse characterization of almost completeness.

## Ordered interpretation and interchangeable set operations

`Examples.TreeBalanceSearch` combines the independent inorder contracts with
CTB-73's existing Ordered/OrderedBy versus strict-pairwise-inorder theorems.
The full-list result is an equivalence between ordered balanced output and
strict pairwise input; the successful-prefix result refers to the actual
prefix. Rebalancing preserves and reflects orderedness of an existing tree.
Keyed versions order keys only, without imposing order or equality on payloads
or requiring a globally injective key function.

Label-set preservation holds for every raw tree, with no ordering premise,
through canonical inorder and the independent `setTree` observation. Together
with orderedness preservation it defines `rebalanceSquare` on the existing
`AbstractSet.representation`. Its implementation is actual `balanceTree`, and
its set specification is the identity. `Relational.compose` combines it with
the existing candidate insertion square. The resulting contract supplies both
validity and membership; an actual directed membership query consumes those
facts through the shared set laws. No new set interface or validity predicate
is introduced, and no semantic agreement is used to transfer a cost theorem.

The complete ten-node source figure is a positive ordered client. Repeated
labels are valid input to balancing, but nondecreasing duplicates do not give
a strict BST. Function-valued payload examples exercise the keyed interface
without payload ordering. An arbitrary untouched suffix need not be sorted.
An undersized request on `[2,1]` returns ordered nil despite the unsorted input
prefix, demonstrating why the prefix equivalence needs sufficient input.

## Measure the executed composition

`Resources.TreeBalance.balRun` is the actual measured consumer. It follows the
same sequential branches, with one entry charge per call, and erases to `bal`
on every input, including failure. On sufficient input its exact count is
`2*n+1`. In the declared source model, arithmetic, pattern matching, constructors
and projections are primitive or uncharged. The failed request `balRun 1 []`
costs two entries; the successful-input formula cannot be asserted for it.

`Examples.TreeBalancePipeline` uses `Resources.bind` to pass each frontend's
actual returned list to that same measured consumer. The literal frontend is
the existing right-associated two-append inorder program. The direct frontend
invokes the suffix traversal at empty suffix. The staged frontend pays both
construction and invocation of the suffix program. These executions reuse the
existing measured folds and accumulator rather than defining a cost-only
surrogate or moving an Examples-owned program into the domain layer.

Let `N` be input node count and `A = Trees.leftSizeSum t`. For `n ≤ N`, the
counts of these actual composed programs are:

| Frontend | Prefix request | Full request `n=N` |
| --- | --- | --- |
| Literal two-append inorder | `5*N + 2*n + 2 + A` | `7*N + 2 + A` |
| Direct suffix invocation | `2*N + 2*n + 2` | `4*N + 2` |
| Construction plus suffix invocation | `4*N + 2*n + 3` | `6*N + 3` |

Each value erasure is unconditional, and the successful result retains the
actual untouched inorder suffix. A linear consumer does not remove the literal
frontend's shape-sensitive append work. The direct full count has a linear
bound for positive input size. The nil counts are respectively two, two and
three, so a staged-versus-literal improvement requires a nonempty-input premise.
Construction remains charged even if the same semantic list is returned.

Asymmetric and chain cases connect equal values with different measured costs
through the public program contracts. These are source-model counts, without
claims about Lean runtime, arbitrary-precision arithmetic, allocation or
physical sharing.

## Evidence and remaining work

The complete CTB-75 requirements and current tracker are in the checkpoint.
The unit's exact candidate, focused builds, all-declarations audit, statement
and case assessment, original-source correspondence, both independent reviews
and final source comparison are recorded there. Those records establish their
stated bounded evidence. Receiving guarded whole-library compilation,
exhaustive project audit, immediate verification and final acceptance remain
separate pending gates. Chapter 4's final row qualification is also separate;
declaration counts are preservation evidence, not chapter-completion percentages.

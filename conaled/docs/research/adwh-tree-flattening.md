# Tree flattening: actual traversal, copying and growth

Issue #190 completes checkpoint 233's `Chapter03/TreeFlatteningCosts.lean`:
22 newly reconstructed declarations and the two perfect-tree helpers already
accepted under #181. The [24-row ledger](adwh-tree-flattening-ledger.json)
records exact source names, lines, destinations and semantic adaptations.
The archive SHA256 is
`8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63`;
the member SHA256 is
`1d3b29808ce0d6e2c6b2f48d91cddccd0ec307fda47d53b8144282277e512641`.
Both hashes and equality with the inspected extraction were verified. Historical
bytes remain unchanged.

## Representations and execution

`Resources.TreeFlattening.Core` implements actual recursive append traversal
and an explicit pending-tree stack on accepted `Bracketing.Tree`. Independent
output semantics use `fringeSpec`. `nodes` reuses the work projection of
`Resources.RandomAccessCosts.structuralSizeRun`; its two recurrence laws recover
the source constructor count. `pending` sums those counts and supplies the
well-founded measure. Cached sizes play no role.

`Cached` retains the literal source branches on raw `RandomAccess.Tree`.
`cachedFromTWithCost_erasure` and `cachedFromTsWithCost_erasure` equate the whole
measured result with the shared-tree execution after semantic erasure. They
preserve output and work, without requiring cache validity or perfection.
These source-facing executions do not call `erase`: the map occurs in the
simulation theorem and termination proof. No erased-tree construction pass is
silently charged zero in the source algorithm.

The recursive algorithm evaluates its left subtree, then its right subtree,
then actual `appendWithCost`. Append copies the left list and returns the
ordinary concatenation; its count equals that list's length. The stack expands
an internal node to left, right, then the old pending suffix. It emits a leaf
before proceeding and charges the final empty-stack test.

Counts distinguish constructor visits from copied left-list cells. A recursive
visit costs one composite unit, including leaf emission; stack expansion costs
one unit and its final empty test costs one. These are finite eager-output
models. They do not assert total allocated cells, peak space, compiler
instructions, arithmetic bit complexity, or lazy printing costs.

## Growth and consumers

`TreeFlattening.Growth` derives perfect-rank formulas using the accepted
`Perfect` predicate and `perfectTree` witnesses. `Resources.Growth` contributes
one reusable lemma: an explicit natural bound beyond a threshold implies
Mathlib `IsBigO` for real-cast counts at `atTop`. It requires no unnecessary
positive-coefficient premise; zero is also a valid bound when its hypothesis
holds. The two source growth results instantiate it with the original positive
constants and thresholds, and export standard `Asymptotics.IsTheta` statements
about actual cached-source executions.

The historical dependency consists only of the `NatO` and `NatTheta`
definitions. They are replaced by the standard interface and explicit natural
bounds, not copied into a new asymptotic framework. Recursive upper/reverse
constants are 3 and 2, both from rank one. Stack constants are 2 and 1, both
from rank zero. Growth is indexed by rank p, with scales p*2^p and 2^p; no
conversion to an arbitrary-size n-log-n theorem is claimed. No theorem from
historical `LogarithmicScales` is needed.

`Observation` composes existing squares and `Measured.bind`:

- `flattenAppend` runs the actual cached forest traversal and passes its output
  to actual suffix append. Work is pending nodes plus one plus output length.
- `flattenQuery` accepts either actual flattening square, constructs a fresh
  valid random-access representation from the produced list, then runs the
  accepted measured lookup. It retains all three costs. Malformed input caches
  are allowed: flattening ignores them and construction establishes validity.

The common query consumer is parameterized by the existing `Square` interface;
it introduces no execution framework or new representation invariant. Its
value theorem retains `flatten.spec`, so it is valid for every supplied square,
not only the two identity-spec flatteners. The agreement theorem specializes
the two actual flattening squares. Semantic decoding proves values; explicit
resource statements prove the distinct counts.

## Statement review and checked public applications

All new claims and definitions were reviewed against their intended domains,
quantifiers, ordering and resource meaning. The table records their connection
to `Examples/TreeFlatteningCosts.lean`; helpers are also consumed in the cited
public derivations. Value types remain universe-polymorphic. No equality or
ordering instance on values is required. Numeric growth claims cast natural
costs to reals only at the standard asymptotic interface.

| Claims and interfaces | Reviewed statement and checked use |
| --- | --- |
| `nodes`, `nodes_leaf`, `nodes_fork`, `pending`, `pending_append` | Shared full-constructor count, distinct from leaf count. Shape examples have five nodes; pending concatenation with a leaf has six. Termination decreases when a node is expanded. |
| `appendWithCost`, `appendWithCost_exact` | Actual copied-left-cell count; empty left costs zero. Repeated input `[1,1,2]` appended to `[3,1]` preserves order and multiplicity with cost three. The suffix consumer uses this same executable function. |
| `fromTWithCost`, `fromTWithCost_value`, `copies`, `fromTWithCost_count` | Output is independent ordered fringe; total is visits plus copying. Left/right-associated three-leaf trees have equal output, copy counts three/two and costs eight/seven. No balance or validity premise. |
| `fromTsWithCost`, `fromTs`, exact/refinement/singleton/suffix laws | Exact ordered `flatMap fringeSpec` and pending+1 count. Empty stack costs one, singleton leaf two, both three-leaf shapes six. Repeated values and a nonempty suffix exercise the public suffix/refinement laws. |
| Cached recursive/stack executors, both erasure simulations, cached value/exact laws | Whole measured results agree under erasure for every raw cache. Malformed cache99 and cache0 yield identical values and counts; the forest with an extra leaf returns `[1,2,3]` at cost five. A separate checked negation establishes that cache99 is invalid. |
| `nodes_perfect`, `copies_perfect` | With `Perfect p t`, nodes+1=2*2^p and twice copying=p*2^p. Rank-three tests use the accepted family witness to obtain 16 and24. No raw malformed tree is passed to these laws. |
| Recursive/stack perfect exact laws and recursive bounds | Exact equations include rank zero: recursive one versus stack two. The recursive upper bound needs p≥1; its rank-zero analogue is checked false. Rank-three laws prove actual output of eight sevens and costs27/16, plus bounds24≤2*work and work≤72. |
| `Resources.isBigO_of_nat_bound`, `recursive_flatten_theta`, `stack_flatten_theta` | Eventual bounds are standard filter/norm statements on real-cast Nat costs. Both growth proofs use the shared bridge. Examples consume the recursive upper BigO and stack reverse BigO projections, and instantiate explicit natural rank-dependent bounds. Constants and thresholds remain visible in the proofs. |
| Forest/tree representations, three flattening squares, `appendSquare`, `flattenAppend` value/cost | These decode actual outputs and compose actual traversal with actual copying. Repeated forest output plus suffix yields `[1,1,2,3,1]`, cost eight. Empty forest plus nonempty suffix costs one, including its final test. |
| `measuredConstructionSquare`, `flattenQuery` value/cost/agreement | Construction consumes the measured produced list; lookup runs on its actual fresh carrier. Malformed input cache99 produces query1=`some 2`, query2=`none`, with counts11/10. Arbitrary-query agreement consumes the public agreement theorem. Rank-three query0 costs50 recursively and39 by stack, retaining the flattening difference after common downstream work. |

The source's small numeric cases were already reducible. Their initial missing
connection was to reusable public contracts and composed consumers, not a
failure of the numeric propositions. The rebuilt cases now invoke erasure,
exact counts, perfect-rank formulas and composition laws. Statement review
retained the rank-zero exception, cache-untrusted domain and final empty test;
none was removed to make an example pass. The stack algorithm is not claimed
to be strictly cheaper for every tree: the leaf case disproves that claim.

## Validation and remaining scope

Targeted checks passed through direnv (1626 jobs):
`lake build Examples.TreeFlatteningCosts Examples.Bracketing
Examples.RandomAccessCosts Examples.RandomAccessEndCosts Examples.Resources`.
The ledger's 24 destination declarations and selected consumer/universe
signatures elaborated separately in Lean with universes displayed. Full fresh build, exhaustive audit,
independent reviews and map verification remain the integration gate.

This closes the selected source module only. Historical Asymptotics beyond the
two replaced predicate definitions, all LogarithmicScales declarations,
arbitrary-shape asymptotic classes, allocation/space analysis and lazy-output
semantics remain separate work.

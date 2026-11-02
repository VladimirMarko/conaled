# Joint relative orders from one shared permutation

Status: **source draft, not compiled or accepted**. This unit extends the
[relative-order draft](fdsa-permutation-order.md) and composes with the
[conditional-tail draft](fdsa-permutation-tail.md). Local FDSA-XU05 retains
its frozen requirements, source/API preflights, independent calculations,
immutable candidate and later validation. No chapter or algorithm obligation
is accepted by this source draft.

## Two actual observations and one joint law

For the existing complete, Nodup positions list, write
`O_A π := restrictedOrder positions A π` and
`η_A := uniformOn (orders positions A : Set (List I))`.
The sampled permutation π maps keys to priority labels. Each O_A reads its
inverse in the specified label order and filters to A.

The new observation is the ordinary pair `(O_A π, O_B π)`. Both components
use the same π. For fixed disjoint A and B under the original global uniform
law μ0, `uniformOn_restrictedOrder_pair_eq` states

```lean
μ0 {π | (O_A π, O_B π) = (xs, ys)} =
  if xs ∈ orders positions A ∧ ys ∈ orders positions B then
    ((Nat.factorial A.card * Nat.factorial B.card : ℕ) : ℝ≥0∞)⁻¹
  else 0
```

This formula includes every output pair, with zero mass when either
coordinate is unsupported. Neither subset must be nonempty and their union
need not cover I. Empty subsets have the sole order [] and 0!=1. Empty I
still has the identity permutation and a normalized original law.

The operation keeps the earlier DecidableEq I interface. Complete positions
provides local finite enumeration for the probability proof. There is no
public Fintype, Finite, key-order, inhabited-index or index-measurable-space
premise. The scalar source-event law requires measurable structure only on
the permutation sample, not on output lists.

`map_restrictedOrder_pair_uniformOn` adds the caller's existing list
measurable-space and measurable-singleton instances and states

```lean
μ0.map (fun π => (O_A π, O_B π)) = η_A.prod η_B
```

The canonical product measurable space is used for pairs. The right-hand
product is the conclusion about the actual paired observation; a newly
defined independent draw is not substituted for that observation. The two
old marginal map equations alone would not supply this joint equality.

## Simultaneous relabeling of the two supports

The implementation extends the existing PermutationOrder module so it can
reuse its private finite-list extension and relabeling helpers. It does not
export those helpers or introduce a generic action framework.

Consider two supported output pairs. Their A lists have exactly A as support
and the same length; their B lists have exactly B as support and the same
length. Disjointness makes each concatenation of an A list and a B list
Nodup. Extend the positionwise map between concatenations to one ambient
permutation σ. Splitting at the proved first-component length gives both
component maps and preservation of A and B separately.

The existing orientation law says that right-composing π with σ.symm maps
each observed list through σ. Thus the same sample bijection transports
both coordinates' fiber simultaneously. It need not fix unused labels
pointwise. The two-supported-order product finset covers all actual outputs,
and its disjoint fibers have equal mass summing to one. Its cardinality is
A.card! times B.card!, giving the reciprocal product in the scalar formula.

For the map law, the two finite nonempty order measures are explicitly
normalized, supplying the SFinite hypotheses of the ordinary product
formulas. Countable singleton extensionality then compares the actual map
with their product. List I is countable under finite I, not generally finite.
The factorial casts satisfy the conditions of ENNReal inverse multiplication.

## Reuse under a current observed-order law

The third public result, `hasLaw_filter_pair`, starts with the existing
`HasLaw Y η_S μ`, for an actual `Y : Ω → List I`. For fixed disjoint A,B⊆S,
it gives

```lean
HasLaw
  (fun ω => ((Y ω).filter (fun a => decide (a ∈ A)),
             (Y ω).filter (fun b => decide (b ∈ B))))
  (η_A.prod η_B) μ
```

The environment Ω can be any measurable space and μ can already be a
changed conditional measure. No finite or discrete source, uniform global
environment or stronger measurable-Y premise is added. HasLaw supplies
the required a.e. measurability and whole-observation map equality. Its
nonempty finite target supplies source normalization when needed.

The canonical pair-filter law on ηS follows by rewriting ηS as the old
actual global projection, composing maps and applying the two existing
nested-filter equalities. HasLaw.fun_comp then transports that canonical
law through Y. A and B may leave unused members of S. They must still be
contained in S: filtering cannot recover an outside label that Y almost
surely lacks. Valid support for an arbitrary Y is only an a.e. guarantee.

No new independence wrapper is introduced. Mathlib's existing
`indepFun_iff_hasLaw_prodMk_prod` connects a joint product HasLaw with
IndepFun when the actual marginal HasLaws are supplied.

## Connected examples

`Examples.PermutationJoint` reuses the earlier public Fin4 experiment. For
A={0,2} and B={1,3}, the new pair-fiber theorem gives mass 1/4 for outputs
([0,2],[1,3]), and the two old marginal theorems give mass 1/2 each. The
new pair map and old marginal maps are assembled as actual HasLaws, from
which the existing IndepFun predicate follows. Malformed [0,0] on the
left and [1,1] on the right each have mass zero through the new formula.

The main module also reuses the boundary module's Fin5 experiment and
conditions its actual full order to start with key 2. The initial HasLaw
comes from XU02's actual map. XU03 gives original event mass 1/5 and the
uniform law of the actual remaining order under the conditioned measure.

The new generic result consumes that tail law for A={0,1} and B={3,4},
which are fixed disjoint subsets of univ.erase 2. The resulting actual
tail-filter pair has a product law and supported-pair mass 1/4. Existing
conditional marginal HasLaws also expose its IndepFun statement. On the
head event, both filters equal the original A/B projections of the same
permutation; conditional a.e. transport gives their actual paired projection
the same product law and mass 1/4.

The environment itself has changed: the head event now has mass one instead
of 1/5. These observations can have a product law without the full environment
being its original global uniform measure. Every call retains the original
complete positions; the partial tail is never used as a complete enumeration.

`Examples.PermutationJointBoundary` keeps the following consequential cases:

| Case | Actual observation and public connection |
|---|---|
| Fin5, A={0}, B={1,2,3}, outside key 4 | The specified pair has mass 1/6 through the new scalar law; the union is explicitly proper. |
| Fin4, empty A and full B | The empty coordinate is [], and a specified full order paired with it has mass 1/24 through the new law. |
| Empty index type | The actual pair is ([],[]) with normalized mass one. Both the scalar formula and generic filter-pair law are instantiated from the actual empty whole-order observation. |
| Fin3 overlapping A={0,1}, B={1,2} | The actual paired event ([1,0],[1,2]) is the full-order first-key-1 event and has mass 1/3. Its two marginal masses are 1/2, giving product 1/4. |

The overlap event is connected through actual nested filters and a finite
supported-order table, then XU03's head law. This refutes dropping disjointness
from the general theorem; it does not claim every overlapping pair must be
dependent. The examples and source-written proofs are uncompiled. Independent
finite counts and source assessments do not supply kernel validation.

## Source use and remaining obligations

The source is the July 27, 2026 edition of
[*Functional Data Structures and Algorithms: A Proof Assistant Approach*](https://fdsa-book.net/functional_data_structures_algorithms.pdf),
SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The source preflight also reads the pinned
[AFP Quick Sort Cost archive](https://isa-afp.org/release/afp-Quick_Sort_Cost-2026-10-26.tar.gz),
SHA-256 `cda7ed0a00991dcf8a5adff2d9909d6e761b2d8fb9501425ed8b93dbf462f457`.

The AFP full cost-distribution correspondence uses the named
partition_random_permutations and pair_pmf step for the actual two filters
after a specified pivot. This unit supports that joint-law step. Expected
sums alone require only the conditional marginals; linearity itself requires
no independence.

The algorithm client must still establish actual partition and recursive
execution correspondences, pivot occurrence/rank conventions, strict versus
non-strict partition agreement on distinct pivot-deleted keys, full history
laws or fresh-choice coupling, and its source cost tariff. Equal payloads
do not identify occurrence indices. The book's two-way repeated-key behavior
is not replaced by a three-way sorter. AFP comparison counts and the book's
call/filter/append observations need their own pathwise bridges.

The product conclusion concerns two fixed disjoint internal orders. It does
not give independent global ordinal positions or raw assigned priorities,
arbitrary adaptive-set laws, or independence for overlapping treap operands.
A mixture over different revealed pivots is not automatically a product law.
Selection usually follows only one retained branch; its existing marginal
law suffices for that step. C10-117's conditional depth, Jensen, actual work
and correlated weighted charging remain open. A bound on E[d] does not
justify factoring E[dZ].

The immutable candidate and all prior/new cases still require matching
focused compilation, the full guarded build and exhaustive audit, both
independent final review axes and immediate candidate verification. The
repaired Chapter 1 and preceding shared base keep their own pending gates.

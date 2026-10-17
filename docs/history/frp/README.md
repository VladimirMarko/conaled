# The two 2015 FRP event denotations

## Verification status

`FRPEquivalence.lean` is an **untypechecked proof-script candidate**. There was no
Lean/Lake installation in the environment used to produce it, and attempts to
obtain one failed. Do not treat this artifact as a kernel-certified development.
It contains proof bodies rather than `sorry`s, extra axioms, or an assumed
representation equivalence. Elaboration and library-compatibility fixes may be
needed before a successful build. Mathematical arguments are summarized below.

Use the file in a Lean project with mathlib, from that project's working directory:

```sh
lake env lean /path/to/FRPEquivalence.lean
```

The final `#print axioms` commands audit the key declarations on a successful
build. `sorryAx` must not occur. This is a mathematical, noncomputable
specification; it is not a runtime event implementation.

## Source boundary

The primary sources are:

- Conal Elliott, `talk-2015-essence-and-origins-of-frp`,
  `essence-and-origins-of-frp.lhs`, especially the Events and Reactivity slides.
  https://github.com/conal/talk-2015-essence-and-origins-of-frp
- Conal Elliott, `talk-2015-more-elegant-frp`, branch `lambdajam-2015`,
  `more-elegant-frp.lhs`, especially the Original formulation and final Events slide.
  https://github.com/conal/talk-2015-more-elegant-frp
- Mathlib's existing possibly infinite lists, for comparison with the small
  self-contained `CoList` representation used here:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Seq/Defs.html

A denotation `Event A -> [(T,A)]` into non-decreasing lists does not assert that
*every* such list is the meaning of an Event. The sources could intend a narrower
image. Here `OldEvent` deliberately starts with the maximal **total-spine**
carrier described by the explicit type and ordering comment. Constraints beyond
ordering are then named and proved separately.

`CoList` represents total finite or omega-long lists, on BOTH sides of the
comparison. Haskell `[A]` in `Behavior [A]` is not automatically Lean `List A`.
The file does not model Haskell bottom, partial spines, partial elements, or
Scott-continuity of the grouping function. The equivalence is between total
mathematical denotations, not an equivalence of lazy computations.

## Main declarations

| Declaration | Content |
| --- | --- |
| `CoList` | Values indexed by a downward-closed subset of the naturals. |
| `CoList.finite_or_infinite` | Shapes are exactly finite initial segments or all naturals. |
| `OldEvent` | Such a co-list of timestamp/value pairs, with non-decreasing timestamps. |
| `Batch.Occ` | Occurrences of a time-indexed family of co-lists, ordered by time then local index. |
| `Batch.Admissible` | Each actual occurrence has finitely many strict predecessors. |
| `Numbering.rank` | Cardinality of an occurrence's strict predecessor set. |
| `Numbering.rank_initial` | The range of rank is an initial segment of the naturals. |
| `OldEvent.group` | Group by timestamp without changing simultaneous order or multiplicity. |
| `Batch.flatten` | Enumerate all occurrences in increasing chronological rank. |
| `eventEquiv` | The exact raw carrier equivalence, with both inverse laws. |
| `admissible_iff_representable` | Finite predecessors are necessary as well as sufficient. |
| `totalEventEquiv` | Restrict the equivalence to finite histories at every observation time. |
| `OldEvent.group_map` | Grouping preserves event mapping. |
| `OldEvent.group_snapshot` | Grouping preserves snapshot. |
| `Realization.before_eq` | Grouping preserves the strictly-before history. |
| `Realization.switcher_eq` | Switching agrees in the finite-history fragment. |
| `OldEvent.finite_before_of_following_occurrence` | Lossless merging with an occurrence at t forces finite history strictly before t. |
| `OldEvent.finite_before_iff_empty_or_last` | A chronological history is finite exactly when it is empty or has a last position. |
| `Examples.zeno_not_finiteHistory` | Ordering alone does not exclude finite-time accumulation. |
| `Examples.infiniteBatch_not_finiteHistory` | Ordering alone does not exclude an infinite simultaneous batch. |

The file includes the old pointwise behavior formulas and their reductions to
Reader-style operations. It does not mechanize a stable-merge implementation or
the final conversion of finite co-lists to native Lean `List`; the corresponding
mathematical arguments appear below and in the accompanying response. The source
slides do not fix complete meanings for `predicate` or `integral`, so this file
does not invent those meanings or claim an equivalence for them.

## Mathematical proof of the exact carrier theorem

For a batch function B, let its occurrences be pairs (t,k), where k is a live
index of B(t). Their values are B(t)[k]. Order these pairs lexicographically by
timestamp and then k.

**Necessity.** In a sorted co-list, the occurrence at index n has exactly n
predecessors. Grouping preserves this order, so every grouped occurrence has
finitely many predecessors.

**Sufficiency.** For an occurrence p let r(p) be the finite cardinality of its
strict predecessor set. If p<q then the predecessors of p form a proper subset
of those of q, so r(p)<r(q). The image has no gaps: for a nonminimal q, take its
largest predecessor p. All predecessors of q are p or predecessors of p, hence
r(q)=r(p)+1. Induction on the rank supplies every smaller rank. Thus r is an
increasing bijection onto a downward-closed subset of the naturals. Its inverse,
with each occurrence's timestamp and value, is the required sorted co-list.

**Inverse laws.** Ordered sets that are initial segments of the naturals have
no nontrivial order automorphisms: an index is the number of its predecessors.
Grouping and flattening preserve timestamp, label, and order. Consequently the
round trips fix every index and every value. This includes order and duplicate
values within a simultaneous batch; it is not equality of sets or multisets.

The exact statement is therefore:

```
OldEvent T A  ≃  {B : T -> CoList A // every occurrence has finite predecessors}
```

It does NOT require finite history at unoccupied times.

## Why the stronger finite-history condition appears

A Zeno sequence at times 1 - 1/(n+2) is a valid raw old event. Every occurrence
has finitely many predecessors, although there are infinitely many occurrences
before time 1. An infinite batch at time 0 is also a valid raw old event.

If a lossless sorted merge of an event e and a singleton at t existed, the
singleton would occupy some natural index N. Every input occurrence strictly
before t must inject into one of the N earlier output positions. Thus e must
have finitely many occurrences before t. Closure under arbitrary such singletons
forces finite history at every real time. This necessity argument does not depend
on an implementation algorithm.

The standard left-biased chronological merge does not solve the raw-carrier
problem: merging the Zeno list with a singleton at 2 keeps producing the Zeno
list and never includes that singleton. Its grouped meaning therefore differs
at time 2 from pointwise append of the grouped inputs. There is no unconditional
merge-homomorphism theorem on the maximal raw carrier.

Similarly, the chronological prefix before t is an initial segment of the
natural indices. If it is infinite it has no last position. Thus the specified
polymorphic last-based switch requires finite histories for total values at all
observation times.

## Finite batches and the earlier `List` model

Over real time, finite history implies every individual batch is finite: the
batch at t injects into the history before t+1. For a function B of finite lists,
finite occurrence-history before each t is equivalent to finiteness of
`{s | s < t and B(s) is nonempty}`. One direction projects occurrence positions
to support times; the other takes a finite union of finite batches.

Consequently the total finite-history restriction of the raw equivalence has a
corollary whose new side is exactly the finite-list, finite-past-support model
used in the preceding response. This is a separately justified total fragment,
not something that follows from the words “non-decreasing times” alone.

## Preservation of the operations

Mapping and snapshot change only occurrence labels. Their equalities follow by
retaining the same position order and changing corresponding labels on both
sides. The included Lean scripts use that general statement.

For lossless merge of finite-history events, order the disjoint union of input
occurrences by `(time, input-side, input-index)`, putting the left input first
on ties. Every bounded-time prefix is finite, so this union has a sorted
co-list enumeration. Its batch at t consists exactly of the left batch followed
by the right batch. This proves the pointwise list-append equation, including
its tie convention. Empty and singleton events satisfy their grouping equations
immediately. This merge argument is mathematical here, not mechanized in the
file.

For switching, the realization restricts to an order isomorphism between the
occurrences strictly before t. It therefore carries an empty history to an
empty history and a last position to the last position. Corresponding positions
carry the same behavior function. Evaluating that function at t gives the same
result in both presentations. The included script encodes this proof using
finite ordered maxima. It does not change `<` to `<=`.

## The slide comprehension is mathematical notation here

The literal Haskell definition using `[a | (ta,a) <- os, ta < t]` does not in
general terminate as a complete finite list on an infinite input, even when only
finitely many items satisfy the test. Searching the remaining infinite tail
continues forever. A literal `last` of that filtered result can therefore diverge
even for non-Zeno events. On sorted lists, `takeWhile` rather than unrestricted
`filter` can exploit crossing the threshold, but Haskell divergence and input
progress still require their own semantics.

The Lean `before` operation instead denotes the mathematically ordered subset
of occurrences before t. This distinction must remain explicit in any later
implementation or domain-theoretic verification.

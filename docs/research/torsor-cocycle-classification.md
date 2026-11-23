# Fixed-cover cocycles and torsors

The cocycle presentation classifies the full category of torsors admitting a
trivialization on a specified cover. The category retains every equivariant
map, including automorphisms. A cover need not trivialize every torsor.

## Inputs and conventions

For a split sheaf family `A` over `X`, a `Cocycle.Datum G A` assigns a group
section `c(x,a,b)` to each pair of lifts of a section `x`. The input consists of
these labels, identity, multiplication and restriction equations:

```
c(x,a,a) = 1
c(x,a,b) * c(x,b,k) = c(x,a,k)
```

These are primitive labels and laws. No descended torsor or effectiveness
certificate is an input. A `Gauge c d` is a sheaf morphism from the cover total
space to the group sheaf, satisfying

```
c(x,a,b) * g(x,b) = g(x,a) * d(x,a,b).
```

The group acts on the torsor on the left. Labels describe right translations,
so a label `g` followed by `h` has label `g * h`. The existing smooth Cech
presentation also uses forward action labels; its inverse-label comparison
remains necessary. No commutativity assumption is made.

Primitive labels, gauges and overlap comparisons retain independent base,
arrow and value universes. Effective classification uses values in `Type (max u v)`, matching the existing constructive torsor descent API over a base
in `Type u` with arrows in `Type v`.

## Classification and recovery

`Datum.toDescent` makes the transition `p ↦ p * c(x,a,b)` on the regular torsor.
`ofDescent` reads its label at the identity section. Their exact recovery laws
connect this presentation to the existing effective descent construction.
`gaugeDescentEquiv` compares every gauge with every compatible equivariant
local map.

When the display of `A` is locally surjective, `equivalence` compares cocycles
with `Admitted A`, the full subcategory of torsors whose restriction has a
trivialization. Admission is a proposition expressed by `Nonempty`; objects
do not retain a chosen trivialization. `chosenCocycle`, `chosenRecovery` and
`chosenRecovery_reindex` separately expose the construction from a selected
local trivialization and its exact local recovery. The inverse of the
categorical equivalence chooses such a witness.

`glueHomEquiv` recovers all arrows, and `stabilizerEquiv` specializes it to
endomorphisms. Torsor maps are automatically invertible by the existing
principality theorem. `classEquivalence` then passes to the quotient relation
“there exists a gauge” and to isomorphism classes of admitted torsors. It makes
no claim about refinement classes, sheaf cohomology, or an additive group
structure.

`trivialRecovery` identifies identity transitions with the globally trivial
torsor. `coboundaryGauge` exhibits the gauge from identity transitions to
`g(a)⁻¹ * g(b)`, and `coboundaryRecovery` gives the resulting trivialization.

## Overlap and cover interfaces

`splitOverlapEquiv` compares stage labels with a sheaf morphism on the double
overlap satisfying diagonal and triple-overlap equations. `overlapEquiv`
transports that independent presentation to the actual pullbacks of an
arbitrary sheaf map. `Gauge.overlap_compatible` exposes the gauge equation as
an equality of sheaf morphisms on the double overlap.

The local-isomorphism construction now lives in `SheafTorsorLocalIso`. Both
torsor and quotient wrappers use the same transport and recovery proofs; the
existing smooth recovery definitions specialize them. `SheafTorsorLabels`
supplies regular-arrow reconstruction and label operations to the generic
classification, quotient arrows and the existing smooth presentation.

## Refinement and base change

`CoverMap` is a natural map from the finer cover fibers to the original cover
fibers over a specified map of bases. It pulls back both cocycles and gauges,
with strict identity and composition laws. `baseChange` is the cartesian
specialization, and `ofSquare` accepts an ordinary commuting square of sheaf
maps.

`comparison` identifies the glued pulled cocycle with the actual reindexed
torsor. `comparison_reindex` and `comparison_evaluation` describe its local
behavior. `comparison_natural` applies to every gauge; `comparison_ident`
and `comparison_comp` prove the identity and successive-change diagrams.
These are equations between the comparisons themselves, beyond the existence
of some isomorphism between the endpoints.

The induced functor on admitted torsors keeps all their arrows.
`comparisonNatIso` connects this functor to cocycle pullback and gluing.
For a refinement over the same base, `refinementFullyFaithful` recovers every
gauge between the original cocycles. A finer cover can admit more torsors, so
this statement does not assert essential surjectivity. `refinement_image`
characterizes the image by admission on the original cover.

`admitsCover_iff_split` identifies admission on an ordinary sheaf map with
admission on its split display. `admitsCover_family` identifies admission on
the categorical coproduct map with admission on every component. It also
applies to an empty indexing type. Together with the existing joint-cover
criterion, this gives the fixed-cover classification for jointly locally
surjective families without assuming that an individual member covers.

## Scope and later extensions

The main API is categorical. The class quotient is a downstream application
and does not replace gauges or stabilizers. All-cover or nonabelian
cohomology comparisons would need a separate refinement-class construction
and an explicit comparison theorem. Abelian cohomology and its group law
would require their own hypotheses and proofs.

The reference [Stacks Project, torsors](https://stacks.math.columbia.edu/tag/03AG)
uses equivariant sheaf maps and proves that triviality is equivalent to a
section. Its abelian first-cohomology classification is broader than the
fixed-cover class quotient established here.

## Checked consumers

The examples retain the quarter-turn clutching torsor and its obstruction to a
global section. Its decoded primitive cocycle recovers the existing interpreted
torsor. Constant permutation gauges distinguish automorphisms and detect their
noncommuting composition; coboundaries have explicit global trivializations.

The proper two-chart family admits the existing nontrivial torsor even though
neither chart covers by itself. The ordinary-map and family admission bridges
produce its cocycle and recovery. Swapping the charts retains every gauge, and
nonidentity scaling maps exercise base-change naturality. The identity-cover
negative control prevents confusing fixed-cover admission with all torsors.
An empty-family control checks that the family admission theorem does not
silently choose an index.

Two successive nonidentity negations of the two-point base check the exact
recovery-arrow composition equation. The generic comparison theorem and all
committed consumers use default budgets. A larger specialization on the smooth
proper cover exceeded bounded kernel heartbeat trials; its resource evidence
is retained for #636. The smooth cover still checks recovery, all-gauge
naturality and chart-swap refinement.

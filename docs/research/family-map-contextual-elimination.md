# Shared family-map experiment for contextual elimination

This bounded [#433] experiment tests a mathematical comparison shared by the
arrow-model and derivation-indexed approaches. It implements neither approach.
The prior all-torsor smooth interpretation and descent milestones are recorded
in [smooth-source-interpretation.md](smooth-source-interpretation.md).

## Result and precise inputs

`Internal.PathTransport.FamilyMapElimination` proves strict equality of functors
and sections for a changing motive family. The family transformation need not
be invertible, full or faithful. No source rule or source proof is changed.

| Declaration | Inputs | Checked conclusion |
| --- | --- | --- |
| `ContextualElimination.normalize_map` | Arbitrary category-valued families `A,B`, natural transformation `α : A ⟶ B`, functor `t` into the total category of `A`, and an actual isomorphism from its base projection to `K` | Mapping the normalized functor equals normalizing the mapped functor |
| `NormalizedEquivalence.eliminate_map` | A normalized equivalence, a branch over its forward functor, and `α` | Mapping the eliminated branch equals eliminating the mapped branch |
| `Telescope.eliminate_map` | Any finite dependent telescope and normalized equivalence at its root, with `α` between motives at its tip | The same equality after the existing repeated dependent extension construction |
| `EquivalenceSquare.eliminate_familyMap` | Two normalized equivalences, a **given** coherent contraction square, independently specified motive families related by `α`, and equality of the mapped branch functors | Strict equality across the context comparison and the changing motives |
| `eliminateSection_mapFamily` | Groupoid-valued motives, `α`, and an actual section of the branch family | Equality of sections, including their action on arrows |
| `Instance.contextualJ_mapFamily` | The existing groupoid model, arbitrary path type/point, arbitrary finite dependent tail, two motives, `α`, and a branch | Compatibility of the existing `Instance.contextualJ` with the motive transformation |

In `Telescope.eliminate_map` and `contextualJ_mapFamily`, the tail is fixed and
its branch is obtained by the existing pullback construction. Each declaration
in that tail may depend on the entire preceding context. These theorems do not
compare independently changing tail families.

The cross-context theorem consumes the existing `EquivalenceSquare.Square`.
Its forward, inverse and counit coherence are hypotheses about the contractions,
not a hypothesis that J already commutes. The additional branch equation is
equality of whole functors, including arrows. This experiment does **not**
construct the contraction square associated to smooth parameter restriction,
or prove its propagation through independently changing tail families.

## Why the conclusion is equality

Normalization carries a functor to one lying strictly over the prescribed base
map. The proof of `normalize_map` uses the actual normalization comparison
isomorphism. Naturality of `α` gives equality of the normalized objects. The
component of the comparison is then proved to be precisely equality transport,
including its fiber arrow. `Functor.ext_of_iso` therefore yields equality of
functors. An arbitrary natural isomorphism alone would not justify this step.

The section map is built by applying `Grothendieck.map` to the section functor
and using the existing `Section.ofOver`. Its lift is proved equal to that mapped
functor. Injectivity of the section presentation transfers the functor theorem
to equality of sections. The final contextual-J theorem specializes this result
to the existing `rootTailEquivalence` and `contextualJ`; it does not define a
replacement eliminator.

This proof uses Mathlib's Grothendieck construction and the repository's existing
normalization and repeated-tail APIs. It does not copy a standalone orbifold
proof or require additional categorical axioms.

## Examples and statement review

`Examples.FamilyMapElimination` uses the projection

    Discrete Bool × C4 → C4.

The map forgets the Boolean object component while retaining every C4 isotropy
arrow. Checked lemmas show it is not injective on objects and is not full. The
latter rejects treating it as an equivalence; noninjectivity on objects alone
would not reject a categorical equivalence. For every chosen Boolean and C4
loop, the mapped arrow is exactly the original loop, and the map on these chosen
loops is injective. Thus the example changes the family without discarding its
selected isotropy labels.

The corresponding constant groupoid families have a section over every context,
so the branch cases are inhabited. The examples apply the shared section theorem
after one arbitrary dependent extension and after an arbitrary finite dependent
telescope. They do not require the declaration in the extension to be constant.
The generic theorem itself permits nonconstant motive transformations as well;
only this noninvertible test fixture is constant in its context.

Statement review checked the distinction between transformations and
isomorphisms, equality of functors versus object equality, arrow preservation,
the arbitrary finite induction domain, and the exact contraction-square
hypotheses. A section-valued result retains arrow action. No faithfulness or
invertibility premise is hidden in the family-map theorem. The hypotheses of
the cross-context theorem retain the contraction coherence needed by the
existing elimination theorem.

Development first exposed the absent normalization/family-map connection.
Object naturality supplied its object equation; direct morphism comparison
introduced equality transports. Using the existing normalization isomorphism
then proved those transports coherent and established strict equality. Focused
builds check the final declarations without placeholders or raised heartbeats.

## Consequences for the two possible routes

The shared interface mentions categories, family transformations, sections,
normalized equivalences and contraction squares. It mentions neither an arrow
model nor derivation-indexed comparison records. Either route can construct
these inputs and consume the same results. Implementing one route need not
change this interface or the other route's prospective implementation.

The experiment removes one uncertainty: a noninvertible motive transformation
is compatible with the selected normalization by strict equality. It does not
settle the remaining architecture. Both routes still need construction of the
path-contraction comparison for changing signature families, propagation
through changing dependent tails, and the relevant section/substitution and
conversion comparisons. The arrow-model route additionally needs its complete
model/projection construction; the derivation-indexed route needs coherent
comparison choices across shared indices. Generated smooth context/family/
section descent remains required under either route.

No claim is made that full shared arbitrary-family-and-tail compatibility,
parameter-indexed smooth-model closure, or #433 is complete. The parent workflow
owns the fresh acceptance build, exhaustive audit, public coverage and independent
review. Focused commands and selected-root audits are recorded in the external
#433 experiment handoff.

[#433]: https://github.com/VladimirMarko/conaled/issues/433

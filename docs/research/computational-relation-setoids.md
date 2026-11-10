# Computational relation setoids

`WitnessSetoids` supplies the computational relation instance missing from the
Prop-valued `SetoidCategory` specialization. Its source is Felix revision
`6f36d28097db7ea5f5df3263db3e8be08f74e490`, `Instances/Setoids.agda`.

The object has a carrier in `Type u` and a relation in `Type v`, with selected
reflexivity, symmetry and transitivity operations. These operations satisfy no
additional equations. A morphism retains its total function and its action on
relation witnesses. Pointwise morphism relations retain the target witnesses.
Category, terminal, initial, product and sum constructions support independent
carrier and witness universes. Exponentials use `Obj.{u,u}`, matching the
source's `Setoid ℓ ℓ`; their carriers contain congruence data. This does not
assert closure at arbitrary independent universes.

The category congruence first uses the selected pointwise witness, then the
second morphism's congruence, in the source's order. Evaluation likewise uses
transitivity on the supplied function witness and the selected congruence of
the second function. Curry uses the chosen reflexivity witnesses. Left and
right distribution rearrange the supplied product/sum witnesses directly.

The erased adapter uses `Nonempty` only at its explicit boundary into the
Prop-valued category. It preserves identity and composition as equal arrows.
Product and sum comparisons preserve underlying values exactly; their relation
comparisons work in both directions. Evaluation and curry commute with the
product and exponential comparisons as equal arrows. No selected witness is
recovered from its erasure, and the exponential comparison is not declared an
isomorphism.

`Examples.WitnessSetoids` uses Boolean carriers with two witnesses for every
pair. Two arrows have the same underlying function but different congruence
actions; erasure identifies them. Distinct pointwise witnesses survive category
congruence. Product, sum, curry and both distribution examples inspect the
actual selected witnesses. These checks would fail to describe this model if
all relations were replaced with lifted propositions.

Statement review: laws are Type-valued witnesses, not equalities of witnesses.
Erased equalities compare Prop-level congruent functions, whose proof fields are
irrelevant. No higher coherence or uniqueness is assumed. The selected-feedback
congruence boundary from #451 remains unchanged.

This is an implementation checkpoint. Right-distribution witness laws, the
remaining operation/law recovery checks, the derived-declaration inventory,
independent review and full candidate validation are still pending.

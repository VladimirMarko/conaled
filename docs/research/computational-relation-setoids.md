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

The direct universal-property packages preserve the source's chosen witness
operations: product projection/pairing, sum restriction/case analysis, and
closed symmetry/uncurrying. Both distribution inverse-law packages are present.
`erase_relation` maps every selected law to its pointwise erased relation;
`erase_ident` and `erase_comp` additionally give exact arrow equalities.
`erase_terminal`, `erase_initial`, `erase_distribution` and
`erase_rightDistribution` check exact underlying operations. Product/sum
round trips recover arrows, and evaluation/curry use the comparison maps
explicitly. Generic derived structural reasoning is inherited from #455;
the checked swap/pair specialization exercises it on this instance.

| Pinned declaration | Checked computational instance |
| --- | --- |
| `Zoid`, `_⟶_` | `Obj`, `Hom` |
| `products`, `coproducts`, `exponentials` | `unit`, `prod`, `zero`, `sum`, `exponential` |
| `rawCategory`, `equivalent`, `category` | `ops`, `equiv`, `congr`, `laws` |
| `rawCartesian`, `cartesian` | `terminal`, `products`, their congruence/laws, `product_universal` |
| `rawCocartesian`, `cocartesian` | `initial`, `coproducts`, their congruence/laws, `coproduct_universal` |
| `rawCartesianClosed`, `cartesianClosed` | `closed`, `closed_congr`, `closed_laws`, `closed_universal` |
| `rawDistributive`, `distributive` | `distribution`, `rightDistribution`, both witness law packages |
| inherited active structural reasoning | #455 generic operations, laws, preservation and transport specialized to these packages |

The source contains no additional active indexed declarations in this instance
module. Its commented trace remains subject to #451's explicit selected-feedback
and congruence contract. This checkpoint does not claim full #8 acceptance.
Independent review and exact-candidate full validation remain pending.

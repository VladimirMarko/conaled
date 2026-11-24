# Foundations follow-up: mod-four fiber and mod-two action

This follow-up was requested after all initial reports were saved. I have now
read `alternatives.md`; the original `foundations.md` is unchanged. The claims
below are paper derivations against the pinned interfaces, not new Lean checks.

The proposed finite mod-four fiber is mathematically compatible with the actual
`StrictTwoTransformation.Trans` interface. I find no obstruction from its
`naturality₂` field or from the strict family laws. It provides a stronger
connected loss control than my initial thin path-family recommendation, so I
recommend using this richer fixture for the implementation child, while keeping
the initial thin fixture as the smaller checked admission baseline. A general
higher correspondence core is still unnecessary.

## The finite fiber has the required strict 2-category laws

Write `Q=ZMod 2`, `R=ZMod 4`, and `π:R→+Q` for the additive reduction map.
The proposed fiber has one object, arrows `m:Q`, and cells

```
K₂(m,n) = { r:R // m = n + πr }.
```

Choose arrow composition `m≫n=m+n`, cell vertical composition by addition of
labels, and both whiskerings to retain the label. For `r:m⇒n` and `s:n⇒p`,

```
m = n+πr = p+πs+πr = p+π(r+s).
```

This is the boundary of the chosen vertical composite. Horizontal composition
similarly has label `r+s` and boundary `m+k = n+l+π(r+s)`. All associativity and
unit equalities reduce to those of the two additive groups. The strict
associator and unitors must be equality transports with label zero. Interchange
reduces to commutativity of R, and inverse labels are `-r`. Thus the proposed
actual `Bicategory.Strict` and local groupoid structures follow from finite
abelian-group equations. These are derived laws, not assumed final coherence
fields. There is no need to formalize an abstract crossed-module theory first.

## Strict transformation naturality₂ imposes no extra obstruction

For `α:Q`, let `τ_α:Id_K⇒Id_K` have component the fiber arrow α. Its arrow
naturality is

```
f + α = α + f.
```

The actual source interface requires, for every `r:f⇒g`,

```
r ▷ α ≫ eqToHom (naturality g)
  = eqToHom (naturality f) ≫ α ◁ r.
```

Both sides retain the same label `r`, because whiskering preserves it and both
equality-transport cells have label zero. After the stated source/target
identifications, subtype extensionality proves this equality. This is a proof
of naturality against genuine fiber 2-cells; arrow-level commutativity alone
would not have discharged the field.

For `F:B²Q→StrictTwoCategory`, use this K as its fiber, identity 1-arrow
transport, and `F.map₂ α=τ_α`. Composition of transformations adds their
components. Source `DoubleDelooping` uses `SingleObj`'s reverse multiplication
convention, so its additive cell composition may print β+α while the component
composite prints α+β. Commutativity supplies the required equality. The strict
transformation extensionality theorem then proves equality of transformations
from equality of components, since naturality fields are host propositions.
The family whiskering laws reduce to whiskering these transformations with
identity functors and the corresponding equality transports. None requires
quotienting R-labels or demanding they be zero.

The implementation must prove the zero-label formula for equality transports
and both whiskering label formulas before using this argument. That is a small
explicit prerequisite, not an additional mathematical axiom.

## The dependent total boundary and parallel loss are sound

An actual total cell has base component α and fiber component of type

```
ρ : p_m ⇒ (F.map₂ α).app(*) ≫ p_n.
```

Writing the R-label of ρ as r gives exactly

```
D(m,n) = { (α:Q,r:R) // m = n+α+πr }.
```

In particular, at `m=n=0`, `d₁=(1,1)` and `d₃=(1,3)` are both well typed.
Their complete source, target and base component agree; their actual fiber
cells differ. Reading the R-coordinate gives observations 1 and 3, so no
observation-reconstructing map can factor both through erasure of r while
retaining only `(m,n,α)`. This is a genuine parallel-cell information-loss
argument. Replacing r by zero at α=1 separately fails typing.

The connection is not an appended arbitrary tag: parity of r must cancel the
nonzero base action at these fixed endpoints. Moreover, the endomorphism group
`D(0,0)` is isomorphic to R by r↦(πr,r), and the selected d₁ has order four:

```
d₁ ≫ d₁ = (0,2) ≠ identity,
d₁ ≫ d₃ = identity.
```

The square has zero base component but a nonzero fiber component. This makes a
particularly useful additional control: retaining only the base α loses a
nonidentity composite, even when the composite's base is identity. It also
shows why describing this fixture as a copy of the thin path family plus an
unexamined label would miss its composition behavior.

The hom-groupoid is now non-thin and has nontrivial isotropy. The stronger loss
claim is still about the displayed erasure/observation map. It does not imply
that every change of presentation or every equivalence loses the cell.

## Connection to correspondence routes and actual threefold composition

The alternatives report's point-selection comma chain is sound. A morphism of
`H=TwoFamily.Hom F x x` is an actual total 2-cell; a comma object for
`Point→H←Point` selecting `p₀` stores precisely a member of `D(0,0)`.
The cell encoder/decoder and both roundtrips must establish that identification.
No comma morphism is being called a total 2-cell, and no total 3-cell follows.

For the implementation child I suggest combining the stronger fiber fixture
with the explicit threefold action from my initial report. Use the third
correspondence apex `Discrete (Q×Q)` rather than an inert Boolean, and read its
entries as the total arrows `p_k,p_l`. Its two interpreted routes are

```
HL = (d ▷ p_k) ▷ p_l
HR = d ▷ (p_k ≫ p_l).
```

Their endpoints are the respective left/right bracketings of the three total
arrows. With `am` and `an` the source and target `Category.assoc` equalities,
require exactly

```
HL ≫ eqToHom an = eqToHom am ≫ HR.
```

The existing `TwoFamily.whisker_right_compose` proves this after the comma
reassociation's full boundary projection identifies d. Select both d₁ and d₃,
with k=l=1. Both actual right factors are nonidentity, both α=1 and the fiber
labels 1/3 survive, and the intermediate endpoints shift from 0 to 1 before
returning to 0. Also check k=1,l=0, so cancellation cannot hide a map that ignores
the last correspondence. This produces a connected finite diagram with both
comma reassociation and actual total-cell threefold reassociation.

Under Boolean/mod-two representation change, use the same R-label type and
transport π through `SecondIdentity.encode.symm` for the Boolean action. Map
m,n,α by `encode` and keep r. This preserves the boundary, addition, all full
cell constructors and the two whiskerings. Hence it derives the representation
functor on H and the two `Comma.post` maps, rather than requiring an assumed
square. The two representation/reassociation routes preserve whole cells and
all tail entries; after interpretation they satisfy the same aligned-cell
comparison above. The r=1/r=3 observation and the `(0,2)` square control survive
representation transport unchanged.

## Selected next decision and validation boundary

Choose the richer finite fixture if the child is intended to retain an
independently selected parallel fiber witness as well as nonzero base action.
Its admission is a precise implementation first step: construct K, its strict
transformation τ, and F; prove encode/decode to actual `TwoFamily.Hom`; check d₁,
d₃, their unequal fiber observations and the nonidentity square `(0,2)`. Follow
with the actual comma chain and interpreted threefold square above. The finite
arithmetic and the inspected structural interfaces give a paper derivation of
feasibility, but no new Lean K/F proof has been executed in this follow-up.

If that admission fails, preserve the exact failed `naturality₂`, strict-family
or cell-roundtrip judgment as the bounded prerequisite. Do not weaken it to a
product label or claim a general mathematical obstruction from elaboration
failure. Existing sigma regrouping and ordinary SpanAction/SpanInterpretation
remain unchanged, including noninvertible ordinary apex maps and #633's
completed coherence.

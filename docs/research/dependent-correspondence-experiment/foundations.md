# Foundations assessment: connected finite dependent-cell correspondences

Source pin: `040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e`.
This is an independent initial assessment for #698. I previously supplied the
foundations perspective for #697 in this agent context. I have read the #698
brief, full issue specification, relevant source and the #694 report, but no
other #698 perspective report. The #697 work concerns a different native path
foundation; none of its proposed truncation lemmas is assumed here.

**Recommendation:** implement a finite, explicitly dimension-shifted
correspondence experiment on the hom-category of an actual `TwoFamily.Total`.
Use the finite path family over `B²(C₂)`, and let the last correspondence supply
two arrows that right-whisker its selected dependent cell. The two interpretations
then have genuinely different threefold boundaries, compared by the existing
`TwoFamily.whisker_right_compose` theorem. Derive representation compatibility
from the Boolean/mod-two group equivalence and exact decoding of cells. No new
higher core or caller-supplied associativity field is needed for this contract.

The recommendation is limited to a nonzero dependent **base** 2-cell with a
forced fiber boundary. It does not establish a nonzero independent fiber
2-automorphism, nontrivial second homotopy group, or correspondence semantics
in arbitrary 2-groupoids. Those would be stronger contracts. The issue's stated
nonzero dependent-cell requirement does not require those stronger properties.

## What the source already establishes

The [TwoFamily definitions](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/SquareKit/Internal/PathTransport/TwoFamily.lean)
make `Family Γ` a strict pseudofunctor to `StrictTwoCategory`. Its total arrows
are pairs `(f,u)`. A total 2-cell between `(f,u)` and `(g,v)` retains

```
α : f ⇒ g
ρ : u ⇒ (F.map₂ α).app a ≫ v.
```

`evaluation`, `Hom`, and `TwoGroupoidHom.cell` implement that exact dependent
boundary. `compose` transports the earlier fiber arrow with the later base
arrow. Both whiskering operations act on actual base and fiber cells.
[TwoFamilyCoherence](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/SquareKit/Internal/PathTransport/TwoFamilyCoherence.lean)
proves vertical compatibility, interchange, the total bicategory and strictness.
Its associators are equality transports between total arrows. This strictness
identifies bracketings of 1-arrows; it does not erase total 2-cells.
`whisker_right_compose` is particularly useful below because it states both
endpoint transports explicitly.

[TwoGroupoidHom](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/SquareKit/Internal/PathTransport/TwoGroupoidHom.lean)
constructs these hom-categories by a CoGrothendieck construction and proves
vertical invertibility from groupoidal input. Its `fiberCell` is an actual
fiber 2-cell, not a Boolean annotation or equality of whole records.
The [integer application](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/Examples/TwoGroupoidHom.lean)
has both a nonzero fiber loop and exact encoding/decoding for the path-family
boundary. They are separate specializations. It would be incorrect to claim
that the path-family example's fiber equality already supplies the independent
fiber loop.

The [existing path family](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/Examples/TwoFamily.lean)
inhabits the full strict-family API. Its nonzero cell is between integer arrows
1 and 0, with forced boundary `m = n + α`; its projection and both whiskerings
retain `α = 1`. The concrete
[TwoGroupoidPath](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/SquareKit/Internal/PathTransport/TwoGroupoidPath.lean)
is locally thin: a fixed pair of arrows determines the cell's base label.

[SecondIdentity](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/Examples/SecondIdentity.lean)
supplies finite groups `Bit`, `Label`, their multiplicative equivalence `encode`,
and independent observations. Its nonzero 2-automorphisms are a different
stronger discriminator than the thin path-family cells used here.
[GroupoidCorrespondence](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/SquareKit/GroupoidCorrespondence.lean)
retains `BG` 1-arrows in comma objects, proves full recovery and the selected
representation/reassociation square, and derives `commaIsDiscrete` for arbitrary
ambient categories when both apex categories are discrete. The last helper,
`discreteEquivalence`, and Mathlib `Comma.equivProd`/`Comma.post` are directly
reusable below. The specific `Left G`, `Right G`, and `changeBoundary` definitions
are specialized to `SingleObj G`; they cannot be applied unchanged to the
path-family hom-category, which has two different objects in the finite case.

[TwoFamilySigmaRegroupHigher](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/SquareKit/Internal/PathTransport/TwoFamilySigmaRegroupHigher.lean)
provides inverse strict pseudofunctors for dependent pair regrouping.
[Its cell construction](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/SquareKit/Internal/PathTransport/TwoFamilySigmaRegroupCells.lean)
retains the second fiber cell with the required transports, and the
[application](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/Examples/TwoFamilySigmaRegroup.lean)
checks independently selected integer observations and inverse recovery.
This is useful existing machinery for a future experiment with nested genuinely
non-discrete fibers. It does not itself identify a sigma total with the comma
apex of a correspondence. That bridge cannot be asserted by renaming pairs.
The selected finite experiment below avoids needing that more general bridge.

## A finite family, including the exact dependent boundary

For a commutative group `G`, take

```
Base_G  = DoubleDelooping.Space G
Fiber_G = LocallyDiscrete (SingleObj G).
```

Define `F_G : TwoFamily.Family Base_G` to have constant fiber `Fiber_G`,
identity action on the sole base 1-arrow, and action on a base 2-cell `α : G`
given by the strict transformation with component `Discrete.mk α`.
Commutativity proves transformation naturality. Identity, multiplication and
whiskering laws are proved from the group/category operations, not extra fields
that assert the desired final coherence. This is the finite/general-group
version of the integer construction already present.

Let `x_G` be the selected total object and `p_m : x_G ⟶ x_G` the total arrow
with fiber arrow `m`. A total cell `p_m ⇒ p_n` has the following exact coordinate
presentation:

```
Cell_G(m,n) = { α : G // m = n * α }.
```

Here `SingleObj` composes by reverse multiplication, so the boundary is
`m = n * α`, not a silently chosen multiplication order. A coordinate cell
encodes into the actual `TwoFamily.Hom` morphism as
`TwoGroupoidHom.cell α (eqToHom (Discrete.ext boundary))`.
Decoding reads its actual base component and obtains the boundary from
`LocallyDiscrete.eq_of_hom` on its actual fiber component. Require both roundtrips
as theorems, following the checked integer `pathCellDecode` pattern.

For `G = Bit`, use additive Boolean notation only in the worked example:

```
m = true, n = false, α = true
true = false XOR true.
```

The total cell is nonzero in its base projection and its fiber boundary depends
on that nonzero action. Replacing `α` by false while keeping these endpoints is
untypable: it would require `true = false`. The fiber 2-cell itself is a
locally-discrete equality witness; no independent nonzero fiber label is claimed.

A bounded isolated Lean probe has **checked** `F_G` for arbitrary `CommGroup G`,
its total object/arrows/cell constructor, the Boolean nonzero cell, its observed
base value 1, right-whiskering retention, and the false replacement equation's
negation. It has not checked coordinate roundtrips or any new comma definitions.

## The actual three correspondences

Let `K_G = TwoFamily.Hom F_G x_G x_G`, with its existing hom-category structure,
and `D_G = Discrete G`. Define `J_G : D_G ⥤ K_G` by `m ↦ p_m`. Let `P` be
`GroupoidCorrespondence.Point`. Use this selected chain:

```
S1 : P   ← D_G       → K_G       (terminal, J_G)
S2 : K_G ← D_G       → P         (J_G, terminal)
S3 : P   ← D_(G×G)   → P         (terminal, terminal).
```

The two coordinates of the last apex are **two actual total arrows** `p_k,p_l`
used in interpretation. They are not spare labels copied into an output.
The first comma boundary is

```
B_G = Comma J_G J_G.
```

An object consists of `m,n` and an actual morphism `c : p_m ⟶ p_n` in `K_G`.
Since `K_G` is a hom-category, that morphism is a **2-cell in `TwoFamily.Total
F_G`**. Its interpretation and boundary are established by the encode/decode
roundtrip above. This is the explicit dimension shift. The correspondence
objects are ordinary groupoids built from hom-categories, not a claimed
bicategory of all correspondences between total 2-groupoids.

Write `!` for the indicated terminal functor and define the actual iterated
comma categories

```
Tail_G = Comma (! : D_G → P) (! : D_(G×G) → P)
L_G    = Comma (! : B_G → P) (! : D_(G×G) → P)
R_G    = Comma (J_G : D_G → K_G) (Comma.fst … … ⋙ J_G).
```

Both full object presentations retain `(m,n,c,k,l)`, including the actual cell
`c`. `L_G` stores it in `object.left.hom`; `R_G` stores it in `object.hom`.
Both are discrete categories by the existing `commaIsDiscrete` helper, because
their apex categories are discrete. That does **not** assert `K_G` is discrete.

Define an equivalence `A_G : L_G ≌ R_G` by moving these existing entries between
the two comma presentations. Use complete normal forms

```
Σ m n : G, (p_m ⟶ p_n) × (G × G)
```

before any optional simplification to `G⁴`. Prove both object roundtrips and the
projections of `m,n,c,k,l`. The cell projection equality is required, with its
actual typed endpoints. Merely projecting `α : G` and forgetting the recovered
fiber boundary does not meet this contract. Since the comma categories are
discrete, `discreteEquivalence` lifts this object equivalence to the categorical
equivalence, including its arrow maps and natural unit/counit.

## Interpretation and both threefold boundaries

For the full retained data `(m,n,c,k,l)`, define two interpreted cells:

```
uL = (p_m ≫ p_k) ≫ p_l          vL = (p_n ≫ p_k) ≫ p_l
uR = p_m ≫ (p_k ≫ p_l)          vR = p_n ≫ (p_k ≫ p_l)

HL = (c ▷ p_k) ▷ p_l : uL ⇒ vL
HR = c ▷ (p_k ≫ p_l) : uR ⇒ vR.
```

`I_L` reads the actual boundary from `L_G` and constructs `HL` with the actual
`TwoFamily.whiskerRight`. `I_R` reads the actual boundary from `R_G` and constructs
`HR` with `TwoFamily.compose` followed by that same whiskering operation.
The first route composes the dependent action with the two later arrows in
sequence; the second composes those later arrows first. Both source and target
arrows are retained. Interpretations can return the full cell packet
`Σ u v : K_G, u ⟶ v`; category-valued packaging can use its discrete category
because the source comma categories are discrete. No truncation of the packet
is part of the map.

Let `am : uL = uR` and `an : vL = vR` be the actual total-category associativity
proofs. The exact comparison is the equality of total 2-cells

```
HL ≫ eqToHom an = eqToHom am ≫ HR : uL ⇒ vR.
```

Equivalently,

```
HR = eqToHom am.symm ≫ HL ≫ eqToHom an.
```

The latter is exactly `TwoFamily.whisker_right_compose F_G c p_k p_l am an`.
Use `A_G`'s full cell projection law to identify the `c` read by both routes
before applying it. This proves a comparison of the interpreted comma routes,
not merely a disconnected comparison of a separately invented cell.
The equality lives in the host type of total 2-cells with aligned boundaries;
no new 3-cell object or third identity level is being claimed.

For the finite selected input take

```
m=1, n=0, c=(α=1), k=1, l=1   in C₂.
```

Both right factors are nonidentity total arrows. After the first whisker the
cell has boundaries `0 ⇒ 1`; after both, it has boundaries `1 ⇒ 0`. Its base
projection stays 1 throughout. The full comparison above carries that cell,
including its dependent fiber equality. Also require `k=1,l=0` as a control:
the final boundary is `0 ⇒ 1`. Otherwise cancellation in the first selected
example could conceal an implementation that ignores both later arrows.

## Representation change and the two routes through the diagram

Use the actual `e = SecondIdentity.encode : Bit ≃* Label`. Construct the
hom-category equivalence `Q_e : K_Bit ≌ K_Label` by applying `e` to total-arrow
coordinates and to the cell's base coordinate. Its fiber component is obtained
by mapping the actual boundary equation with `e`; its inverse uses `e.symm`.
Prove identity/composition laws and exact roundtrips using the full cell decoder.
Also prove preservation of total-arrow composition and right whiskering with
explicit endpoint conversions. These are derived from `e.map_mul`, the cell
boundary and actual `TwoFamily` operations, not new coherence hypotheses.

Apply `Comma.post` to `Q_e` and align the apex functors with the coordinate
functors `D_Bit → D_Label`. Map the last apex by `e × e`. This yields separately
defined `C_L : L_Bit ≌ L_Label` and `C_R : R_Bit ≌ R_Label`. Their entries are

```
(m,n,c,k,l) ↦ (e m,e n,Q_e.map c,e k,e l).
```

The two representation/reassociation routes are

```
L_Bit --C_L--> L_Label --A_Label--> R_Label
L_Bit --A_Bit--> R_Bit --C_R--> R_Label.
```

Prove their equality on the whole comma object and a natural isomorphism on
functors, preserving all five entries. Unlike #694's chosen-conjugate
`changeRight`, the finite `C_R` can be defined directly by its actual comma
components. Its agreement is then a derived comparison of those definitions;
using conjugation is also valid but must be described as the weaker selection
contract it is.

After applying `I_R`, both paths return the same complete interpreted cell
packet. Also compare `Q_e` applied to `I_L` with `I_L` after `C_L`, and similarly
on the right, using the checked preservation equations for composition and
whiskering. The represented associativity square is the same square with
`em,en,ek,el` and `Q_e.map c`; its nonzero projection is `oneCell` and its
independent `labelObservation` is 1. The inverse representation must recover
the complete selected input cell and all four arrow coordinates.

## Loss controls and the limits of the thin example

The direct cell-erasure control fixes all arrow boundaries and replaces the
selected cell's base coordinate by identity. The required fiber boundary is
false, before and after either interpretation and representation route. This
is a typed rejection, not a comparison of two well-typed parallel cells.

The strict object-pullback replacement for `Comma J_G J_G` retains only pairs
with `p_m = p_n`. The selected nonzero input has `p_1 ≠ p_0`, detected by the
fiber-arrow coordinate, so it cannot enter that pullback. A boundary-preserving
map from the actual comma object to that strict pullback is therefore impossible
on the selected input. An erasure that also changes the boundaries may be
typeable, but then loses the chosen source/target observations.

The distinction is relative to those chosen boundaries. Each `Cell_G(m,n)`
is a singleton, because its label is forced to `n⁻¹*m`, and `K_G` is a connected
thin groupoid. It is equivalent to the terminal groupoid. Consequently this
experiment is **not** an equivalence-invariant higher obstruction. Exact
boundary-preserving recovery distinguishes it from that terminal presentation.
Nor can this example prove two different parallel cells survive: there are no
such cells in this specialization. Preserve the existing independent
`SecondIdentity.no_groupoid_observation` and `fiber_one_ne_zero` results, but
do not count them as extra conclusions of this connected finite experiment.

## Ordinary specialization and derived laws

For a discrete ambient category `Discrete X`, the same comma construction
specializes to matching endpoints and the actual chosen pullback through
`GroupoidCorrespondence.discretePullback`. Retain the existing
`discretePullback_encode` connection to `IndexedSumBaseChange.encode`, and the
checked ordinary selected inputs in `Examples.GroupoidCorrespondence`.
This is a specialization of the comma boundary construction, not a claim that
setting `G` to the trivial group recovers all ordinary categories.

[SpanAction](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/SquareKit/SpanAction.lean)
requires only pullbacks and includes arbitrary apex maps. Its slice action and
selected compositor retain full payloads and apex witnesses.
[SpanInterpretation](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/SquareKit/SpanInterpretation.lean)
requires pullback preservation, not finite-limit preservation, and its
[composition implementation](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/SquareKit/SpanInterpretationComposition.lean)
already supplies the ordinary interpretation-variable coherence completed in
#633. Keep the noninjective `Examples.SpanAction.collapse` and the slice-forgetting
interpretation examples unchanged. The selected groupoid experiment adds no
invertibility condition to them.

Inputs to the proposed construction are a commutative group, its finite
specializations, and a group equivalence for representation change. Family
functoriality, cell composition, total whiskering, associativity comparison,
comma reassociation and representation compatibility are derived. The fiber
in this example is deliberately locally discrete and the resulting hom-category
thin. There is no global assumption that all 2-cells in the existing library
are proof irrelevant, nor any truncation theorem for arbitrary `TwoFamily`s.

## Smallest implementation plan and decision test

1. Add the finite/group-valued path-family construction and exact total-cell
   encoder/decoder. Prove the forced boundary and both roundtrips. Recover the
   existing integer formulas as a specialization if generalized library code
   is chosen; alternatively retain the integer implementation and add the
   finite checked specialization without changing its assumptions.
2. Define `J_G`, `B_G`, `Tail_G`, `L_G`, `R_G` as actual functors/comma categories.
   Construct `A_G` from the complete cell normal form and prove every projection
   and inverse law. Do not assume an opaque reassociation field.
3. Define `I_L/I_R` with the actual composed total-arrow endpoints and actual
   whiskered cells. Prove their comparison by the existing
   `whisker_right_compose` and the retained comma-cell projection.
4. Define `Q_e`, both representation maps, and the full representation square.
   Prove the interpretation and boundary comparisons, including inverse recovery.
5. Check both finite tail inputs above, the nonzero observations, the zero-cell
   rejection, the strict-pullback rejection, and the unchanged ordinary clients.
   Run the usual focused/integrated proof validation for the implementation.

The discriminator for readiness is a checked term that reads the selected
actual comma boundary, returns the corresponding actual `TwoFamily.Total`
2-cell after both nonidentity right-whiskers, and proves the displayed
associativity square with its source and target transports. It must report 1
in both representations and reject zero with the same boundaries. Replacing
this with equality of a copied label, or with a separately constructed
`SecondIdentity` loop, fails the discriminator.

A generic two-correspondence core would add choices of weak pullback/comma
objects for 2-categories, maps on their cells, their interpretation, and
coherence among those choices. Neither the selected #694 chain nor
`sigmaRegroup` currently supplies all that data. The finite construction above
needs no such new axioms and produces a meaningful ready child under #555.
If a future task requires independently variable nonzero fiber `ρ` at fixed
boundaries, choose that stronger fixture explicitly and use the existing
`fiberLoop`/sigma machinery; do not present this thin fixture as having proved it.

## Validation record

The isolated probe is `/tmp/conaled-698-evidence/foundations-probe/FinitePath.lean`;
its final log is `FinitePath.log`. The invocation used the repository dev shell,
`flock /tmp/conaled-native-followups-lake.lock`, and `timeout 30 lake env lean`
on the external file. Final exit status was 0, with no local resource override.
It establishes only the family/cell/whiskering/rejection claims listed above.
Three preceding sources and logs are retained as `FinitePath-attempt{1,2,3}`.
Their failures were unit-composition simplification/elaboration issues in the
strict-transformation whiskering proof; explicit `Category.id_comp` and
`Category.comp_id` resolved them without changing the statement. They are not
mathematical obstructions. No repository source or tracker was changed, and no
full build was run for this design assessment.

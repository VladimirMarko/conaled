# #698 alternatives assessment

Recommend a direct finite experiment built through `TwoFamily` and actual ordinary comma categories of one of its hom-groupoids. Do not start a general higher comma or correspondence interface. Make the dimensional connection a proved part of the experiment: an arrow of this particular hom-groupoid is an actual dependent 2-cell of the total `TwoFamily`, and both correspondence routes must decode back to that complete cell. A comma arrow without this bridge would repeat #694 at a renamed level.

For the strongest finite discriminator, I recommend the small construction below with a mod-four fiber witness and mod-two dependent action. It distinguishes two parallel dependent cells after retaining their base action and endpoints. A smaller mod-two specialization of the existing path family is also feasible on paper, but its correct rejection is an ill-typed zero replacement, not an impossibility of reconstructing a cell from its retained endpoints. That difference should be explicit in the selected child.

This assessment is independent of the other #698 lenses. I coordinated #694's acceptance review and read its Standards/Spec reports; I did not author #694. That exposure informed my knowledge of its selected construction. I have not read the #698 foundations/use reports or exchanged conclusions with those assessors. The host could not allocate the requested fresh thread; this reused coordinator thread supplies one alternatives assessment, not an additional acceptance axis. Root relayed a search observation about higher comma module names after my source audit; no inference below depends on absence of a filename.

## Pinned evidence and existing capability

All code references are to `040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e`.

- [TwoFamily](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/SquareKit/Internal/PathTransport/TwoFamily.lean#L16) takes a strict pseudofunctor into `StrictTwoCategory`. Its total hom category retains `(α,ρ)`, with `ρ : u ⇒ F(α)(a) ≫ v`. `compose`, `whiskerLeft` and `whiskerRight` act on the actual dependent fields. [TwoFamilyCoherence](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/SquareKit/Internal/PathTransport/TwoFamilyCoherence.lean) supplies the total strict bicategory; [TwoFamilyHigher](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/SquareKit/Internal/PathTransport/TwoFamilyHigher.lean) supplies projection and local groupoid closure. These constructions already handle the dimension needed here.
- [TwoGroupoidHom.cell](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/SquareKit/Internal/PathTransport/TwoGroupoidHom.lean#L62) requires an actual fiber 2-cell, not equality of the base labels. Its inverse construction and groupoid instance retain both fields. [Examples.TwoGroupoidHom](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/Examples/TwoGroupoidHom.lean#L22) separately witnesses nonzero fiber loops and exact encoding/decoding of the original dependent path cell.
- [Examples.TwoFamily.pathFamily](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/Examples/TwoFamily.lean#L15) shows that base 2-cell action need not be erased. Its cell with source arrow 1 and target arrow 0 has base component 1; the existing right/left whiskering clients retain it.
- [sigmaRegroup/sigmaUngroup](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/SquareKit/Internal/PathTransport/TwoFamilySigmaRegroupHigher.lean#L19) are already strict pseudofunctors with inverse laws on complete data. [The checked regroup client](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/Examples/TwoFamilySigmaRegroup.lean#L44) retains a selected second fiber cell and checks horizontal/vertical compatibility. This is strong evidence against proposing a new generic reassociation core before trying the finite specialization. It does not by itself identify a sigma regrouping with a comma-composition reassociation; that comparison still needs its own types and maps.
- [GroupoidCorrespondence](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/SquareKit/GroupoidCorrespondence.lean) supplies actual comma/product/unit constructions and selected whole-object recovery. `commaIsDiscrete` and `discreteEquivalence` work beyond a one-object target. Its concrete `Boundary/Left/Right` interfaces specialize the target to `SingleObj G`. Reusing their pattern for a chosen object in a different groupoid is a bounded addition, not a new higher foundation.
- [SecondIdentity.encode](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/Examples/SecondIdentity.lean#L46) gives the independently checked Boolean/mod-two representation equivalence. Its loss theorem concerns parallel 2-cells in a locally discrete target. Do not transfer that theorem to a thin path-family example without checking its endpoints and observations.

## The smallest existing-path alternative and its limit

Replacing the integer abelian group in the existing path family by `ZMod 2` gives the following proposed finite specialization. Its total 1-arrows are `m : ZMod 2`; cells `m ⇒ n` retain `α : ZMod 2` with equation `m = n + α`. The selected `1 ⇒ 0` cell has `α = 1`. Erasing α to zero at those same endpoints makes the boundary false. Whiskering with arrow 1 changes the endpoints to `0 ⇒ 1` and retains α=1, so the action is not a disconnected tag.

However, for every fixed m,n the boundary forces `α = m-n`. The existing integer [Cell.base_eq and subsingleton instance](https://github.com/VladimirMarko/conaled/blob/040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e/SquareKit/Internal/PathTransport/TwoGroupoidPath.lean#L57) already expose this fact. There is a reconstruction from endpoints. A proposed universal no-reconstruction theorem after forgetting α but keeping m,n would therefore be false. This is an established mathematical limitation of that control, not a missing Lean feature.

This small experiment meets a literal nonzero-dependent-action target if its loss claim is limited to ill-typed zero replacement. It does not demonstrate loss of independently chosen parallel fiber witnesses. Appending an unrelated `fiberLoop 1` product label would not repair the connection unless the proposed maps and dependent boundary use that field. I recommend the next finite construction when the child is meant to retain both nonzero action and genuine parallel witness information.

## A finite dependent model with a separating fiber witness

The following are proposed definitions and paper calculations, not executed Lean declarations.

Write `Q = ZMod 2`, `R = ZMod 4`, and `π : R →+ Q` for reduction modulo two. Define a strict 2-category K with one object, 1-arrows `m : Q`, and 2-cells

```text
FiberCell(m,n) = { r : R // m = n + π(r) }.
```

Vertical and horizontal composition add the R labels; 1-arrow composition adds Q labels. Identities have label 0 and inverses negate labels. The boundary equations compose because π is additive. Associativity follows from addition, and interchange follows from commutativity of R. These facts must be proved as the actual `Bicategory.Strict` and invertibility instances, not supplied as arbitrary final laws. This is a finite concrete instance; there is no need to introduce a generic crossed-module framework for it.

Over the existing base `B²Q`, define a `TwoFamily.Family` with fiber K, identity transport on the sole base 1-arrow, and action of a base 2-cell α by the strict transformation of identity whose component is the fiber 1-arrow α. Its naturality uses commutativity of Q, and its 2-cell naturality preserves the R label. This gives a total dependent cell

```text
D(m,n) = { (α : Q, r : R) // m = n + α + π(r) }.
```

This equation is the required connection. With m=n=0, both `d₁=(1,1)` and `d₃=(1,3)` are well typed, since `1+π(1)=1+π(3)=0` in Q. They have the same source, target and nonzero base action but different fiber witnesses. The independent observation `r.val : Nat` yields 1 and 3. Removing r while retaining (m,n,α) cannot reconstruct both observations. Replacing r by 0 at the selected α=1 is not well typed. Thus one finite model supplies both a typing rejection and a genuine information-loss theorem without a disconnected product tag.

The primitive new work is this finite K and its family action. `TwoFamily` then supplies total composition/whiskering/coherence and the hom-groupoid H at the sole total object. An H-object is a total 1-arrow m; an H-arrow is the complete dependent total 2-cell D(m,n). Prove the exact encode/decode and both roundtrips to the `TwoFamily.Hom` representation, including the dependent fiber field. That connection is the admission test for using ordinary comma categories below.

## Actual correspondence chain and both routes

Let `P` be the existing terminal discrete groupoid, `H` the total hom-groupoid above, `p₀ : P ⥤ H` select the total arrow 0, and `B = Discrete Bool`. Use precisely these spans:

```text
S₁ : P ← P → H       right leg p₀
S₂ : H ← P → P       left leg p₀
S₃ : P ← B → P       terminal legs
```

Define `C = Comma p₀ p₀`, `T = Comma (terminal P) (terminal B)`,

```text
L = Comma (terminal C) (terminal B),
R = Comma p₀ (Comma.fst (terminal P) (terminal B) ⋙ p₀).
```

Both are actual iterated comma presentations, not a new tuple pretending to be composition. Their complete normal form is `D(0,0) × Bool`; all remaining data are terminal. Use #694's discrete-comma equivalence construction to derive the categorical equivalences and reassociation A. The selected inputs `(d₁,false)` and `(d₃,false)` must remain distinct in L, R and the decoded total hom. The entire D-record, not just r's observation, is the recovery target.

The dimensional shift is explicit: the comma boundary is a 1-arrow of H, which is definitionally or via the proved bridge a 2-cell of the total family. A comma morphism is not being called a total 2-cell. No total 3-cell or dependent higher transformation is thereby constructed.

For representation change, build the same finite model using `Bit` for the Q coordinates and the same R fiber-label type. Define its boundary by applying the existing `SecondIdentity.encode` to m,n,α before the Q equation. The representation maps m,n,α with encode and leaves r unchanged. Prove the family-action compatibility and induced functor on H, including complete-cell recovery. The two routes are then

```text
LBit --changeL--> LLabel --ALabel--> RLabel
LBit --ABit-----> RBit   --changeR--> RLabel.
```

Define changeL/changeR by actual comma postcomposition and endpoint alignment, or explicitly choose the right map by conjugation and retain that weaker comparison boundary as #694 does. If chosen by conjugation, do not claim independent interpretations agree. In either case, both routes send `(d₁,b)` to `(encode α=1, r=1, b)` and similarly preserve r=3. Require whole-record equality after displayed endpoint identifications, plus the categorical natural comparison. Comparing only final singleton endpoints would miss every required observation.

An additional connected check should first horizontally whisker a selected total cell by a nonidentity total arrow using `TwoFamily.whiskerLeft/Right`, then pass the resulting cell through the corresponding point-selection chain. This checks the family action, not merely storage in a hom-set. For d₁ and a shift by 1, both endpoints move from 0 to 1 while α=1 and r=1 remain. The exact equalities and representation compatibility are proposed obligations.

## Reuse, alternatives and declaration plan

| Choice | Retained content | New work and limitation |
|---|---|---|
| Finite path-family control | Nonzero dependent base action with forced boundary | Smallest specialization; zero replacement is rejected, but endpoints reconstruct the cell. |
| Recommended finite K/TwoFamily/hom-comma construction | Nonzero action and distinct parallel fiber witnesses, whole comma observations | Concrete finite K/family admission and dimensional bridge; no general higher-comma universal property. |
| General higher comma or correspondence core | Potentially arbitrary 2-dimensional apex/leg data | Requires more cell levels and general coherence than this selected experiment; not justified by a missing module name or this client alone. |
| Existing sigma regrouping | Complete nested dependent cell data and actual inverse strict functors | Reuse where the selected construction is expressed as a family tower; do not identify its regrouping with the comma routes without an explicit comparison. |

A ready child can order its declarations as: `fiberCell` and finite K; `finiteFamily`; `dependentCellEquiv` into the total hom; `selectedOne/selectedThree`; `homRepresentation` with inverse laws; the two comma presentations and `reassociate`; representation/reassociation square; actual whiskering control; erasure theorems; ordinary specialization. Freeze the independently expected equations and observations above before filling proofs. If the K/family admission does not elaborate, retain the exact failed judgment and limit the prerequisite to that admission with d₁/d₃ and the two boundary equations as its discriminator. Do not replace it with a request for an unspecified consumer.

For the ordinary specialization, retain #694's `discretePullback` and `discretePullback_encode`, with its existing SpanAction native selected recovery and SpanInterpretation consumer under their original assumptions. This route does not need the finite K or invertible apex maps. No `IsGroupoid` requirement should be added to the ordinary noninvertible-apex interface. The finite higher branch is a specialization alongside it, not a replacement for #633's completed ordinary coherence.

## Supplied laws, checks and remaining evidence

Supply the finite additive groups, π and the existing Boolean/mod-two equivalence. Derive the concrete K/family laws, dependent cell equations, inverses, functoriality, whole-record recovery and selected comma comparisons. Do not add fields containing the desired reassociation or erasure result. At the declared truncation level the finite model is a strict 2-category with set-valued 2-cell carriers and equality of 2-cells as propositions; its parallel 2-cells themselves are not truncated. Hom categories retain those cells as arrows.

I inspected pinned source and calculated the finite boundaries and two routes on paper. I ran no Lean probe or integrated build and make no measured author-effort or execution claim. Existing checked source establishes the reusable infrastructure, not the new K admission or its comma bridge. The finite construction is an implementable declaration plan with exact tests; its Lean feasibility still requires the stated implementation. No external theorem is needed for the new finite calculations, so I have not used an unverified literature assertion to stand in for them. No other assessment draft was read before saving this initial report.

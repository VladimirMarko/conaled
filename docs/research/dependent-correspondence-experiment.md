# Connected dependent-cell correspondence experiment

[#698](https://github.com/VladimirMarko/conaled/issues/698) selects a finite
implementation contract under [#555](https://github.com/VladimirMarko/conaled/issues/555):
a mod-two base action with a mod-four dependent fiber witness, admitted through
`TwoFamily`, then carried by actual comma composition and interpreted by actual
whiskering. Two parallel cells have the same endpoints and base action but
observations 1 and 3. The contract retains both witnesses through representation
change and threefold reassociation.

This is a paper construction and declaration plan. The stronger finite fiber,
its admission and its correspondence client are **not yet Lean implementations**.
A smaller path-family admission has been checked, and finite tables check the
proposed arithmetic. Neither check establishes the unimplemented contracts.
The selected implementation child belongs under #555; its tracker link is
recorded in #698's closeout and #555's task list. It is not added to the current
execution queue.

## Source audit and independent assessments

The source revision is `040f28a9dbcbb0e9059eddbd4819419fc5c0ff1e`, with Lean 4.35.0
and the pinned Mathlib. The [shared brief](dependent-correspondence-experiment/brief.md)
and initial [foundations](dependent-correspondence-experiment/foundations.md),
[use](dependent-correspondence-experiment/use.md), and
[alternatives](dependent-correspondence-experiment/alternatives.md) assessments
are preserved. Host thread limits required three reused agents; their prior
exposure is disclosed. They inspected sources independently before sharing
reports. The [foundations follow-up](dependent-correspondence-experiment/foundations-followup.md)
and [use follow-up](dependent-correspondence-experiment/use-followup.md) assess
the stronger finite alternative after that disclosure. These design assessments
do not replace independent Standards/Spec acceptance review.

The relevant delivered contracts are:

- [TwoFamily](../../SquareKit/Internal/PathTransport/TwoFamily.lean) defines
  strict higher families and total arrows/cells. `TwoGroupoidHom.cell α ρ`
  requires the actual dependent fiber cell `ρ : u ⇒ F(α)(a) ≫ v`.
- [TwoFamilyCoherence](../../SquareKit/Internal/PathTransport/TwoFamilyCoherence.lean)
  derives the total strict bicategory, including whiskering and its composition
  comparison. [TwoFamilyHigher](../../SquareKit/Internal/PathTransport/TwoFamilyHigher.lean)
  supplies projection and local groupoid closure.
- [TwoGroupoidHom](../../SquareKit/Internal/PathTransport/TwoGroupoidHom.lean)
  retains both components and derives vertical inverses. Its
  [applications](../../Examples/TwoGroupoidHom.lean) separately check independent
  fiber loops and exact decoding of the integer path boundary.
- [Sigma regrouping](../../SquareKit/Internal/PathTransport/TwoFamilySigmaRegroupHigher.lean)
  is already an invertible strict higher construction retaining genuine cells.
  It is not automatically the associator of comma correspondence composition;
  that identification would require its own comparison. The use assessment's
  `TwoFamilySigmaRegroupCell_fiber_heq` spelling denotes the existing theorem
  `TwoFamily.sigmaRegroupCell_fiber_heq` in `TwoFamilySigmaRegroupCells.lean`.
- [#694's selected comma construction](groupoid-correspondence-boundaries.md)
  supplies `commaIsDiscrete`, `discreteEquivalence`, actual chosen-pullback
  recovery and a group-valued selected chain. Its `Left G` and `Right G` are
  specialized to `SingleObj G`; their concrete types are not the new client.
  The helpers and Mathlib comma operations are reusable.
- [SecondIdentity](../../Examples/SecondIdentity.lean) supplies the Boolean/mod-two
  group equivalence and independent observations. Its locally discrete loss
  theorem must not be applied to a thin dependent example with different
  endpoints as though it supplied parallel witnesses.

No audit found a need to replace the total higher-family core. The missing work
is a concrete finite fiber, its family action and the explicitly selected
correspondence/interpretation maps below.

## Why select the stronger finite example

The smaller checked probe uses a family over `B²(C₂)` with fiber `BC₂` viewed
locally discretely. Its total cells have equation `m = n + α`. It admits a
nonzero cell `1 ⇒ 0`, and replacing α by zero at those fixed endpoints is
impossible. Its endpoints nevertheless determine α. Its hom-groupoid is thin
and contractible; no independent parallel witness is lost when α is reconstructed
from its endpoints. This is a useful admission control, not the strongest
witness-recovery test.

The selected alternative uses a fiber boundary that depends on the base action
and has two possible witnesses at the same endpoints. It adds one finite
strict 2-category, not a generic crossed-module library. The dependent boundary
uses the new witness, and the interpretation composes the resulting actual
cell. An unrelated product label or a separately evaluated `SecondIdentity`
loop cannot discharge the contract.

## Finite fiber and actual dependent cell

Use additive notation `Q = ZMod 2`, `R = ZMod 4`, and reduction `π : R →+ Q`.
Define a one-object strict 2-category `K` with 1-arrows `m : Q` and

```text
FiberCell(m,n) = { r : R // m = n + π(r) }.
```

Compose 1-arrows by addition in Q. Vertical and horizontal composition add
R labels; identity labels are zero and inverse labels negate. Additivity of π
proves the boundaries. Associativity follows from addition; commutativity of R
proves interchange. Associator and unitor labels are zero, with their actual
endpoint equations. Equality transports of arrows must be shown to have label
zero, so a hidden `eqToHom` cannot change an observation.

Over the existing `DoubleDelooping.Space (Multiplicative Q)`, construct
`F : TwoFamily.Family` with constant fiber K and identity action on the sole
base 1-arrow. A base 2-cell α acts by the strict transformation of identity
whose component is the fiber 1-arrow α. Its arrow naturality is commutativity
of Q. In `StrictTwoTransformation.Trans.naturality₂`, both whiskerings retain
r and the boundary transports have zero label; the two sides therefore have
the same R label. Prove this equation, together with the family identity,
vertical and horizontal laws, as actual interface fields. Do not substitute
an ordinary natural transformation that omits the 2-cell law.

Let x be the selected total object and `p_m : x ⟶ x` the total arrow with
fiber arrow m. The coordinate description of its actual total 2-cells is

```text
D(m,n) = { (α : Q, r : R) // m = n + α + π(r) }.
```

Construct an equivalence between D(m,n) and the morphism type
`p_m ⟶ p_n` in `TwoFamily.Hom F x x`, with both roundtrips retaining the
actual fiber witness. The equation follows from `TwoGroupoidHom.cell`'s
boundary, not from an extra observational axiom. Prove the coordinate formulas
for composition, inversion and whiskering through these public operations.
In coordinates vertical/horizontal composition add both labels; whiskering by
`p_k` shifts both endpoints by k and preserves α and r.

At m=n=0 select

```text
d₁ = (α=1, r=1),     d₃ = (α=1, r=3).
```

Both satisfy `0 = 0 + 1 + π(r)` and have nonzero base action. Their fiber
components are actual cells from 0 to 1 in K, with different R witnesses.
Observe r by its natural-number representative: 1 versus 3. Replacing r by 0
with those same endpoints and α=1 fails the boundary. Forgetting r while keeping
(m,n,α) identifies the two admitted cells, so no observation on that retained
data can reconstruct both values. This is a genuine parallel-witness loss
control, alongside the fixed-boundary typing rejection. Also require the
actual vertical composites `d₁ ≫ d₁ = (α=0,r=2) ≠ identity` and
`d₁ ≫ d₃ = identity`. The first has zero base action but a nonzero fiber
witness, exposing loss in a composite as well as in the supplied inputs.

All chosen object, arrow and cell carriers are finite in `Type 0`. The existing
classifier packaging and general `TwoFamily` universe parameters remain as
implemented; no assertion that the whole classifier is finite is needed.
Cells are set-valued mathematical data, with propositional equality between
them. The fiber is not locally discrete and parallel 2-cells are not truncated.

## Correspondences, interpretation and the exact threefold equation

Let `H = TwoFamily.Hom F x x`, whose arrows are the actual total 2-cells above.
Use its derived groupoid structure. Let `D_Q = Discrete Q`, `J : D_Q ⥤ H`
select `p_m`, and `P = GroupoidCorrespondence.Point`. Choose these three spans:

```text
S₁ : P ← D_Q → H           (terminal, J)
S₂ : H ← D_Q → P           (J, terminal)
S₃ : P ← Discrete(Q×Q) → P (terminal, terminal).
```

The final pair (k,l) supplies two actual arrows `p_k,p_l` to the interpretation.
Define the two bracketings using Mathlib's actual comma categories:

```text
B    = Comma J J
Tail = Comma (terminal D_Q) (terminal (Discrete(Q×Q)))
L    = Comma (terminal B) (terminal (Discrete(Q×Q)))
R    = Comma J (Comma.fst (terminal D_Q) (terminal (Discrete(Q×Q))) ⋙ J).
```

Their complete normal form is `(m,n,c : p_m ⟶ p_n,k,l)`. Both are discrete
because their apex categories are discrete; H itself is not assumed discrete.
Reuse #694's helpers to construct `A : L ≌ R`, retaining the entire actual c,
all four arrow coordinates, functor laws and both inverse laws.

The dimensional connection is explicit: the stored comma boundary is a
1-arrow of H, and the same term is a 2-cell of the independently constructed
total bicategory. Recovery must prove that connection on the actual types.
Neither the comma category nor its arrows are claimed to be a general higher
correspondence bicategory.

Read c from the respective comma presentation. Write `*` for actual total-arrow
composition and `▷` for actual `TwoFamily.whiskerRight`. Interpret the routes by

```text
I_L(c,k,l) = (c ▷ p_k) ▷ p_l : (p_m*p_k)*p_l ⇒ (p_n*p_k)*p_l
I_R(A(c,k,l)) = c ▷ (p_k*p_l) : p_m*(p_k*p_l) ⇒ p_n*(p_k*p_l).
```

Let `a_m` and `a_n` be the actual total-category associativity equalities at
those endpoints. The exact full-cell comparison is

```text
I_R(A(c,k,l)) = eqToHom(a_m.symm) ≫ I_L(c,k,l) ≫ eqToHom(a_n).
```

This is an application of existing `TwoFamily.whisker_right_compose` after
recovering the same actual c from the two comma objects. It is not a copied
coordinate equality or a caller-supplied associativity field. The interpretation
returns the complete endpoint/cell packet; functoriality on these discrete
comma categories follows by mapping their identity arrows. No third identity
level is claimed by the equality of these 2-cells.

Freeze d₁ and d₃ with k=l=1. The first whisker changes endpoints `0⇒0` to
`1⇒1`; the second returns to `0⇒0`. Both α=1 and r=1 or 3 survive. Also test
k=1,l=0, whose final endpoints remain `1⇒1`, so cancellation cannot conceal
ignoring the later arrows. Run both loss controls on the interpreted packets.

## Representation transport and recovery

Use `SecondIdentity.encode` for the Boolean/mod-two equivalence on Q; keep
R=`ZMod 4`. Here the additive Q coordinate is
`Multiplicative.toAdd (SecondIdentity.encode b)` for `b : Bit`. The Boolean fiber uses the same boundary written through encode.
Derive its operations and action using that group equivalence, including the
same zero-label transports. Construct the actual hom-category equivalence
`E : H_Bit ≌ H_Label` that maps the total-arrow and base-cell coordinates by
encode and retains r. Both full-cell roundtrips, including the fiber witness,
are required. Establish its compatibility with actual total composition and
whiskering, with endpoint conversions displayed. A direct equivalence of the
actual hom-groupoids with these laws suffices. `TwoFamily.StrongMap.toHigher`
works over a common base and does not by itself provide this cross-base map;
using it instead requires an explicit base map, reindexing and family comparison.

Define `M_L` and `M_R` independently on their actual comma components, using
Mathlib postcomposition/apex maps and the needed pointwise alignments. Their
full-coordinate action is

```text
(m,n,c,k,l) ↦ (encode m,encode n,E.map c,encode k,encode l).
```

Compare the functors `M_L ⋙ A_Label` and `A_Bit ⋙ M_R` by a natural isomorphism
with explicit object components. Prove whole-object recovery, not only the
observations 1 and 3. Unlike #694's documented chosen-conjugate right map,
this contract tests a directly defined right map. Also compare E applied to
each interpreted cell with interpretation after the corresponding M map.
Combine those laws with the displayed threefold equation. Both represented
routes retain r=1 or r=3, nonzero base observation 1 and the selected endpoints;
the inverse representation recovers the entire original packet.

## Ordinary specialization and implementation order

For arbitrary discrete cospans the comma layer recovers the actual chosen
Type pullback through `GroupoidCorrespondence.discretePullback`, with the
existing encoder equation `discretePullback_encode`. Retain its checked ordinary
compositor, native whole-selected-value recovery and slice interpretation
applications. This is a specialization of the comma construction, not a claim
that the finite group example covers arbitrary ordinary categories.
[SpanAction](../../SquareKit/SpanAction.lean) still requires pullbacks and admits
noninvertible apex maps. [SpanInterpretation](../../SquareKit/SpanInterpretation.lean)
still requires pullback preservation, not all finite limits. #633's completed
ordinary comparison/modification coherence remains complete. Keep the
noninjective apex, non-left-exact forgetting and failed truncation-preservation
controls under their original assumptions.

The ready child has these ordered acceptance obligations:

1. Construct the fixed finite K and F in the actual interfaces. Derive all
   category, strictness, invertibility, family and `naturality₂` laws from the
   finite group operations. Prove zero-label transports. Supply no final
   recovery or coherence theorem as an assumption.
2. Prove the actual D-to-total-cell equivalence, both roundtrips and operation
   formulas; admit d₁/d₃ and prove their distinction, typing rejection and
   parallel-witness no-reconstruction theorem, including the two selected vertical
   composites and their complete recovery.
3. Construct J, B, Tail, L, R and the actual categorical reassociation with
   whole-cell and arrow-coordinate recovery. Build both interpretations from
   recovered c and prove the exact threefold equation through the existing
   theorem, including both tail tests.
4. Construct both representations, the full hom equivalence, independent comma
   maps, natural comparison and interpretation square. Prove inverse recovery
   and both loss controls after transport and reassociation.
5. Retain the discrete chosen-pullback and ordinary/native clients with their
   original hypotheses. Put public checked applications in the normal build;
   run focused checks, integrated proof audit and independent Standards/Spec
   review. Preserve failed experiments and distinguish encoding/resource
   failures from mathematical obstructions.

Suggested declarations are `FiniteFiber`, `fiberCell`, `finiteFamily`,
`dependentCellEquiv`, `selectedOne`, `selectedThree`, `homRepresentation`,
`leftPresentation`, `rightPresentation`, `reassociate`, `interpretLeft`,
`interpretRight` and their recovery/comparison theorems. These names are a plan,
not an inventory of existing declarations. Keep the new fiber finite and local
unless a demonstrated second consumer warrants generalization.

The next decision is to implement this fixed child. No missing mathematical
choice or demonstrated prerequisite blocks its specification. If admission
fails, preserve the exact judgment, source and resource evidence; a scoped
prerequisite must target that judgment with d₁/d₃ as the discriminator. Do not
replace them by the thin probe to claim success. Generic higher comma universal
properties, unbounded coherence and motivic interpretations remain under #555
and its existing owners.

## Validation and limits

The retained [Lean probe](dependent-correspondence-experiment/finite-path.lean.txt)
and [log](dependent-correspondence-experiment/finite-path.log) check the smaller
commutative-group path family, actual Boolean cell, nonzero observation,
right-whiskering retention and zero-replacement rejection. Default Lean budgets
sufficed. Three earlier unit-composition elaboration attempts are retained in
the task evidence; explicit category unit equations fixed them without changing
the mathematical statement. They do not test the selected mod-four fiber.

The [finite table checker](dependent-correspondence-experiment/finite-tables.py.txt)
and [output](dependent-correspondence-experiment/finite-tables.log) enumerate eight
fiber cells and sixteen total cells. They check the proposed inverse, vertical,
horizontal and shift boundaries, additive associativity/interchange, the two
parallel witnesses, zero replacement and Boolean encoding. These Python checks
validate finite formulas only; they are not Lean proofs or interface admission.

Publication validation checks exact candidate documentation links/whitespace,
replays those retained probes against matching audited source inputs, and obtains
independent Standards/Spec review. No library theorem or axiom is added by this
report. The finite family's Lean admission, all new comparison maps and their
proofs remain the child's work; no general productivity or performance claim is
made.

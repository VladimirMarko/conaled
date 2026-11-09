import SquareKit.SmoothQuotientSource
import SquareKit.SmoothQuotientDeformationCocycle
import Examples.QuotientDescent

/-! Checked consumers of the retained source proof on smooth quotient
parameters. These examples do not stand in for generated-context descent. -/
noncomputable section
namespace Examples.SmoothSourceTransport
open CategoryTheory SquareKit SheafActionQuotient SmoothOpenSite
open SmoothQuotientDeformations SmoothQuarterTurnQuotient SmoothQuarterTurnArcs
open SmoothQuotientTransport Orbifolds.QuarterTurn

/-- A concise ordinary caller, retaining arbitrary quotient objects and arrows. -/
example {H : Type} [Group H] {M X : Sheaf topology Type}
    {a : Action (locallyConstantGroup H) M} {P Q R : Object a X}
    (p : P ⟶ Q) (q : Q ⟶ R) (h : Deformation P) :
    transport (p ≫ q) h = transport q (transport p h) := source_composition p q h

/-- This parameterized quotient object has no global chart lift. -/
example (c : C4) (hc : c ≠ 1) (m : SmoothClutching.base ⟶ SmoothClutching.base) :
    ¬ Nonempty (SheafActionQuotient.Arrow
      (chart (ActionQuotientEvidence.ineffective C4) m)
      (ActionQuotientEvidence.nontrivialObject C4 c)) :=
  not_chart_of_no_section (ActionQuotientEvidence.nontrivialObject C4 c)
    (SmoothClutching.no_global_section C4 c hc) m

/-- The same source theorem applies over that nontrivial torsor. -/
example (c : C4)
    (p q : ActionQuotientEvidence.nontrivialObject C4 c ⟶ ActionQuotientEvidence.nontrivialObject C4 c) :
    transport (p ≫ q) (constant (ActionQuotientEvidence.nontrivialObject C4 c)) =
      transport q (transport p (constant (ActionQuotientEvidence.nontrivialObject C4 c))) :=
  source_composition p q _

/-- Every boundary datum over the nontrivial torsor is recovered, not merely
its isomorphism class or a chosen global trivialization. -/
example (c : C4) (F : Fiber (ActionQuotientEvidence.nontrivialObject C4 c)) :
    (fromFiber F).fiber ≅ F := recovery F

example : Nat.card (SheafActionQuotient.Arrow
    (chart diskRepresentation.action (point coordinateOrigin))
    (chart diskRepresentation.action (point coordinateOrigin))) = 4 := origin_arrow_count

example (x : EuclideanOpen.Points diskDomain) (hx : (diskPoints x : ℂ) ≠ 0)
    (p : chart diskRepresentation.action (point x) ⟶ chart diskRepresentation.action (point x)) :
    p = 𝟙 _ := nonzero_arrow_identity x hx p

example (m : realBase ⟶ scalar) :
    ineffectiveActionArrow quarterTurn m ≠ ineffectiveActionArrow 1 m :=
  ineffective_forward_distinct m

example (m : realBase ⟶ scalar) (h : QuotientFixedArcs.Arcs (parameterZero realBase) m) :
    forwardArcTransport (ineffectiveActionArrow quarterTurn m ≫ ineffectiveActionArrow 1 m) h = h :=
  SmoothQuotientSource.ineffective_composition quarterTurn 1 m h

/-- Deformation descent works over arbitrary locally surjective parameters. -/
example {H : Type} [Group H] {M X Y : Sheaf topology Type}
    {a : Action (locallyConstantGroup H) M} (P : Object a X) (f : Y ⟶ X)
    [Presheaf.IsLocallySurjective topology f.hom] (d : DescentDatum P f) :
    restrict f d.descend = d.localDeformation := d.descend_restrict

/-- A torsor cocycle and a compatible local deformation suffice for recovery;
no global quotient object is supplied to this caller. -/
example {H : Type} [Group H] {M X : Sheaf topology Type}
    {a : Action (locallyConstantGroup H) M} {A : SplitSheaf.Ty X}
    [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]
    (d : CocycleDatum (a := a) A) :
    transport d.quotient.comparison (restrict (SplitSheaf.p A) d.descend) =
      d.localDeformation := d.recover

end Examples.SmoothSourceTransport

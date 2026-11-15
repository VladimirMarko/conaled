import Examples.CechDeformationDescent
import Examples.SmoothTorsors
import SquareKit.SheafActionQuotientDescentDisplay

/-! A selected ineffective C4 loop is a valid quotient arrow but cannot be
used unchanged as a Čech overlap on every pair of copies. -/
noncomputable section
namespace Examples.CechOverlapRejection
open CategoryTheory Opposite SquareKit SheafActionQuotient SmoothOpenSite
open Orbifolds.QuarterTurn

private def action : Action SmoothTorsors.group SmoothTorsors.point where
  act _ _ x := x
  one_act _ _ := rfl
  mul_act _ _ _ _ := rfl
  natural _ _ _ := rfl

private def object := chart action (𝟙 SmoothTorsors.point)
private def loop : object ⟶ object :=
  chartArrowOfRelation (a := action) (constantSection SmoothTorsors.point quarterTurn)
    (𝟙 _) (𝟙 _) rfl

private theorem loop_ne_id : loop ≠ 𝟙 object := by
  intro he
  have hv := congrArg (fun k : object ⟶ object => k.torsorArrow.iso.hom.app
    (SmoothTorsors.point.obj.elementsMk
      (SmoothGeometricKL.atStage (SmoothPresentationSite.free 0)) (𝟙 _))
      (1 : SmoothTorsors.group.obj.obj
        (SmoothGeometricKL.atStage (SmoothPresentationSite.free 0)))) he
  change (1 : SmoothTorsors.group.obj.obj
    (SmoothGeometricKL.atStage (SmoothPresentationSite.free 0))) *
      (show SmoothTorsors.group.obj.obj
        (SmoothGeometricKL.atStage (SmoothPresentationSite.free 0)) from
        (constantSection SmoothTorsors.point quarterTurn).hom.app _ (𝟙 _)) = 1 at hv
  rw [one_mul] at hv
  exact SmoothTorsors.quarterTurn_ne_one
    (constantLabel_injective C4 (SmoothPresentationSite.free 0) (𝟙 _)
      (hv.trans (((constantLabel C4).app _).hom.map_one.symm)))

/-- The actual C4 overlap fails the diagonal law although it preserves the
quotient object's value. Endpoint and value tests alone would accept it. -/
theorem quarterTurn_overlap_rejected :
    let A := SplitSheaf.ofDisplay (𝟙 SmoothTorsors.point)
    (loop.reindex (SplitSheaf.Cech.first A ≫ SplitSheaf.p A)).reindex
      (SplitSheaf.Cech.diagonal A) ≠ Arrow.ident (reindex object (SplitSheaf.p A)) :=
  by
    have : Presheaf.IsLocallySurjective topology (𝟙 SmoothTorsors.point : SmoothTorsors.point ⟶ SmoothTorsors.point).hom := by
      change Presheaf.IsLocallySurjective topology (𝟙 SmoothTorsors.point.obj)
      infer_instance
    have := Descent.splitCover_locallySurjective
      (f := (𝟙 SmoothTorsors.point : SmoothTorsors.point ⟶ SmoothTorsors.point))
    exact CechDeformationDescent.rejects_constant_loop object loop loop_ne_id

end Examples.CechOverlapRejection

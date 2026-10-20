import SquareKit.SmoothQuarterTurnArcs
import SquareKit.SmoothConstantAction
import SquareKit.SmoothConstantOrdinary

/-! Quotient chart arrows retain the disk stabilizers and ineffective labels. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory Opposite
open scoped Manifold
namespace SquareKit.SmoothQuarterTurnQuotient
open SmoothPresentationSite SmoothOpenSite EuclideanOpen SmoothQuarterTurnArcs
open Orbifolds.QuarterTurn SheafActionQuotient

def diskRepresentation : SmoothConstantAction.Representation C4 diskSheaf :=
  ⟨SmoothQuarterTurnArcs.diskAction, diskAction_one, diskAction_mul⟩

def ineffectiveRepresentation : SmoothConstantAction.Representation C4 scalar :=
  ⟨ineffectiveScalarAction, ineffectiveScalarAction_one, ineffectiveScalarAction_mul⟩

def realBase : Sheaf SmoothOpenSite.topology Type := SmoothOpenSite.topology.yoneda.obj (op (free 0))

def point (x : Points diskDomain) : realBase ⟶ diskSheaf :=
  SmoothOpenSite.topology.yoneda.map (ordinaryPoint diskDomain x)

def realLabelEquiv : (realBase ⟶ locallyConstantGroupSheaf C4) ≃ C4 :=
  SmoothOpenSite.topology.yonedaEquiv.trans (constantLabelRealEquiv C4).symm

@[simp] theorem realLabelEquiv_constant (g : C4) :
    realLabelEquiv (constantSection realBase g) = g :=
  (constantLabelRealEquiv C4).symm_apply_apply g

theorem realLabelEquiv_inverse (g : realBase ⟶ locallyConstantGroupSheaf C4) :
    constantSection realBase (realLabelEquiv g) = g := by
  apply realLabelEquiv.injective
  exact realLabelEquiv_constant _

theorem disk_constant_onMap (g : C4) (x : Points diskDomain) :
    diskRepresentation.action.onMap (constantSection realBase g) (point x) =
      point ((show Map diskDomain diskDomain from diskMap g).toFun x) := by
  have hc : diskRepresentation.action.onMap (constantSection realBase g) (point x) =
      point x ≫ SmoothQuarterTurnArcs.diskAction g := by
    ext U y
    exact diskRepresentation.act_constant U g ((point x).hom.app U y)
  rw [hc]
  apply SmoothOpenSite.topology.yonedaEquiv.injective
  change (embedding.map (diskMap g)).hom.app _ ((realSectionEquiv diskDomain).symm x) =
    (realSectionEquiv diskDomain).symm _
  apply (realSectionEquiv diskDomain).injective
  rw [Equiv.apply_symm_apply]
  exact (realSectionEquiv_naturality (diskMap g) _).trans
    (congrArg (fun y => (show Map diskDomain diskDomain from diskMap g).toFun y)
      ((realSectionEquiv diskDomain).apply_symm_apply x))

theorem point_injective : Function.Injective point := by
  intro x y h
  apply (realSectionEquiv diskDomain).symm.injective
  exact congrArg (fun k : realBase ⟶ diskSheaf => SmoothOpenSite.topology.yonedaEquiv k) h

/-- Actual quotient automorphisms, including all their labels, are exactly the
ordinary stabilizer at a real point. This uses the full torsor quotient's chart. -/
def diskArrowEquiv (x : Points diskDomain) :
    Arrow (chart diskRepresentation.action (point x)) (chart diskRepresentation.action (point x)) ≃
      {g : C4 // (show Map diskDomain diskDomain from diskMap g).toFun x = x} :=
  (chartArrowEquiv (point x) (point x)).trans {
    toFun g := ⟨realLabelEquiv g.val, by
      apply point_injective
      rw [← disk_constant_onMap, realLabelEquiv_inverse]
      exact g.property⟩
    invFun g := ⟨constantSection realBase g.val, by
      rw [disk_constant_onMap, g.property]⟩
    left_inv g := Subtype.ext (realLabelEquiv_inverse g.val)
    right_inv g := Subtype.ext (realLabelEquiv_constant g.val) }

def originArrowEquiv :
    Arrow (chart diskRepresentation.action (point coordinateOrigin))
      (chart diskRepresentation.action (point coordinateOrigin)) ≃ C4 :=
  (diskArrowEquiv coordinateOrigin).trans originLabelEquiv

theorem origin_arrow_count :
    Nat.card (Arrow (chart diskRepresentation.action (point coordinateOrigin))
      (chart diskRepresentation.action (point coordinateOrigin))) = 4 :=
  (Nat.card_congr originArrowEquiv).trans card_C4

theorem nonzero_arrow_identity (x : Points diskDomain) (hx : (diskPoints x : ℂ) ≠ 0)
    (f : Arrow (chart diskRepresentation.action (point x)) (chart diskRepresentation.action (point x))) :
    f = Arrow.ident _ := by
  apply (diskArrowEquiv x).injective
  apply Subtype.ext
  have hf := nonzero_label x hx (diskArrowEquiv x f).val (diskArrowEquiv x f).property
  have hi := nonzero_label x hx (diskArrowEquiv x (Arrow.ident _)).val (diskArrowEquiv x (Arrow.ident _)).property
  exact hf.trans hi.symm

/-- The retained origin-arrow label has the proved classical coefficient action.
The chart convention is m = g·n, so forward transport uses the inverse label. -/
theorem origin_arrow_label_derivative
    (f : Arrow (chart diskRepresentation.action (point coordinateOrigin))
      (chart diskRepresentation.action (point coordinateOrigin))) (v : Fin 2 → ℝ) :
    complexCoordinates (coefficientAction (originArrowEquiv f) v) =
      mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) (fun w : Disk => originArrowEquiv f • w) origin (complexCoordinates v) :=
  disk_coefficients_classical _ _ _

theorem ineffective_constant_onMap (g : C4) (m : realBase ⟶ scalar) :
    ineffectiveRepresentation.action.onMap (constantSection realBase g) m = m := by
  ext U y
  exact ineffectiveRepresentation.act_constant U g (m.hom.app U y)

def ineffectiveArrowEquiv (m : realBase ⟶ scalar) :
    Arrow (chart ineffectiveRepresentation.action m) (chart ineffectiveRepresentation.action m) ≃ C4 :=
  (chartArrowEquiv m m).trans {
    toFun g := realLabelEquiv g.val
    invFun g := ⟨constantSection realBase g, ineffective_constant_onMap g m⟩
    left_inv g := Subtype.ext (realLabelEquiv_inverse g.val)
    right_inv := realLabelEquiv_constant }

theorem ineffective_distinct_arrows (m : realBase ⟶ scalar) :
    (ineffectiveArrowEquiv m).symm quarterTurn ≠ (ineffectiveArrowEquiv m).symm 1 :=
  fun h => quarterTurn_ne_one ((ineffectiveArrowEquiv m).symm.injective h)

/-- The usual action arrow x→g·x uses inverse label under the chart convention. -/
def diskActionArrow (g : C4) (x : Points diskDomain) :
    Arrow (chart diskRepresentation.action (point x))
      (chart diskRepresentation.action (point ((show Map diskDomain diskDomain from diskMap g).toFun x))) :=
  chartArrowOfRelation (constantSection realBase g⁻¹) _ _ (by
    rw [disk_constant_onMap]
    congr 1
    change diskPoints.symm (g⁻¹ • diskPoints (diskPoints.symm (g • diskPoints x))) = x
    simp)

/-- At the origin these are automorphisms, indexed by the forward action. -/
def originActionArrow (g : C4) :
    Arrow (chart diskRepresentation.action (point coordinateOrigin))
      (chart diskRepresentation.action (point coordinateOrigin)) :=
  originArrowEquiv.symm g⁻¹

theorem originActionArrow_label (g : C4) :
    originArrowEquiv (originActionArrow g) = g⁻¹ := originArrowEquiv.apply_symm_apply _

theorem origin_forward_label_derivative (g : C4) (v : Fin 2 → ℝ) :
    complexCoordinates (coefficientAction (originArrowEquiv (originActionArrow g))⁻¹ v) =
      mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) (fun w : Disk => g • w) origin (complexCoordinates v) := by
  rw [originActionArrow_label, inv_inv]
  exact disk_coefficients_classical _ _ _

end SquareKit.SmoothQuarterTurnQuotient

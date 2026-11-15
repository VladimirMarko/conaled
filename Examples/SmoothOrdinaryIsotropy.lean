import SquareKit.SmoothOrdinaryQuotient
import SquareKit.SmoothManifoldFullFaithfulness

/-! C4, ineffective isotropy, and manifold comparison through the designated
ordinary-open arrow equivalence. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory Opposite
open scoped ContDiff Manifold
namespace Examples.SmoothOrdinaryIsotropy
open SquareKit SquareKit.SmoothAlgebra SquareKit.EuclideanOpen SquareKit.SmoothOpenSite
open SquareKit.SheafActionQuotient SquareKit.SmoothOrdinaryQuotient
open SquareKit.SmoothQuarterTurnArcs SquareKit.SmoothQuarterTurnQuotient Orbifolds.QuarterTurn

abbrev pointDomain := full 0

def solePoint : Points pointDomain := ⟨fun i => Fin.elim0 i, one_ne_zero⟩

instance : Subsingleton (Points pointDomain) := ⟨fun _x _y => Subtype.ext (funext (fun i => Fin.elim0 i))⟩

/-- Evaluation on the zero-dimensional ordinary domain retains every group element. -/
def pointLabelEquiv (G : Type) : LocallyConstant (Points pointDomain) G ≃ G where
  toFun l := l solePoint
  invFun g := LocallyConstant.const _ g
  left_inv l := DFunLike.ext _ _ (fun x => congrArg l (Subsingleton.elim solePoint x))
  right_inv _ := rfl

abbrev pointChart (x : Points diskDomain) :=
  chart diskRepresentation.action (embedding.map (constantMap pointDomain diskDomain x))

/-- The actual ordinary comparison reduces to the same stabilizer contract as
the existing real-stage comparison. -/
def ordinaryPointArrowEquiv (x : Points diskDomain) :
    Arrow (pointChart x) (pointChart x) ≃
      {g : C4 // (show Map _ _ from diskMap g) x = x} :=
  (diskChartArrowEquiv pointDomain (constantMap pointDomain diskDomain x)
    (constantMap pointDomain diskDomain x)).trans {
    toFun k := ⟨pointLabelEquiv C4 k.val, k.property solePoint⟩
    invFun g := ⟨(pointLabelEquiv C4).symm g.val, fun _ => g.property⟩
    left_inv k := Subtype.ext ((pointLabelEquiv C4).symm_apply_apply k.val)
    right_inv g := Subtype.ext ((pointLabelEquiv C4).apply_symm_apply g.val) }

/-- This chosen comparison identifies the same actual stabilizer label on both routes. -/
def pointArrowComparison (x : Points diskDomain) :
    Arrow (pointChart x) (pointChart x) ≃
      Arrow (chart diskRepresentation.action (point x)) (chart diskRepresentation.action (point x)) :=
  (ordinaryPointArrowEquiv x).trans (diskArrowEquiv x).symm

theorem pointArrowComparison_label (x : Points diskDomain) (f : Arrow (pointChart x) (pointChart x)) :
    (diskArrowEquiv x (pointArrowComparison x f)).val = ordinaryArrowLabel f solePoint :=
  congrArg Subtype.val ((diskArrowEquiv x).apply_symm_apply _)

theorem ordinary_origin_count : Nat.card (Arrow (pointChart coordinateOrigin) (pointChart coordinateOrigin)) = 4 :=
  (Nat.card_congr (pointArrowComparison coordinateOrigin)).trans origin_arrow_count

theorem ordinary_regular_identity (x : Points diskDomain) (hx : (diskPoints x : ℂ) ≠ 0)
    (f : Arrow (pointChart x) (pointChart x)) : f = Arrow.ident _ := by
  apply (ordinaryPointArrowEquiv x).injective
  apply Subtype.ext
  exact (nonzero_label x hx _ (ordinaryPointArrowEquiv x f).property).trans
    (ordinaryArrowLabel_ident diskRepresentation.action _ solePoint).symm

/-- The retained derivative convention uses the inverse of a forward action label. -/
theorem ordinary_origin_derivative (f : Arrow (pointChart coordinateOrigin) (pointChart coordinateOrigin))
    (v : Fin 2 → ℝ) :
    complexCoordinates (coefficientAction (ordinaryArrowLabel f solePoint) v) =
      mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) (fun w : Disk => ordinaryArrowLabel f solePoint • w) origin
        (complexCoordinates v) := by
  have h := origin_arrow_label_derivative (pointArrowComparison coordinateOrigin f) v
  have he : originArrowEquiv (pointArrowComparison coordinateOrigin f) = ordinaryArrowLabel f solePoint :=
    pointArrowComparison_label coordinateOrigin f
  rw [he] at h
  exact h

def ordinaryOriginForwardArrow (g : C4) : Arrow (pointChart coordinateOrigin) (pointChart coordinateOrigin) :=
  (pointArrowComparison coordinateOrigin).symm (originActionArrow g)

theorem ordinary_forward_label (g : C4) :
    ordinaryArrowLabel (ordinaryOriginForwardArrow g) solePoint = g⁻¹ := by
  have h := pointArrowComparison_label coordinateOrigin (ordinaryOriginForwardArrow g)
  change originArrowEquiv (pointArrowComparison coordinateOrigin (ordinaryOriginForwardArrow g)) = _ at h
  rw [ordinaryOriginForwardArrow, Equiv.apply_symm_apply, originActionArrow_label] at h
  exact h.symm

theorem ordinary_forward_derivative (g : C4) (v : Fin 2 → ℝ) :
    complexCoordinates (coefficientAction (ordinaryArrowLabel (ordinaryOriginForwardArrow g) solePoint)⁻¹ v) =
      mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) (fun w : Disk => g • w) origin (complexCoordinates v) := by
  rw [ordinary_forward_label, inv_inv]
  exact disk_coefficients_classical _ _ _

/-- Ineffective actions retain all locally constant labels over every ordinary open. -/
def ordinaryIneffectiveArrowEquiv (U : Domain) (m : embedding.obj U ⟶ scalar) :
    Arrow (chart ineffectiveRepresentation.action m) (chart ineffectiveRepresentation.action m) ≃
      LocallyConstant (Points U) C4 :=
  (chartArrowEquiv m m).trans {
    toFun g := ordinaryHomLabelEquiv C4 U g.val
    invFun k := ⟨(ordinaryHomLabelEquiv C4 U).symm k, by
      ext V x
      exact ineffectiveRepresentation.act_of_trivial (fun _ => rfl) V _ _⟩
    left_inv g := Subtype.ext ((ordinaryHomLabelEquiv C4 U).symm_apply_apply g.val)
    right_inv k := (ordinaryHomLabelEquiv C4 U).apply_symm_apply k }

theorem ordinary_ineffective_distinct (m : embedding.obj pointDomain ⟶ scalar) :
    (ordinaryIneffectiveArrowEquiv pointDomain m).symm (LocallyConstant.const _ quarterTurn) ≠
      (ordinaryIneffectiveArrowEquiv pointDomain m).symm (LocallyConstant.const _ 1) := by
  intro h
  have he := (ordinaryIneffectiveArrowEquiv pointDomain m).symm.injective h
  exact quarterTurn_ne_one (congrArg (fun k => k solePoint) he)

/-- Principal manifold interpretation returns the exact embedded arrow used by
the quotient comparison, through the named principal isomorphisms. -/
theorem manifold_arrow_recovers {U V : Domain} (f : U ⟶ V) :
    (ManifoldRealization.principalIso U).inv ≫
      ManifoldRealization.homEquiv (ManifoldRealization.openSmoothEquiv U V f) ≫
      (ManifoldRealization.principalIso V).hom = embedding.map f := by
  rw [ManifoldRealization.homEquiv_principal]
  change (ManifoldRealization.principalIso U).inv ≫
    ((ManifoldRealization.principalIso U).hom ≫ embedding.map f ≫
      (ManifoldRealization.principalIso V).inv) ≫ (ManifoldRealization.principalIso V).hom = _
  simp

end Examples.SmoothOrdinaryIsotropy

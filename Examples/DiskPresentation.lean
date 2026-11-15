import SquareKit.SmoothDiskPresentation
import Examples.SmoothOrdinaryComparison

/-! Controls for the external proper étale comparison: singular and regular
points, disconnected labels, canonical recovery, and retained ineffective data. -/
noncomputable section
open CategoryTheory
open scoped Manifold ContDiff
namespace Examples.DiskPresentation
open SquareKit SquareKit.EuclideanOpen SquareKit.SmoothOpenSite
open SquareKit.SmoothDiskPresentation SquareKit.SheafActionQuotient
open SquareKit.SmoothQuarterTurnArcs SquareKit.SmoothQuarterTurnQuotient
open Orbifolds.QuarterTurn SmoothOrdinaryIsotropy SmoothOrdinaryComparison


example : IsManifold Orbifolds.QuarterTurn.DiskPresentation.arrowModel ∞ Orbifolds.QuarterTurn.DiskPresentation.Arrow := inferInstance
example : T2Space Orbifolds.QuarterTurn.DiskPresentation.Arrow := inferInstance
example : SecondCountableTopology Orbifolds.QuarterTurn.DiskPresentation.Arrow := inferInstance
example : IsProperMap Orbifolds.QuarterTurn.DiskPresentation.anchor ∧ IsLocalDiffeomorph Orbifolds.QuarterTurn.DiskPresentation.arrowModel 𝓘(ℝ, ℂ) ∞ Orbifolds.QuarterTurn.DiskPresentation.source ∧
    IsLocalDiffeomorph Orbifolds.QuarterTurn.DiskPresentation.arrowModel 𝓘(ℝ, ℂ) ∞ Orbifolds.QuarterTurn.DiskPresentation.target := Orbifolds.QuarterTurn.DiskPresentation.proper_etale

/-- The chosen forward origin arrow maps to the same geometric label. -/
theorem origin_forward (g : C4) :
    (chartEquiv pointDomain (constantMap pointDomain diskDomain coordinateOrigin)
      (constantMap pointDomain diskDomain coordinateOrigin) (ordinaryOriginForwardArrow g)).arrow solePoint =
      (g, origin) := by
  change ((SmoothOrdinaryQuotient.ordinaryArrowLabel (ordinaryOriginForwardArrow g) solePoint)⁻¹,
    diskPoints coordinateOrigin) = _
  rw [ordinary_forward_label, inv_inv]
  exact Prod.ext rfl (diskPoints.apply_symm_apply origin)

theorem origin_four_families : Nat.card (Family pointDomain
    (constantMap pointDomain diskDomain coordinateOrigin)
    (constantMap pointDomain diskDomain coordinateOrigin)) = 4 :=
  (Nat.card_congr (chartEquiv _ _ _).symm).trans ordinary_origin_count

/-- Every regular-point family is the identity family, through the actual comparison. -/
theorem regular_family (x : Points diskDomain) (hx : (diskPoints x : ℂ) ≠ 0)
    (f : Family pointDomain (constantMap pointDomain diskDomain x) (constantMap pointDomain diskDomain x)) :
    f = Family.ident _ := by
  calc
    f = chartEquiv _ _ _ ((chartEquiv _ _ _).symm f) := ((chartEquiv _ _ _).apply_symm_apply f).symm
    _ = chartEquiv _ _ _ (Arrow.ident _) := congrArg (chartEquiv _ _ _)
      (ordinary_regular_identity x hx ((chartEquiv _ _ _).symm f))
    _ = Family.ident _ := chartEquiv_ident _ _

/-- The anchor keeps four origin arrows although their endpoints agree. -/
theorem anchor_not_injective : ¬ Function.Injective Orbifolds.QuarterTurn.DiskPresentation.anchor := by
  intro h
  have he : Orbifolds.QuarterTurn.DiskPresentation.anchor (quarterTurn, origin) = Orbifolds.QuarterTurn.DiskPresentation.anchor (1, origin) := by
    change (origin, quarterTurn • origin) = (origin, (1 : C4) • origin)
    refine Prod.ext rfl ?_
    apply Subtype.ext
    simp [origin]
  exact quarterTurn_ne_one (congrArg Prod.fst (h he))

/-- At a regular point, the quarter-turn is not an isotropy arrow. -/
theorem half_not_fixed : Orbifolds.QuarterTurn.DiskPresentation.target (quarterTurn, half) ≠ half := by
  intro h
  have hn : (half : ℂ) ≠ 0 := by norm_num [half]
  have hs : quarterTurn ∈ MulAction.stabilizer C4 half := h
  rw [nonzero_stabilizer half hn] at hs
  exact quarterTurn_ne_one hs

/-- Existing coefficient transport agrees with the derivative of this external rotation. -/
theorem forward_derivative (g : C4) (v : Fin 2 → ℝ) :
    complexCoordinates (coefficientAction
      ((chartEquiv pointDomain (constantMap pointDomain diskDomain coordinateOrigin)
        (constantMap pointDomain diskDomain coordinateOrigin) (ordinaryOriginForwardArrow g)).val solePoint) v) =
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Orbifolds.QuarterTurn.DiskPresentation.rotation g) origin (complexCoordinates v) :=
  ordinary_forward_derivative g v

/-- This is a smooth family with genuinely varying labels, not a constant-label replacement. -/
theorem disconnected_forward :
    (chartEquiv _ _ _ varyingOriginArrow).val negativePoint = 1 ∧
    (chartEquiv _ _ _ varyingOriginArrow).val positivePoint = quarterTurn⁻¹ := by
  change (SmoothOrdinaryQuotient.ordinaryArrowLabel varyingOriginArrow negativePoint)⁻¹ = 1 ∧ _
  rw [varyingOriginArrow_labels.1, inv_one]
  exact ⟨rfl, congrArg Inv.inv varyingOriginArrow_labels.2⟩

/-- The existing named refinement commutes with the external smooth-family comparison. -/
theorem sign_recovery (m n : SmoothClutching.punctured ⟶ diskDomain)
    (f : Descent.Map
      (Descent.canonicalDatum signFamily (chart diskRepresentation.action (embedding.map m)))
      (Descent.canonicalDatum signFamily (chart diskRepresentation.action (embedding.map n)))) :
    smoothChartEquiv _ m n (Descent.canonicalArrowEquiv refinedSignFamily _ _
      (Descent.recoveryArrowComparison signFamily refinedSignFamily _ _ f)) =
    smoothChartEquiv _ m n (Descent.canonicalArrowEquiv signFamily _ _ f) :=
  canonicalRecovery_comparison _ m n signFamily refinedSignFamily f

/-- Recovery of the actual varying origin arrow retains its smooth family. -/
theorem sign_varying_recovery :
    smoothChartEquiv _ _ _ (Descent.canonicalArrowEquiv refinedSignFamily _ _
      (Descent.recoveryArrowComparison signFamily refinedSignFamily _ _
        ((Descent.canonicalArrowEquiv signFamily _ _).symm varyingOriginArrow))) =
    smoothChartEquiv _ _ _ varyingOriginArrow := by
  rw [Descent.recoveryArrowComparison_commutes, Equiv.apply_symm_apply]

/-- Proper étale disk geometry does not collapse the retained ineffective labels. -/
theorem ineffective_control (m : embedding.obj pointDomain ⟶ scalar) :
    IsProperMap Orbifolds.QuarterTurn.DiskPresentation.anchor ∧
    (ordinaryIneffectiveArrowEquiv pointDomain m).symm (LocallyConstant.const _ quarterTurn) ≠
      (ordinaryIneffectiveArrowEquiv pointDomain m).symm (LocallyConstant.const _ 1) :=
  ⟨Orbifolds.QuarterTurn.DiskPresentation.anchor_proper, ordinary_ineffective_distinct m⟩

/-- A noncommutative control uses the same quotient label comparison on a trivial action. -/
def trivialRepresentation (G : Type) [Group G] : SmoothConstantAction.Representation G scalar :=
  ⟨fun _ => 𝟙 _, rfl, fun _ _ => (Category.id_comp _).symm⟩

def trivialLabelEquiv (G : Type) [Group G] (m : embedding.obj pointDomain ⟶ scalar) :
    Arrow (chart (trivialRepresentation G).action m) (chart (trivialRepresentation G).action m) ≃
      LocallyConstant (Points pointDomain) G :=
  (chartArrowEquiv m m).trans {
    toFun g := ordinaryHomLabelEquiv G pointDomain g.val
    invFun k := ⟨(ordinaryHomLabelEquiv G pointDomain).symm k, by
      ext V x
      exact (trivialRepresentation G).act_of_trivial (fun _ => rfl) V _ _⟩
    left_inv g := Subtype.ext ((ordinaryHomLabelEquiv G pointDomain).symm_apply_apply g.val)
    right_inv k := (ordinaryHomLabelEquiv G pointDomain).apply_symm_apply k }

def trivialForward {G : Type} [Group G] (m : embedding.obj pointDomain ⟶ scalar) (g : G) :=
  (trivialLabelEquiv G m).symm (LocallyConstant.const _ g⁻¹)

theorem trivialForward_label {G : Type} [Group G] (m : embedding.obj pointDomain ⟶ scalar) (g : G) :
    ForwardLabel.label (trivialForward m g) solePoint = g := by
  have h := (trivialLabelEquiv G m).apply_symm_apply (LocallyConstant.const _ g⁻¹)
  change SmoothOrdinaryQuotient.ordinaryArrowLabel (trivialForward m g) = _ at h
  change (SmoothOrdinaryQuotient.ordinaryArrowLabel (trivialForward m g) solePoint)⁻¹ = g
  rw [h]
  exact inv_inv g

/-- Following swap 0/1 by swap 1/2 sends 0 to 2; reversed composition sends it to 1. -/
theorem noncommutative_order (m : embedding.obj pointDomain ⟶ scalar) :
    let g : Equiv.Perm (Fin 3) := Equiv.swap 0 1
    let h : Equiv.Perm (Fin 3) := Equiv.swap 1 2
    ForwardLabel.label ((trivialForward m g).comp (trivialForward m h)) solePoint = h * g ∧
    ForwardLabel.label ((trivialForward m g).comp (trivialForward m h)) solePoint ≠ g * h := by
  dsimp only
  rw [ForwardLabel.comp, trivialForward_label, trivialForward_label]
  constructor
  · rfl
  · intro he
    have h0 := congrArg (fun p : Equiv.Perm (Fin 3) => p 0) he
    norm_num [Equiv.Perm.mul_apply, Equiv.swap_apply_def] at h0

end Examples.DiskPresentation

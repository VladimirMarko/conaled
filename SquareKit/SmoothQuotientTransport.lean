import SquareKit.QuotientFixedArcs
import SquareKit.SmoothTorsorParameters
import SquareKit.SmoothQuarterTurnQuotient

/-! Fixed infinitesimal quotient fibers over arbitrary sheaf parameters, and
forward transport compared with the disk coefficient action. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory Opposite
open scoped Manifold
namespace SquareKit.SmoothQuotientTransport
open SmoothOpenSite SheafActionQuotient SheafRelation
variable {H : Type} [Group H] {M : Sheaf SmoothOpenSite.topology Type}
variable (a : Action (locallyConstantGroup H) M) (X : Sheaf SmoothOpenSite.topology Type) (m : X ⟶ M)
local notation "D" => SmoothOpenSite.infinitesimal

def fixedEquivalence :
    Discrete (QuotientFixedArcs.Arcs (parameterZero X) m) ≌
      QuotientFixedArcs.Fiber a (parameterZero X) m := by
  letI : (SheafTorsor.restriction (G := locallyConstantGroup H) (parameterZero X)).Full :=
    inferInstanceAs (parameterTorsorEquivalence (H := H) X).inverse.Full
  letI : (SheafTorsor.restriction (G := locallyConstantGroup H) (parameterZero X)).Faithful :=
    inferInstanceAs (parameterTorsorEquivalence (H := H) X).inverse.Faithful
  exact QuotientFixedArcs.equivalence a (parameterZero X) m

variable {a X m}

def forwardArcTransport {n : X ⟶ M} (c : chart a m ⟶ chart a n)
    (h : QuotientFixedArcs.Arcs (parameterZero X) m) :
    QuotientFixedArcs.Arcs (parameterZero X) n :=
  QuotientFixedArcs.forwardArcs (snd D X) (parameterZero_projection X) c h

def forwardArcTransportIso {n : X ⟶ M} (c : chart a m ⟶ chart a n)
    (h : QuotientFixedArcs.Arcs (parameterZero X) m) :
    (QuotientFixedArcs.comparison a (parameterZero X) n).obj ⟨forwardArcTransport c h⟩ ≅
      (QuotientFixedArcs.transport c).obj
        ((QuotientFixedArcs.comparison a (parameterZero X) m).obj ⟨h⟩) :=
  QuotientFixedArcs.forwardComparisonIso (snd D X) (parameterZero_projection X) c h

theorem forwardArcTransport_identity (h : QuotientFixedArcs.Arcs (parameterZero X) m) :
    forwardArcTransport (𝟙 (chart a m)) h = h :=
  QuotientFixedArcs.forwardArcs_identity _ _ h

theorem forwardArcTransport_composition {n k : X ⟶ M}
    (c : chart a m ⟶ chart a n) (d : chart a n ⟶ chart a k)
    (h : QuotientFixedArcs.Arcs (parameterZero X) m) :
    forwardArcTransport (c ≫ d) h = forwardArcTransport d (forwardArcTransport c h) :=
  QuotientFixedArcs.forwardArcs_composition _ _ c d h

def restrictArc {Y : Sheaf SmoothOpenSite.topology Type} (g : Y ⟶ X)
    (h : QuotientFixedArcs.Arcs (parameterZero X) m) :
    QuotientFixedArcs.Arcs (parameterZero Y) (g ≫ m) :=
  QuotientFixedArcs.restrictArcs (parameterZero Y) g (SheafFunction.parameterMap D g)
    (parameterZero_natural g).symm h

theorem forwardArcTransport_natural {Y : Sheaf SmoothOpenSite.topology Type} (g : Y ⟶ X)
    {n : X ⟶ M} (c : chart a m ⟶ chart a n)
    (h : QuotientFixedArcs.Arcs (parameterZero X) m) :
    restrictArc g (forwardArcTransport c h) =
      forwardArcTransport (show chart a (g ≫ m) ⟶ chart a (g ≫ n) from c.reindex g) (restrictArc g h) :=
  QuotientFixedArcs.forwardArcs_natural (parameterZero Y) g (SheafFunction.parameterMap D g)
    (parameterZero_natural g).symm (snd D X) (parameterZero_projection X)
    (snd D Y) (parameterZero_projection Y) rfl c h

open SmoothPresentationSite SmoothGeometricKL EuclideanOpen

/-- Zero evaluation of a parameterized open-domain arc is exactly its base coefficient. -/
theorem openCoefficients_base (U : Domain) {X : Sheaf SmoothOpenSite.topology Type}
    (h : product D X ⟶ embedding.obj U) :
    parameterZero X ≫ h = SmoothOpenArcs.parameterCoefficients U X h ≫ fst _ _ := by
  ext A x
  change h.hom.app A (⟨0, by simp⟩,x) =
    (SmoothOpenArcs.stageCoefficients U A.unop.unop
      (dualSectionsEquiv _ A.unop.unop ((SheafFunction.curry h).hom.app A x)).unop).1.op
  rw [SmoothOpenArcs.dualSections_curry, SmoothOpenArcs.stageCoefficients_zero]
  have hn := congrArg (fun k : (product D X).obj.obj (atStage (dual A.unop.unop)) ⟶
      (embedding.obj U).obj.obj A =>
    k (eps A.unop.unop, X.obj.map (stageMap (inl A.unop.unop)) x))
      (h.hom.naturality (stageMap (dualZero A.unop.unop)))
  have hd : (D).obj.map (stageMap (dualZero A.unop.unop)) (eps A.unop.unop) = ⟨0, by simp⟩ :=
    Subtype.ext (dualLift_eps _ _ _ _)
  have hx : X.obj.map (stageMap (dualZero A.unop.unop))
      (X.obj.map (stageMap (inl A.unop.unop)) x) = x := by
    rw [← ConcreteCategory.comp_apply, ← X.obj.map_comp]
    change X.obj.map (stageMap (inl A.unop.unop ≫ dualZero A.unop.unop)) x = x
    rw [inl_dualZero]
    exact congrArg (fun k => k x) (X.obj.map_id A)
  change h.hom.app A ((D).obj.map _ (eps A.unop.unop),
    X.obj.map _ (X.obj.map _ x)) = _ at hn
  rw [hd, hx] at hn
  exact hn

/-- Fixing an ordinary open's zero lift leaves an arbitrary sheaf-parameter
velocity map. No extra smoothness or constancy of parameters is assumed. -/
def openFixedCoefficients (U : Domain) {X : Sheaf SmoothOpenSite.topology Type}
    (m : X ⟶ embedding.obj U) :
    QuotientFixedArcs.Arcs (parameterZero X) m ≃ (X ⟶ scalarPower U.dimension) where
  toFun h := SmoothOpenArcs.parameterCoefficients U X h.val ≫ snd _ _
  invFun v := ⟨(SmoothOpenArcs.parameterCoefficients U X).symm (lift m v), by
    rw [openCoefficients_base, Equiv.apply_symm_apply]
    rfl⟩
  left_inv h := by
    apply Subtype.ext
    apply (SmoothOpenArcs.parameterCoefficients U X).injective
    rw [Equiv.apply_symm_apply]
    ext A x
    apply Prod.ext
    · exact congrArg (fun k : X ⟶ embedding.obj U => k.hom.app A x)
        ((openCoefficients_base U h.val).symm.trans h.property).symm
    · rfl
  right_inv v := by
    change (SmoothOpenArcs.parameterCoefficients U X)
      ((SmoothOpenArcs.parameterCoefficients U X).symm (lift m v)) ≫ snd _ _ = v
    rw [Equiv.apply_symm_apply]
    rfl

/-- The fixed quotient fiber over an ordinary open is the discrete groupoid of
velocity maps, for arbitrary sheaf parameters. -/
def openFixedFiberEquivalence (U : Domain)
    (b : Action (locallyConstantGroup H) (embedding.obj U))
    (X : Sheaf SmoothOpenSite.topology Type) (m : X ⟶ embedding.obj U) :
    Discrete (X ⟶ scalarPower U.dimension) ≌
      QuotientFixedArcs.Fiber b (parameterZero X) m :=
  (Discrete.equivalence (openFixedCoefficients U m).symm).trans (fixedEquivalence b X m)

open Orbifolds.QuarterTurn SmoothQuarterTurnArcs SmoothQuarterTurnQuotient

theorem originActionArrow_inverse_label (g : C4) :
    arrowLabel (SheafActionQuotient.Arrow.inverse (originActionArrow g)) = constantSection realBase g := by
  ext U y
  change (1 : (locallyConstantGroup C4).obj.obj U) *
    ((constantLabel C4).app U g⁻¹)⁻¹ = (constantLabel C4).app U g
  rw [map_inv, inv_inv, one_mul]

/-- Forward transport is the actual sheaf action on the entire parameterized arc. -/
theorem origin_forward_arc (g : C4)
    (h : QuotientFixedArcs.Arcs (parameterZero realBase) (point coordinateOrigin)) :
    (forwardArcTransport (originActionArrow g) h).val = h.val ≫ SmoothQuarterTurnArcs.diskAction g := by
  change diskRepresentation.action.onMap
    (snd D realBase ≫ arrowLabel (SheafActionQuotient.Arrow.inverse (originActionArrow g))) h.val = _
  rw [originActionArrow_inverse_label]
  ext U y
  exact diskRepresentation.act_constant U g (h.val.hom.app U y)

/-- The actual coherent fiber transport has the expected coefficient map at
all generalized presentation stages. -/
theorem origin_forward_coefficients (g : C4)
    (h : QuotientFixedArcs.Arcs (parameterZero realBase) (point coordinateOrigin))
    (A : SmoothPresentationSite.Code) (x : realBase.obj.obj (SmoothGeometricKL.atStage A)) :
    ((SmoothOpenArcs.parameterCoefficients diskDomain realBase
      (forwardArcTransport (originActionArrow g) h).val).hom.app (SmoothGeometricKL.atStage A) x).2 =
      coefficientAction g
        ((SmoothOpenArcs.parameterCoefficients diskDomain realBase h.val).hom.app
          (SmoothGeometricKL.atStage A) x).2 := by
  rw [origin_forward_arc, SmoothOpenArcs.parameterCoefficients_apply,
    SmoothOpenArcs.parameterCoefficients_apply]
  exact disk_coefficients_action g A _

/-- The real coefficients of forward quotient transport give the already
checked classical manifold derivative at the singular origin. -/
theorem origin_forward_classical (g : C4)
    (h : QuotientFixedArcs.Arcs (parameterZero realBase) (point coordinateOrigin))
    (x : realBase.obj.obj (SmoothGeometricKL.atStage (SmoothPresentationSite.free 0))) :
    complexCoordinates (fun i => SmoothOpenSite.realEvaluation
      (((SmoothOpenArcs.parameterCoefficients diskDomain realBase
        (forwardArcTransport (originActionArrow g) h).val).hom.app
          (SmoothGeometricKL.atStage (SmoothPresentationSite.free 0)) x).2 i)) =
      mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) (fun w : Disk => g • w) origin
        (complexCoordinates (fun i => SmoothOpenSite.realEvaluation
          (((SmoothOpenArcs.parameterCoefficients diskDomain realBase h.val).hom.app
            (SmoothGeometricKL.atStage (SmoothPresentationSite.free 0)) x).2 i))) := by
  rw [origin_forward_coefficients, coefficientAction_natural]
  exact disk_coefficients_classical _ _ _

/-- Ineffective arrows remain different, but their actual fixed-arc transport is identity. -/
def ineffectiveActionArrow (g : C4) (m : realBase ⟶ scalar) :
    chart ineffectiveRepresentation.action m ⟶ chart ineffectiveRepresentation.action m :=
  (ineffectiveArrowEquiv m).symm g⁻¹

theorem ineffectiveActionArrow_inverse_label (g : C4) (m : realBase ⟶ scalar) :
    arrowLabel (SheafActionQuotient.Arrow.inverse (ineffectiveActionArrow g m)) = constantSection realBase g := by
  ext U y
  change (1 : (locallyConstantGroup C4).obj.obj U) *
    ((constantLabel C4).app U g⁻¹)⁻¹ = (constantLabel C4).app U g
  rw [map_inv, inv_inv, one_mul]

theorem ineffective_forward_identity (g : C4) (m : realBase ⟶ scalar)
    (h : QuotientFixedArcs.Arcs (parameterZero realBase) m) :
    forwardArcTransport (ineffectiveActionArrow g m) h = h := by
  apply Subtype.ext
  change ineffectiveRepresentation.action.onMap
    (snd D realBase ≫ arrowLabel (SheafActionQuotient.Arrow.inverse (ineffectiveActionArrow g m))) h.val = _
  rw [ineffectiveActionArrow_inverse_label]
  ext U y
  exact ineffectiveRepresentation.act_constant U g (h.val.hom.app U y)

theorem ineffective_forward_distinct (m : realBase ⟶ scalar) :
    ineffectiveActionArrow quarterTurn m ≠ ineffectiveActionArrow 1 m := by
  intro h
  have he := (ineffectiveArrowEquiv m).symm.injective h
  exact quarterTurn_ne_one (inv_injective he)

end SquareKit.SmoothQuotientTransport

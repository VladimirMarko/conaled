import SquareKit.Internal.CoherentSheafFibration
import Examples.CoherentSheafOver
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck

/-! Recovery of diagrams over changing contexts, including a noninvertible
endomorphism after a round trip through a larger context. -/
noncomputable section
set_option autoImplicit false
namespace Examples.CoherentSheafFibration
open CategoryTheory Opposite SquareKit.CoherentSheafOver
open CategoryTheory.Functor
open CategoryTheory.Pseudofunctor.CoGrothendieck
open SquareKit.RepresentableClassification

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Diagrams
universe u v w a b i j
variable {B : Type u} [Category.{v} B] {D : Type a} [Category.{b} D]
variable (G : B ⥤ D) (J : GrothendieckTopology D) [G.Full] [G.Faithful]
variable [∀ Γ : D, (CostructuredArrow.toOver G Γ).IsCoverDense (J.over Γ)]
variable [∀ (Γ : D) (X : (Over Γ)ᵒᵖ),
  Limits.HasLimitsOfShape (StructuredArrow X (CostructuredArrow.toOver G Γ).op) (Type w)]
variable {I : Type i} [Category.{j} I]

/-- A system over any diagram of contexts recovers through functor composition. -/
def recovery (A : I ⥤ CodeTotal.{u,v,w} G J) :
    A ≅ (A ⋙ totalDecode G J) ⋙ totalCode G J :=
  (CategoryTheory.Functor.rightUnitor A).symm ≪≫
    CategoryTheory.Functor.isoWhiskerLeft A (totalRecovery G J) ≪≫
    (CategoryTheory.Functor.associator A (totalDecode G J) (totalCode G J)).symm

theorem decoded_over (K : I ⥤ D) (A : I ⥤ CodeTotal.{u,v,w} G J)
    (hA : A ⋙ forget (codePseudofunctor G J) = K) :
    (A ⋙ totalDecode G J) ⋙ forget (J.pseudofunctorOver (Type w)) = K := by
  rw [CategoryTheory.Functor.assoc, totalDecode_projection]
  exact hA

theorem recovered_over (K : I ⥤ D) (A : I ⥤ CodeTotal.{u,v,w} G J)
    (hA : A ⋙ forget (codePseudofunctor G J) = K) :
    ((A ⋙ totalDecode G J) ⋙ totalCode G J) ⋙ forget (codePseudofunctor G J) = K := by
  rw [CategoryTheory.Functor.assoc, totalCode_projection]
  exact decoded_over G J K A hA

@[simp] theorem recovery_base (A : I ⥤ CodeTotal.{u,v,w} G J) (i : I) :
    ((recovery G J A).hom.app i).base = 𝟙 (A.obj i).base := by
  simp [recovery]

/-- The recovery isomorphism projects to the identity of the chosen context diagram. -/
theorem recovery_over (K : I ⥤ D) (A : I ⥤ CodeTotal.{u,v,w} G J)
    (hA : A ⋙ forget (codePseudofunctor G J) = K) :
    isoWhiskerRight (recovery G J A) (forget (codePseudofunctor G J)) =
      eqToIso (hA.trans (recovered_over G J K A hA).symm) := by
  apply Iso.ext
  ext i
  simp [recovery]

theorem recovery_naturality (A : I ⥤ CodeTotal.{u,v,w} G J)
    {i j : I} (f : i ⟶ j) :
    A.map f ≫ (recovery G J A).hom.app j =
      (recovery G J A).hom.app i ≫
        ((A ⋙ totalDecode G J) ⋙ totalCode G J).map f :=
  (recovery G J A).hom.naturality f

/-- Recovery also respects arbitrary compatible maps between systems. -/
theorem recovery_map {A B : I ⥤ CodeTotal.{u,v,w} G J} (η : A ⟶ B) :
    η ≫ (recovery G J B).hom =
      (recovery G J A).hom ≫
        whiskerRight (whiskerRight η (totalDecode G J)) (totalCode G J) := by
  apply NatTrans.ext
  funext i
  simpa [recovery] using (totalRecovery G J).hom.naturality (η.app i)

@[simp] theorem recovered_map_base {A B : I ⥤ CodeTotal.{u,v,w} G J}
    (η : A ⟶ B) (i : I) :
    ((whiskerRight (whiskerRight η (totalDecode G J)) (totalCode G J)).app i).base =
      (η.app i).base := by
  simp

/-- A natural transformation over the same context diagram stays over that diagram. -/
theorem recovered_compatible_map (K : I ⥤ D)
    {A B : I ⥤ CodeTotal.{u,v,w} G J} (η : A ⟶ B)
    (hA : A ⋙ forget (codePseudofunctor G J) = K)
    (hB : B ⋙ forget (codePseudofunctor G J) = K)
    (hη : whiskerRight η (forget (codePseudofunctor G J)) = eqToHom (hA.trans hB.symm)) :
    whiskerRight (whiskerRight (whiskerRight η (totalDecode G J)) (totalCode G J))
        (forget (codePseudofunctor G J)) =
      eqToHom ((recovered_over G J K A hA).trans (recovered_over G J K B hB).symm) := by
  ext i
  have hi := NatTrans.congr_app hη i
  simpa using hi

theorem decoded_cartesian (A : I ⥤ CodeTotal.{u,v,w} G J) {i j : I} (f : i ⟶ j)
    [(forget (codePseudofunctor G J)).IsCartesian (A.map f).base (A.map f)] :
    (forget (J.pseudofunctorOver (Type w))).IsCartesian (A.map f).base
      ((A ⋙ totalDecode G J).map f) :=
  totalDecode_cartesian G J (A.map f)

theorem recovered_cartesian (A : I ⥤ CodeTotal.{u,v,w} G J) {i j : I} (f : i ⟶ j)
    [(forget (codePseudofunctor G J)).IsCartesian (A.map f).base (A.map f)] :
    (forget (codePseudofunctor G J)).IsCartesian (A.map f).base
      (((A ⋙ totalDecode G J) ⋙ totalCode G J).map f) := by
  let : (forget (J.pseudofunctorOver (Type w))).IsCartesian
      ((totalDecode G J).map (A.map f)).base ((totalDecode G J).map (A.map f)) :=
    decoded_cartesian G J A f
  exact totalCode_cartesian G J ((totalDecode G J).map (A.map f))

/-- The sheaf-side diagram round trip uses the original total counit. -/
def sheafRecovery (A : I ⥤ SheafTotal.{w} J) :
    (A ⋙ totalCode.{u,v,w} G J) ⋙ totalDecode G J ≅ A :=
  CategoryTheory.Functor.associator A (totalCode G J) (totalDecode G J) ≪≫
    isoWhiskerLeft A (totalCounit G J) ≪≫ CategoryTheory.Functor.rightUnitor A

theorem sheafRecovered_over (K : I ⥤ D) (A : I ⥤ SheafTotal.{w} J)
    (hA : A ⋙ forget (J.pseudofunctorOver (Type w)) = K) :
    ((A ⋙ totalCode.{u,v,w} G J) ⋙ totalDecode G J) ⋙
      forget (J.pseudofunctorOver (Type w)) = K := by
  rw [CategoryTheory.Functor.assoc, totalDecode_projection,
    CategoryTheory.Functor.assoc, totalCode_projection]
  exact hA

theorem sheafRecovery_over (K : I ⥤ D) (A : I ⥤ SheafTotal.{w} J)
    (hA : A ⋙ forget (J.pseudofunctorOver (Type w)) = K) :
    isoWhiskerRight (sheafRecovery G J A) (forget (J.pseudofunctorOver (Type w))) =
      eqToIso ((sheafRecovered_over G J K A hA).trans hA.symm) := by
  apply Iso.ext
  ext i
  simp [sheafRecovery]

theorem sheafRecovery_naturality (A : I ⥤ SheafTotal.{w} J) {i j : I} (f : i ⟶ j) :
    ((A ⋙ totalCode.{u,v,w} G J) ⋙ totalDecode G J).map f ≫
        (sheafRecovery G J A).hom.app j =
      (sheafRecovery G J A).hom.app i ≫ A.map f :=
  (sheafRecovery G J A).hom.naturality f

theorem sheafRecovery_map {A B : I ⥤ SheafTotal.{w} J} (η : A ⟶ B) :
    whiskerRight (whiskerRight η (totalCode.{u,v,w} G J)) (totalDecode G J) ≫
        (sheafRecovery G J B).hom =
      (sheafRecovery G J A).hom ≫ η := by
  apply NatTrans.ext
  funext i
  simpa [sheafRecovery] using (totalCounit G J).hom.naturality (η.app i)

end Diagrams

namespace Boolean
open Examples.CoherentSheafOver.Contexts

abbrev system := codePseudofunctor.{0,0,0} representables J
abbrev code := classifier.inverse.obj pairDisplay
abbrev codeCollapse := classifier.inverse.map collapse

@[simp] theorem diagonal_projection : diagonal ≫ pairProjection = 𝟙 boolContext := by
  ext
  rfl

theorem projection_diagonal_ne_id : pairProjection ≫ diagonal ≠ 𝟙 pairContext := by
  intro h
  have hh := congrArg (fun f => f.app (op (Discrete.mk PUnit.unit)) (true, false)) h
  change (true, true) = (true, false) at hh
  cases hh

abbrev total : CodeTotal representables J := ⟨boolContext, code⟩
abbrev pulled : CodeTotal representables J := domainCartesianLift (F := system) code pairProjection
abbrev twicePulled : CodeTotal representables J :=
  domainCartesianLift (F := system) pulled.fiber diagonal

abbrev projectionLift : pulled ⟶ total := cartesianLift (F := system) code pairProjection
abbrev diagonalLift : twicePulled ⟶ pulled := cartesianLift (F := system) pulled.fiber diagonal
abbrev roundTripLift : twicePulled ⟶ total := diagonalLift ≫ projectionLift

@[simp] theorem roundTripLift_base : roundTripLift.base = 𝟙 boolContext :=
  diagonal_projection

abbrev oppositeDomain : CodeTotal representables J :=
  domainCartesianLift (F := system) twicePulled.fiber pairProjection

abbrev oppositeComposite : oppositeDomain ⟶ pulled :=
  cartesianLift (F := system) twicePulled.fiber pairProjection ≫ diagonalLift

theorem oppositeComposite_base_ne_id : oppositeComposite.base ≠ 𝟙 pairContext :=
  projection_diagonal_ne_id

theorem decoded_opposite_base_ne_id :
    ((totalDecode representables J).map oppositeComposite).base ≠ 𝟙 pairContext :=
  oppositeComposite_base_ne_id

instance roundTripLift_isIso : IsIso roundTripLift := by
  have : IsIso (diagonal ≫ pairProjection) := by rw [diagonal_projection]; infer_instance
  let : (forget system).IsStronglyCartesian diagonal diagonalLift :=
    isStronglyCartesian_homCartesianLift (F := system) pulled.fiber diagonal
  let : (forget system).IsStronglyCartesian pairProjection projectionLift :=
    isStronglyCartesian_homCartesianLift (F := system) code pairProjection
  let : (forget system).IsStronglyCartesian (diagonal ≫ pairProjection) roundTripLift :=
    Functor.IsStronglyCartesian.comp (forget system)
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso (forget system)
    (diagonal ≫ pairProjection) roundTripLift

def roundTripComparison :
    reindex representables J pairProjection ⋙ reindex representables J diagonal ≅
      𝟭 (LocalCode representables J boolContext) :=
  reindexComp representables J pairProjection diagonal ≪≫
    eqToIso (congrArg (reindex representables J) diagonal_projection) ≪≫
    reindexId representables J boolContext

abbrev twicePulledCollapse : twicePulled.fiber ⟶ twicePulled.fiber :=
  (reindex representables J diagonal).map
    ((reindex representables J pairProjection).map codeCollapse)

abbrev verticalCollapse : twicePulled ⟶ twicePulled :=
  (ι system boolContext).map twicePulledCollapse

abbrev composedCollapse : twicePulled ⟶ total := verticalCollapse ≫ roundTripLift

@[simp] theorem composedCollapse_base : composedCollapse.base = 𝟙 boolContext := by
  change 𝟙 boolContext ≫ (diagonal ≫ pairProjection) = 𝟙 boolContext
  simp

theorem collapse_idempotent : collapse ≫ collapse = collapse := by
  ext
  rfl

theorem codeCollapse_idempotent : codeCollapse ≫ codeCollapse = codeCollapse := by
  rw [← classifier.inverse.map_comp, collapse_idempotent]

theorem twicePulledCollapse_not_iso : ¬ IsIso twicePulledCollapse := by
  intro h
  let : (reindex representables J pairProjection ⋙
      reindex representables J diagonal).IsEquivalence :=
    Functor.isEquivalence_of_iso roundTripComparison.symm
  let : IsIso ((reindex representables J pairProjection ⋙
      reindex representables J diagonal).map codeCollapse) := h
  exact code_collapse_not_iso
    (isIso_of_reflects_iso codeCollapse
      (reindex representables J pairProjection ⋙ reindex representables J diagonal))

theorem twicePulledCollapse_idempotent :
    twicePulledCollapse ≫ twicePulledCollapse = twicePulledCollapse := by
  exact ((reindex representables J pairProjection ⋙
      reindex representables J diagonal).map_comp codeCollapse codeCollapse).symm.trans
    (congrArg ((reindex representables J pairProjection ⋙
      reindex representables J diagonal).map) codeCollapse_idempotent)

theorem verticalCollapse_not_iso : ¬ IsIso verticalCollapse := by
  intro h
  have hi : verticalCollapse ≫ verticalCollapse = verticalCollapse := by
    change (ι system boolContext).map twicePulledCollapse ≫
      (ι system boolContext).map twicePulledCollapse = _
    rw [← Functor.map_comp, twicePulledCollapse_idempotent]
  have he : verticalCollapse = 𝟙 twicePulled :=
    (cancel_mono verticalCollapse).1 (by simpa using hi)
  let : (ι system boolContext).Faithful := by
    change (HasFibers.ι (p := forget system) boolContext).Faithful
    infer_instance
  have hf : twicePulledCollapse = 𝟙 twicePulled.fiber := by
    apply (ι system boolContext).map_injective
    rw [(ι system boolContext).map_id]
    exact he
  apply twicePulledCollapse_not_iso
  rw [hf]
  infer_instance

theorem composedCollapse_not_iso : ¬ IsIso composedCollapse := by
  intro h
  have : IsIso verticalCollapse := IsIso.of_isIso_comp_right verticalCollapse roundTripLift
  exact verticalCollapse_not_iso this

theorem collapse_fiber_recovery :
    twicePulledCollapse ≫ roundTripComparison.hom.app code =
      roundTripComparison.hom.app code ≫ codeCollapse :=
  roundTripComparison.hom.naturality codeCollapse

/-- The public decoder composes both nonidentity context changes with the collapse. -/
theorem decoded_composite :
    (totalDecode representables J).map composedCollapse =
      (totalDecode representables J).map verticalCollapse ≫
        (totalDecode representables J).map diagonalLift ≫
          (totalDecode representables J).map projectionLift := by
  rw [show composedCollapse = verticalCollapse ≫ (diagonalLift ≫ projectionLift) from rfl]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]

theorem decoded_composite_not_iso :
    ¬ IsIso ((totalDecode representables J).map composedCollapse) := by
  intro h
  let : IsIso ((totalEquivalence representables J).functor.map composedCollapse) := h
  exact composedCollapse_not_iso
    (isIso_of_reflects_iso composedCollapse (totalEquivalence representables J).functor)

/-- Recovery naturality sees the whole composed arrow, including its noninvertible map. -/
theorem composite_recovery_naturality :
    composedCollapse ≫ (totalRecovery representables J).hom.app total =
      (totalRecovery representables J).hom.app twicePulled ≫
        (totalCode representables J).map ((totalDecode representables J).map composedCollapse) :=
  (totalRecovery representables J).hom.naturality composedCollapse

end Boolean
section UnequalUniverses
variable {B : Type} [Category.{1} B] {D : Type 2} [Category.{3} D]
variable (G : B ⥤ D) (J : GrothendieckTopology D) [G.Full] [G.Faithful]
variable [∀ Γ : D, (CostructuredArrow.toOver G Γ).IsCoverDense (J.over Γ)]
variable [∀ (Γ : D) (X : (Over Γ)ᵒᵖ),
  Limits.HasLimitsOfShape (StructuredArrow X (CostructuredArrow.toOver G Γ).op) (Type 4)]

example : CodeTotal.{0,1,4} G J ≌ SheafTotal.{4} J := totalEquivalence G J

example {A B : CodeTotal.{0,1,4} G J} (f : A ⟶ B) :
    ((totalDecode G J).map f).fiber =
      (sheafOverClassification G J A.base).functor.map f.fiber ≫
        (decodeReindex G J f.base).hom.app B.fiber := totalDecode_map_fiber G J f
end UnequalUniverses

section ReversedUniverses
variable {B : Type 4} [Category.{3} B] {D : Type 2} [Category.{1} D]
variable (G : B ⥤ D) (J : GrothendieckTopology D) [G.Full] [G.Faithful]
variable [∀ Γ : D, (CostructuredArrow.toOver G Γ).IsCoverDense (J.over Γ)]
variable [∀ (Γ : D) (X : (Over Γ)ᵒᵖ),
  Limits.HasLimitsOfShape (StructuredArrow X (CostructuredArrow.toOver G Γ).op) Type]

example : CodeTotal.{4,3,0} G J ≌ SheafTotal.{0} J := totalEquivalence G J
end ReversedUniverses

end Examples.CoherentSheafFibration

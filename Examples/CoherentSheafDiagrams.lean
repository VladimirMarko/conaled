import SquareKit.Internal.CoherentSheafDiagrams
import Examples.CoherentSheafFibration
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-! Universal properties and arbitrary vertical maps in fixed-context diagram categories. -/
noncomputable section
set_option autoImplicit false
namespace Examples.CoherentSheafDiagrams
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Pseudofunctor.CoGrothendieck
open SquareKit.CoherentSheafOver
open SquareKit.RepresentableClassification

section UniversalProperties
universe u v w a b i j
variable {B : Type u} [Category.{v} B] {D : Type a} [Category.{b} D]
variable (G : B ⥤ D) (J : GrothendieckTopology D) [G.Full] [G.Faithful]
variable [∀ Γ : D, (CostructuredArrow.toOver G Γ).IsCoverDense (J.over Γ)]
variable [∀ (Γ : D) (X : (Over Γ)ᵒᵖ),
  HasLimitsOfShape (StructuredArrow X (CostructuredArrow.toOver G Γ).op) (Type w)]
variable {I : Type i} [Category.{j} I] (K : I ⥤ D)

/-- A universal solution of compatible constraints remains universal after decoding. -/
def decodedEqualizer
    {A X Y : CodeDiagrams.{u,v,w} G J K} {f g : X ⟶ Y} {h : A ⟶ X}
    (w : h ≫ f = h ≫ g) (hlim : IsLimit (Fork.ofι h w)) :
    IsLimit (Fork.ofι ((diagramEquivalence G J K).functor.map h)
      (by simp only [← Functor.map_comp, w]) :
      Fork ((diagramEquivalence G J K).functor.map f)
        ((diagramEquivalence G J K).functor.map g)) :=
  isLimitForkMapOfIsLimit (diagramEquivalence G J K).functor w hlim

/-- The sheaf-side universal property proves the code-side universal property. -/
def codeEqualizerOfDecoded
    {A X Y : CodeDiagrams.{u,v,w} G J K} {f g : X ⟶ Y} {h : A ⟶ X}
    (w : h ≫ f = h ≫ g)
    (hlim : IsLimit (Fork.ofι ((diagramEquivalence G J K).functor.map h)
      (by simp only [← Functor.map_comp, w]) :
      Fork ((diagramEquivalence G J K).functor.map f)
        ((diagramEquivalence G J K).functor.map g))) :
    IsLimit (Fork.ofι h w) :=
  isLimitOfIsLimitForkMap (diagramEquivalence G J K).functor w hlim

/-- Cartesian sections retain the same universal-property transport for arbitrary maps. -/
def decodedCartesianEqualizer
    {A X Y : CodeCartesianDiagrams.{u,v,w} G J K} {f g : X ⟶ Y} {h : A ⟶ X}
    (w : h ≫ f = h ≫ g) (hlim : IsLimit (Fork.ofι h w)) :
    IsLimit (Fork.ofι ((cartesianDiagramEquivalence G J K).functor.map h)
      (by simp only [← Functor.map_comp, w]) :
      Fork ((cartesianDiagramEquivalence G J K).functor.map f)
        ((cartesianDiagramEquivalence G J K).functor.map g)) :=
  isLimitForkMapOfIsLimit (cartesianDiagramEquivalence G J K).functor w hlim

/-- This reflects an existing limiting fork; it assumes no general limit-existence result. -/
def codeCartesianEqualizerOfDecoded
    {A X Y : CodeCartesianDiagrams.{u,v,w} G J K} {f g : X ⟶ Y} {h : A ⟶ X}
    (w : h ≫ f = h ≫ g)
    (hlim : IsLimit (Fork.ofι ((cartesianDiagramEquivalence G J K).functor.map h)
      (by simp only [← Functor.map_comp, w]) :
      Fork ((cartesianDiagramEquivalence G J K).functor.map f)
        ((cartesianDiagramEquivalence G J K).functor.map g))) :
    IsLimit (Fork.ofι h w) :=
  isLimitOfIsLimitForkMap (cartesianDiagramEquivalence G J K).functor w hlim
end UniversalProperties

namespace Boolean
set_option backward.isDefEq.respectTransparency false
open Examples.CoherentSheafOver.Contexts
open Examples.CoherentSheafFibration.Boolean

abbrev constantContext := (Functor.const WalkingParallelPair).obj twicePulled.base

/-- Identity transitions are cartesian, independently of the vertical maps between sections. -/
def constantDiagram : CodeCartesianDiagrams representables J constantContext where
  obj := { toFunctor := (Functor.const WalkingParallelPair).obj twicePulled, w := rfl }
  property := by
    intro i j f
    change (forget system).IsCartesian ((forget system).map (𝟙 twicePulled)) (𝟙 twicePulled)
    infer_instance

/-- The existing noninvertible collapse is a map of cartesian sections. -/
def constantCollapse : constantDiagram ⟶ constantDiagram :=
  ObjectProperty.homMk
    { toNatTrans := (Functor.const WalkingParallelPair).map verticalCollapse
      isHomLift' := fun _ => by
        apply IsHomLift.of_fac _ _ _ rfl rfl
        rfl }

theorem constantCollapse_not_iso : ¬ IsIso constantCollapse := by
  intro h
  have : IsIso constantCollapse.hom := inferInstance
  have : IsIso (X := constantDiagram.obj.toFunctor) constantCollapse.hom.toNatTrans := inferInstance
  have : IsIso (constantCollapse.hom.toNatTrans.app WalkingParallelPair.zero) := inferInstance
  exact verticalCollapse_not_iso this

theorem decodedConstantCollapse_not_iso :
    ¬ IsIso ((cartesianDiagramEquivalence representables J constantContext).functor.map
      constantCollapse) := by
  intro h
  exact constantCollapse_not_iso
    (isIso_of_reflects_iso constantCollapse
      (cartesianDiagramEquivalence representables J constantContext).functor)

/-- The packaged unit recovers this arbitrary map inside the cartesian-section category. -/
theorem constantCollapse_recovery :
    constantCollapse ≫
        (cartesianDiagramEquivalence representables J constantContext).unitIso.hom.app
          constantDiagram =
      (cartesianDiagramEquivalence representables J constantContext).unitIso.hom.app
          constantDiagram ≫
        (cartesianDiagramEquivalence representables J constantContext).inverse.map
          ((cartesianDiagramEquivalence representables J constantContext).functor.map
            constantCollapse) := by
  exact
    (cartesianDiagramEquivalence representables J constantContext).unitIso.hom.naturality
      constantCollapse

abbrev changingFunctor := parallelPair oppositeComposite oppositeComposite
abbrev changingContext := changingFunctor ⋙ forget system

/-- Both transitions compose canonical lifts over the nonidentity context endomorphism. -/
def changingDiagram : CodeCartesianDiagrams representables J changingContext where
  obj := { toFunctor := changingFunctor, w := rfl }
  property := by
    intro i j f
    have : (forget system).IsStronglyCartesian pairProjection
        (cartesianLift (F := system) twicePulled.fiber pairProjection) :=
      isStronglyCartesian_homCartesianLift (F := system) twicePulled.fiber pairProjection
    have : (forget system).IsStronglyCartesian diagonal diagonalLift :=
      isStronglyCartesian_homCartesianLift (F := system) pulled.fiber diagonal
    have : (forget system).IsStronglyCartesian (pairProjection ≫ diagonal) oppositeComposite :=
      Functor.IsStronglyCartesian.comp (forget system)
    cases f with
    | left =>
      change (forget system).IsCartesian (pairProjection ≫ diagonal) oppositeComposite
      infer_instance
    | right =>
      change (forget system).IsCartesian (pairProjection ≫ diagonal) oppositeComposite
      infer_instance
    | id i =>
      change (forget system).IsCartesian ((forget system).map (𝟙 _)) (𝟙 _)
      infer_instance

theorem changingContext_left_not_id :
    changingContext.map WalkingParallelPairHom.left ≠ 𝟙 pairContext :=
  oppositeComposite_base_ne_id

abbrev decodedChangingDiagram : SheafCartesianDiagrams J changingContext :=
  (cartesianDiagramEquivalence representables J changingContext).functor.obj changingDiagram

/-- Decoding retains the actual nonidentity context map. -/
theorem decodedChangingDiagram_left_base :
    (decodedChangingDiagram.obj.map WalkingParallelPairHom.left).base =
      pairProjection ≫ diagonal := by
  change ((totalDecode representables J).map oppositeComposite).base = _
  simp

theorem decodedChangingDiagram_left_cartesian :
    (forget (J.pseudofunctorOver (Type 0))).IsCartesian
      (decodedChangingDiagram.obj.map WalkingParallelPairHom.left).base
      (decodedChangingDiagram.obj.map WalkingParallelPairHom.left) :=
  decodedChangingDiagram.property WalkingParallelPairHom.left

end Boolean

namespace NonverticalControl
abbrev Index := Discrete PUnit.{1}
abbrev context : Index ⥤ Type := (Functor.const Index).obj Bool

def diagram : SquareKit.BasedDiagram.Over (𝟭 (Type)) context where
  toFunctor := context
  w := rfl

/-- An ambient transformation need not be vertical even when both diagrams lie over K. -/
def collapse : diagram.toFunctor ⟶ diagram.toFunctor :=
  (Functor.const Index).map (TypeCat.ofHom (fun _ : Bool => false))

set_option backward.isDefEq.respectTransparency false in
theorem collapse_not_vertical :
    ¬ ∀ i, (𝟭 (Type)).IsHomLift (𝟙 (context.obj i)) (collapse.app i) := by
  intro h
  let : (𝟭 (Type)).IsHomLift (𝟙 Bool) (collapse.app ⟨PUnit.unit⟩) := h _
  have he := IsHomLift.eq_of_isHomLift (𝟭 (Type)) (𝟙 Bool) (collapse.app ⟨PUnit.unit⟩)
  have hc := congrArg (fun f : Bool ⟶ Bool => f true) he
  cases hc

/-- The category rejects the nonvertical ambient transformation as a morphism. -/
theorem collapse_not_diagram_map :
    ¬ ∃ η : diagram ⟶ diagram, η.toNatTrans = collapse := by
  rintro ⟨η, hη⟩
  apply collapse_not_vertical
  intro i
  rw [← hη]
  exact η.isHomLift' i
end NonverticalControl

section UnequalUniverses
variable {B : Type} [Category.{1} B] {D : Type 2} [Category.{3} D]
variable (G : B ⥤ D) (J : GrothendieckTopology D) [G.Full] [G.Faithful]
variable [∀ Γ : D, (CostructuredArrow.toOver G Γ).IsCoverDense (J.over Γ)]
variable [∀ (Γ : D) (X : (Over Γ)ᵒᵖ),
  HasLimitsOfShape (StructuredArrow X (CostructuredArrow.toOver G Γ).op) (Type 4)]
variable {I : Type 5} [Category.{6} I] (K : I ⥤ D)

example : CodeDiagrams.{0,1,4} G J K ≌ SheafDiagrams.{4} J K :=
  diagramEquivalence G J K

example : CodeCartesianDiagrams.{0,1,4} G J K ≌ SheafCartesianDiagrams.{4} J K :=
  cartesianDiagramEquivalence G J K
end UnequalUniverses

section ReversedUniverses
variable {B : Type 4} [Category.{3} B] {D : Type 2} [Category.{1} D]
variable (G : B ⥤ D) (J : GrothendieckTopology D) [G.Full] [G.Faithful]
variable [∀ Γ : D, (CostructuredArrow.toOver G Γ).IsCoverDense (J.over Γ)]
variable [∀ (Γ : D) (X : (Over Γ)ᵒᵖ),
  HasLimitsOfShape (StructuredArrow X (CostructuredArrow.toOver G Γ).op) Type]
variable {I : Type 6} [Category.{5} I] (K : I ⥤ D)

example : CodeDiagrams.{4,3,0} G J K ≌ SheafDiagrams.{0} J K :=
  diagramEquivalence G J K

example : CodeCartesianDiagrams.{4,3,0} G J K ≌ SheafCartesianDiagrams.{0} J K :=
  cartesianDiagramEquivalence G J K
end ReversedUniverses

end Examples.CoherentSheafDiagrams

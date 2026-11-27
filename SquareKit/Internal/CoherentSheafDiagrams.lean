import SquareKit.BasedDiagram
import SquareKit.Internal.CoherentSheafFibration

/-! Equivalences of coherent local-code and slice-sheaf diagrams over a fixed
diagram of contexts. Cartesian diagrams retain all vertical transformations. -/

noncomputable section
set_option autoImplicit false

namespace SquareKit.CoherentSheafOver

open CategoryTheory Opposite
open CategoryTheory.Pseudofunctor.CoGrothendieck

universe u v w a b i j
variable {B : Type u} [Category.{v} B] {D : Type a} [Category.{b} D]
variable (G : B ⥤ D) (J : GrothendieckTopology D) [G.Full] [G.Faithful]
variable [∀ Γ : D, (CostructuredArrow.toOver G Γ).IsCoverDense (J.over Γ)]
variable [∀ (Γ : D) (X : (Over Γ)ᵒᵖ),
  Limits.HasLimitsOfShape (StructuredArrow X (CostructuredArrow.toOver G Γ).op) (Type w)]
variable {I : Type i} [Category.{j} I] (K : I ⥤ D)

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Coherent local-code diagrams over K, with arbitrary vertical transformations. -/
abbrev CodeDiagrams := BasedDiagram.Over (forget (codePseudofunctor.{u,v,w} G J)) K

/-- Slice-sheaf diagrams over K, with arbitrary vertical transformations. -/
abbrev SheafDiagrams := BasedDiagram.Over (forget (J.pseudofunctorOver (Type w))) K

/-- Coherent local-code diagrams whose transitions are cartesian. -/
abbrev CodeCartesianDiagrams :=
  BasedDiagram.CartesianOver (forget (codePseudofunctor.{u,v,w} G J)) K

/-- Slice-sheaf diagrams whose transitions are cartesian. -/
abbrev SheafCartesianDiagrams :=
  BasedDiagram.CartesianOver (forget (J.pseudofunctorOver (Type w))) K

/-- Decode and encode whole diagrams over K, including every vertical map. -/
def diagramEquivalence : CodeDiagrams.{u,v,w} G J K ≌ SheafDiagrams.{w} J K :=
  BasedDiagram.equivalence
    (forget (codePseudofunctor G J)) (forget (J.pseudofunctorOver (Type w))) K
    (totalEquivalence G J) (totalDecode_projection G J) (totalCode_projection G J)
    (fun A => by
      apply IsHomLift.of_fac _ _ _ rfl rfl
      change 𝟙 A.base = 𝟙 A.base ≫ 𝟙 A.base ≫ 𝟙 A.base
      simp)
    (fun A => by
      apply IsHomLift.of_fac _ _ _ rfl rfl
      change 𝟙 A.base = 𝟙 A.base ≫ 𝟙 A.base ≫ 𝟙 A.base
      simp)

/-- The forward operation is the existing total decoder composed with the diagram. -/
@[simp] theorem diagramEquivalence_functor_obj (A : CodeDiagrams.{u,v,w} G J K) :
    ((diagramEquivalence G J K).functor.obj A).toFunctor = A.toFunctor ⋙ totalDecode G J := rfl

/-- The inverse operation is the existing total encoder composed with the diagram. -/
@[simp] theorem diagramEquivalence_inverse_obj (A : SheafDiagrams.{w} J K) :
    ((diagramEquivalence.{u,v,w} G J K).inverse.obj A).toFunctor =
      A.toFunctor ⋙ totalCode G J := rfl

@[simp] theorem diagramEquivalence_functor_map
    {A B : CodeDiagrams.{u,v,w} G J K} (η : A ⟶ B) :
    ((diagramEquivalence G J K).functor.map η).toNatTrans =
      Functor.whiskerRight η.toNatTrans (totalDecode G J) := rfl

@[simp] theorem diagramEquivalence_inverse_map
    {A B : SheafDiagrams.{w} J K} (η : A ⟶ B) :
    ((diagramEquivalence.{u,v,w} G J K).inverse.map η).toNatTrans =
      Functor.whiskerRight η.toNatTrans (totalCode G J) := rfl

/-- Diagram recovery uses the original total recovery at every index. -/
@[simp] theorem diagramEquivalence_unit_app (A : CodeDiagrams.{u,v,w} G J K) (i : I) :
    ((diagramEquivalence G J K).unitIso.hom.app A).app i =
      (totalRecovery G J).hom.app (A.obj i) := rfl

/-- The diagram counit uses the original total counit at every index. -/
@[simp] theorem diagramEquivalence_counit_app (A : SheafDiagrams.{w} J K) (i : I) :
    ((diagramEquivalence.{u,v,w} G J K).counitIso.hom.app A).app i =
      (totalCounit G J).hom.app (A.obj i) := rfl

/-- Restrict to cartesian transitions while retaining every vertical transformation. -/
def cartesianDiagramEquivalence :
    CodeCartesianDiagrams.{u,v,w} G J K ≌ SheafCartesianDiagrams.{w} J K :=
  BasedDiagram.cartesianEquivalence
    (forget (codePseudofunctor G J)) (forget (J.pseudofunctorOver (Type w))) K
    (totalEquivalence G J) (totalDecode_projection G J) (totalCode_projection G J)
    (fun A => by
      apply IsHomLift.of_fac _ _ _ rfl rfl
      change 𝟙 A.base = 𝟙 A.base ≫ 𝟙 A.base ≫ 𝟙 A.base
      simp)
    (fun A => by
      apply IsHomLift.of_fac _ _ _ rfl rfl
      change 𝟙 A.base = 𝟙 A.base ≫ 𝟙 A.base ≫ 𝟙 A.base
      simp)
    (fun _ _ f hf => by
      have : (forget (codePseudofunctor G J)).IsCartesian f.base f := hf
      exact totalDecode_cartesian G J f)
    (fun _ _ f hf => by
      have : (forget (J.pseudofunctorOver (Type w))).IsCartesian f.base f := hf
      change (forget (codePseudofunctor G J)).IsCartesian
        ((totalCode G J).map f).base ((totalCode G J).map f)
      rw [totalCode_map_base]
      exact totalCode_cartesian G J f)

@[simp] theorem cartesianDiagramEquivalence_functor_obj
    (A : CodeCartesianDiagrams.{u,v,w} G J K) :
    ((cartesianDiagramEquivalence G J K).functor.obj A).obj.toFunctor =
      A.obj.toFunctor ⋙ totalDecode G J := rfl

@[simp] theorem cartesianDiagramEquivalence_inverse_obj
    (A : SheafCartesianDiagrams.{w} J K) :
    ((cartesianDiagramEquivalence.{u,v,w} G J K).inverse.obj A).obj.toFunctor =
      A.obj.toFunctor ⋙ totalCode G J := rfl

@[simp] theorem cartesianDiagramEquivalence_functor_map
    {A B : CodeCartesianDiagrams.{u,v,w} G J K} (η : A ⟶ B) :
    ((cartesianDiagramEquivalence G J K).functor.map η).hom.toNatTrans =
      Functor.whiskerRight η.hom.toNatTrans (totalDecode G J) := rfl

@[simp] theorem cartesianDiagramEquivalence_inverse_map
    {A B : SheafCartesianDiagrams.{w} J K} (η : A ⟶ B) :
    ((cartesianDiagramEquivalence.{u,v,w} G J K).inverse.map η).hom.toNatTrans =
      Functor.whiskerRight η.hom.toNatTrans (totalCode G J) := rfl

@[simp] theorem cartesianDiagramEquivalence_unit_app
    (A : CodeCartesianDiagrams.{u,v,w} G J K) (i : I) :
    ((cartesianDiagramEquivalence G J K).unitIso.hom.app A).hom.app i =
      (totalRecovery G J).hom.app (A.obj.obj i) := rfl

@[simp] theorem cartesianDiagramEquivalence_counit_app
    (A : SheafCartesianDiagrams.{w} J K) (i : I) :
    ((cartesianDiagramEquivalence.{u,v,w} G J K).counitIso.hom.app A).hom.app i =
      (totalCounit G J).hom.app (A.obj.obj i) := rfl

end SquareKit.CoherentSheafOver

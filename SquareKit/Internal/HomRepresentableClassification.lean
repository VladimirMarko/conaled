import SquareKit.Internal.SheafRepresentableClassification
import Mathlib.CategoryTheory.Sites.SheafOfTypes

/-! Codes for maps to a presheaf, with the precise sheafness criterion. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.RepresentableClassification.HomSystem
open CategoryTheory Opposite
universe u v w
variable {C : Type v} [Category.{w} C] (B : Context.{u} C)

def system : System.{u} C where
  Data Γ := ULift.{max v (u+1) (w+1)} (Γ ⟶ B)
  restrict a σ := ⟨σ ≫ a.down⟩
  restrict_id a := congrArg ULift.up (Category.id_comp a.down)
  restrict_comp a σ τ := congrArg ULift.up (Category.assoc τ σ a.down).symm

/-- Evaluation at the identity; its inverse is the represented section. -/
def sectionEquiv (I : C) : (system B).codes.obj (op I) ≃
    (raisedContext B).obj (op I) where
  toFun a := ⟨a.down.app (op I) ⟨𝟙 I⟩⟩
  invFun b := ⟨represented (B.elementsMk (op I) b.down)⟩
  left_inv a := by
    apply ULift.ext
    exact represented_map_generic a.down
  right_inv b := by
    apply ULift.ext
    exact represented_id (B.elementsMk (op I) b.down)

def codesIso : (system B).codes ≅ raisedContext B :=
  NatIso.ofComponents (fun I => (sectionEquiv B I.unop).toIso) (by
    intro I J f
    ext a
    change ULift.up (a.down.app J ⟨𝟙 J.unop ≫ f.unop⟩) =
      ULift.up (B.map f (a.down.app I ⟨𝟙 I.unop⟩))
    apply congrArg ULift.up
    have h := ConcreteCategory.congr_hom (a.down.naturality f) (show (representable.{u} I.unop).obj I from ⟨𝟙 I.unop⟩)
    change a.down.app J ⟨f.unop ≫ 𝟙 I.unop⟩ = B.map f (a.down.app I ⟨𝟙 I.unop⟩) at h
    simpa only [Category.id_comp, Category.comp_id] using h)

@[simp] theorem codesIso_code {Γ : Context.{u} C} (a : Γ ⟶ B) :
    (system B).code ⟨a⟩ ≫ (codesIso B).hom = raisedSub a := by
  ext I x
  change ULift.up (a.app I (Γ.map (𝟙 I.unop).op x.down)) = ULift.up (a.app I x.down)
  rw [show (𝟙 I.unop).op = 𝟙 I from rfl, Γ.map_id]
  rfl

/-- Universe raising changes neither existence nor uniqueness of amalgamations. -/
theorem codes_isSheaf_iff (J : GrothendieckTopology C) :
    Presheaf.IsSheaf J (system B).codes ↔ Presheaf.IsSheaf J B := by
  rw [Presheaf.isSheaf_of_iso_iff (codesIso B)]
  rw [isSheaf_iff_isSheaf_of_type, isSheaf_iff_isSheaf_of_type]
  exact Presieve.isSheaf_comp_uliftFunctor_iff (P := B) J

theorem codes_isSheaf {J : GrothendieckTopology C} (hB : Presheaf.IsSheaf J B) :
    Presheaf.IsSheaf J (system B).codes := (codes_isSheaf_iff B J).2 hB

end SquareKit.RepresentableClassification.HomSystem

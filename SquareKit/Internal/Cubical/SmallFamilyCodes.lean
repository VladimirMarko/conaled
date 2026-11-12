import SquareKit.Internal.Cubical.LocalFillingBridge
import SquareKit.Internal.Cubical.FamilyData

/-! Small codes retain a family over a represented cube and its selected lawful
local filler. The code presheaf lies one universe above its fibers. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

structure LocalFamily (Γ : Context.{u}) where
  family : Family Γ
  filling : LocalFilling family
  lawful : filling.Lawful

def LocalFamily.reindex {Γ Δ : Context.{u}} (A : LocalFamily Γ) (σ : Δ ⟶ Γ) : LocalFamily Δ :=
  ⟨Presheaf.reindex A.family σ,A.filling.reindex σ,A.lawful.reindex σ⟩

def LocalFamily.ofNative {Γ : Context.{u}} (A : LawfulFamily Γ) : LocalFamily Γ :=
  ⟨A.family,A.filling.toLocal,Filling.toLocal_lawful A.lawful⟩

def LocalFamily.toNative {Γ : Context.{u}} (A : LocalFamily Γ) : LawfulFamily Γ :=
  ⟨⟨A.family,A.filling.toFilling A.lawful⟩,A.filling.toFilling_lawful A.lawful⟩

theorem LocalFamily.reindex_id {Γ : Context.{u}} (A : LocalFamily Γ) : A.reindex (𝟙 Γ) = A := rfl

theorem LocalFamily.reindex_comp {Γ Δ Θ : Context.{u}} (A : LocalFamily Γ)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) : (A.reindex σ).reindex τ = A.reindex (τ ≫ σ) := rfl

abbrev SmallFamilyCode (I : Cube) := LocalFamily (representable.{u} I)

def smallFamilyCodes : Context.{u+1} where
  obj I := SmallFamilyCode.{u} I.unop
  map f := TypeCat.ofHom (fun A => A.reindex (representableMap f.unop))
  map_id I := by
    apply ConcreteCategory.hom_ext
    intro A
    have e : representableMap (𝟙 I.unop) = 𝟙 (representable.{u} I.unop) := by
      ext J f
      exact congrArg ULift.up (Category.comp_id f.down)
    exact (congrArg A.reindex e).trans (A.reindex_id)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro A
    have e : representableMap (g.unop ≫ f.unop) =
        representableMap g.unop ≫ representableMap f.unop := by
      ext J h
      exact congrArg ULift.up (Category.assoc h.down g.unop f.unop).symm
    exact (congrArg A.reindex e).trans (A.reindex_comp _ _).symm

end SquareKit.Cubical.Presheaf

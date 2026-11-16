import SquareKit.Internal.Cubical.CartesianLocalFillingBridge

/-! Small codes retain a family over a represented cube and its selected lawful
local filler. The code presheaf lies one universe above its fibers. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u

structure LocalFamily (Γ : Context.{u}) where
  family : Family Γ
  filling : LocalFilling family
  lawful : filling.Lawful

def LocalFamily.reindex {Γ Δ : Context.{u}} (A : LocalFamily Γ) (σ : Δ ⟶ Γ) : LocalFamily Δ :=
  ⟨Cartesian.reindex A.family σ,A.filling.reindex σ,A.lawful.reindex σ⟩

def LocalFamily.ofFilling {Γ : Context.{u}} (A : Family Γ) (F : Filling A)
    (hF : F.Lawful) : LocalFamily Γ :=
  ⟨A, F.toLocal, Filling.toLocal_lawful hF⟩

def LocalFamily.toFilling {Γ : Context.{u}} (A : LocalFamily Γ) : Filling A.family :=
  A.filling.toFilling A.lawful

theorem LocalFamily.toFilling_lawful {Γ : Context.{u}} (A : LocalFamily Γ) :
    A.toFilling.Lawful := A.filling.toFilling_lawful A.lawful

@[ext] theorem LocalFamily.ext {Γ : Context.{u}} {A B : LocalFamily Γ}
    (h : A.family = B.family) (hF : HEq A.filling B.filling) : A = B := by
  cases A
  cases B
  cases h
  cases hF
  rfl

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

end SquareKit.Cubical.Cartesian

import Mathlib.Tactic.DSimpPercent
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

/-- Restriction of complete native local-family data supplies the shared coding laws. -/
def localFamilySystem : RepresentableClassification.System.{u} Cube where
  Data := LocalFamily
  restrict := LocalFamily.reindex
  restrict_id := LocalFamily.reindex_id
  restrict_comp := LocalFamily.reindex_comp

-- Specialize once so nested clients do not repeatedly reduce adapter projections.
def smallFamilyCodes : Context.{u+1} :=
  dsimp% only [RepresentableClassification.System.codes, localFamilySystem]
    localFamilySystem.codes

end SquareKit.Cubical.Presheaf

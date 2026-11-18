import Mathlib.Tactic.DSimpPercent
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

end SquareKit.Cubical.Cartesian

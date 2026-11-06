import SquareKit.Internal.Cubical.NormalizedIdentityFilling

/-! Raw semantic family data retains a selected filler. Lawfulness is a
separate predicate; the certified boundary is used by the source-model adapter. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

structure FamilyData (Γ : Context.{u}) where
  family : Family Γ
  filling : Filling family

abbrev FamilyData.Lawful {Γ : Context.{u}} (A : FamilyData Γ) : Prop := A.filling.Lawful
abbrev LawfulFamily (Γ : Context.{u}) := {A : FamilyData Γ // A.Lawful}

namespace FamilyData

def reindex {Γ Δ : Context.{u}} (A : FamilyData Γ) (σ : Δ ⟶ Γ) : FamilyData Δ :=
  ⟨Presheaf.reindex A.family σ,A.filling.reindex σ⟩

theorem Lawful.reindex {Γ Δ : Context.{u}} {A : FamilyData Γ} (hA : A.Lawful) (σ : Δ ⟶ Γ) :
    (A.reindex σ).Lawful := Filling.Lawful.reindex hA σ

@[ext] theorem ext {Γ : Context.{u}} {A B : FamilyData Γ} (h : A.family = B.family)
    (hF : HEq A.filling B.filling) : A = B := by
  cases A
  cases B
  cases h
  cases hF
  rfl

end FamilyData

namespace LawfulFamily
abbrev family {Γ : Context.{u}} (A : LawfulFamily Γ) := A.val.family
abbrev filling {Γ : Context.{u}} (A : LawfulFamily Γ) := A.val.filling
abbrev lawful {Γ : Context.{u}} (A : LawfulFamily Γ) : A.filling.Lawful := A.property

def reindex {Γ Δ : Context.{u}} (A : LawfulFamily Γ) (σ : Δ ⟶ Γ) : LawfulFamily Δ :=
  ⟨A.val.reindex σ,A.property.reindex σ⟩

@[ext] theorem ext {Γ : Context.{u}} {A B : LawfulFamily Γ} (h : A.family = B.family)
    (hF : HEq A.filling B.filling) : A = B := Subtype.ext (FamilyData.ext h hF)

noncomputable def identity {Γ : Context.{u}} (A : LawfulFamily Γ) (a b : Term A.family) : LawfulFamily Γ :=
  ⟨⟨normalizedIdentity A.family a b,normalizedIdentityFilling A.filling A.lawful a b⟩,
    normalizedIdentityFilling_lawful A.filling A.lawful a b⟩

theorem reindex_id {Γ : Context.{u}} (A : LawfulFamily Γ) : A.reindex (𝟙 Γ) = A := rfl

theorem reindex_comp {Γ Δ Θ : Context.{u}} (A : LawfulFamily Γ) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    (A.reindex σ).reindex τ = A.reindex (τ ≫ σ) := rfl

theorem identity_reindex {Γ Δ : Context.{u}} (A : LawfulFamily Γ)
    (a b : Term A.family) (σ : Δ ⟶ Γ) :
    (A.identity a b).reindex σ = (A.reindex σ).identity (a.reindex σ) (b.reindex σ) := by
  apply LawfulFamily.ext (normalizedIdentity_reindex A.family a b σ)
  have h := normalizedIdentityFilling_reindex A.filling A.lawful a b σ
  have convert_heq : ∀ {X Y : Family Δ} (e : X = Y) (G : Filling X), HEq (G.convert e) G := by
    intro X Y e G
    cases e
    rfl
  exact (convert_heq (normalizedIdentity_reindex A.family a b σ) _).symm.trans (heq_of_eq h)

end LawfulFamily
end SquareKit.Cubical.Presheaf

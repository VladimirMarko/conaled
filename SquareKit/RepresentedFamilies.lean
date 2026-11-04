import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Sigma.Basic

/-! A signature-independent presentation by representability. Comprehension
is specified by a natural hom-set equivalence, without primitive projections,
variables or pairing. There is no distinguished or terminal context. -/
namespace SquareKit
open CategoryTheory
universe u v w

/-- Strict substitution of families and their dependent sections. -/
structure IndexedFamilies (C : Type u) [Category.{v} C] where
  Ty : C → Type w
  Tm : (Γ : C) → Ty Γ → Type w
  pullTy : {Γ Δ : C} → Ty Γ → (Δ ⟶ Γ) → Ty Δ
  pullTm : {Γ Δ : C} → {A : Ty Γ} → Tm Γ A → (f : Δ ⟶ Γ) → Tm Δ (pullTy A f)
  ty_id : ∀ {Γ} (A : Ty Γ), pullTy A (𝟙 Γ) = A
  ty_comp : ∀ {Γ Δ Θ} (A : Ty Γ) (f : Δ ⟶ Γ) (g : Θ ⟶ Δ),
    pullTy (pullTy A f) g = pullTy A (g ≫ f)
  tm_id : ∀ {Γ A} (t : Tm Γ A), HEq (pullTm t (𝟙 Γ)) t
  tm_comp : ∀ {Γ Δ Θ A} (t : Tm Γ A) (f : Δ ⟶ Γ) (g : Θ ⟶ Δ),
    HEq (pullTm (pullTm t f) g) (pullTm t (g ≫ f))

namespace IndexedFamilies
variable {C : Type u} [Category.{v} C] (F : IndexedFamilies.{u,v,w} C)

abbrev Element (Δ Γ : C) (A : F.Ty Γ) := (f : Δ ⟶ Γ) × F.Tm Δ (F.pullTy A f)

def reindexElement {Γ Δ Θ} {A : F.Ty Γ} (e : F.Element Δ Γ A) (g : Θ ⟶ Δ) :
    F.Element Θ Γ A :=
  ⟨g ≫ e.1, cast (congrArg (F.Tm Θ) (F.ty_comp A e.1 g)) (F.pullTm e.2 g)⟩

/-- A choice of representing object and natural representing equivalences. -/
structure Representation where
  ext : (Γ : C) → F.Ty Γ → C
  decode : ∀ {Γ} (A : F.Ty Γ) (Δ : C), (Δ ⟶ ext Γ A) ≃ F.Element Δ Γ A
  natural : ∀ {Γ Δ Θ} (A : F.Ty Γ) (f : Δ ⟶ ext Γ A) (g : Θ ⟶ Δ),
    decode A Θ (g ≫ f) = F.reindexElement (decode A Δ f) g

namespace Representation
variable {F} (R : F.Representation)

def projection {Γ} (A : F.Ty Γ) : R.ext Γ A ⟶ Γ := (R.decode A _ (𝟙 _)).1

def generic {Γ} (A : F.Ty Γ) : F.Tm (R.ext Γ A) (F.pullTy A (R.projection A)) :=
  (R.decode A _ (𝟙 _)).2

def pair {Γ Δ} (A : F.Ty Γ) (f : Δ ⟶ Γ) (t : F.Tm Δ (F.pullTy A f)) :
    Δ ⟶ R.ext Γ A := (R.decode A Δ).symm ⟨f, t⟩

theorem decode_eq {Γ Δ} (A : F.Ty Γ) (f : Δ ⟶ R.ext Γ A) :
    R.decode A Δ f = F.reindexElement (R.decode A _ (𝟙 _)) f := by
  simpa using R.natural A (𝟙 _) f

theorem pair_projection {Γ Δ} (A : F.Ty Γ) (f : Δ ⟶ Γ) (t : F.Tm Δ (F.pullTy A f)) :
    R.pair A f t ≫ R.projection A = f := by
  have h := R.decode_eq A (R.pair A f t)
  rw [pair, Equiv.apply_symm_apply] at h
  exact (congrArg Sigma.fst h).symm

theorem pair_variable {Γ Δ} (A : F.Ty Γ) (f : Δ ⟶ Γ) (t : F.Tm Δ (F.pullTy A f)) :
    HEq (F.pullTm (R.generic A) (R.pair A f t)) t := by
  have h := R.decode_eq A (R.pair A f t)
  rw [pair, Equiv.apply_symm_apply] at h
  have ht := (Sigma.mk.inj_iff.mp h).2
  exact (cast_heq _ _).symm.trans ht.symm

theorem pair_eta {Γ Δ} (A : F.Ty Γ) (f : Δ ⟶ R.ext Γ A) :
    R.pair A (f ≫ R.projection A)
      (cast (congrArg (F.Tm Δ) (F.ty_comp A (R.projection A) f))
        (F.pullTm (R.generic A) f)) = f := by
  apply (R.decode A Δ).injective
  rw [pair, Equiv.apply_symm_apply, R.decode_eq A f]
  rfl

/-- Naturality of pairing is forced by the representing equivalence. -/
theorem pair_natural {Γ Δ Θ} (A : F.Ty Γ) (f : Δ ⟶ Γ) (t : F.Tm Δ (F.pullTy A f))
    (g : Θ ⟶ Δ) :
    g ≫ R.pair A f t = R.pair A (g ≫ f)
      (cast (congrArg (F.Tm Θ) (F.ty_comp A f g)) (F.pullTm t g)) := by
  apply (R.decode A Θ).injective
  simp only [R.natural, pair, Equiv.apply_symm_apply]
  rfl

end Representation
end IndexedFamilies
end SquareKit

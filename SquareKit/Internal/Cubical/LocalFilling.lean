import SquareKit.Internal.Cubical.Representables
import SquareKit.Internal.Cubical.Filling

/-! Filling tested only on represented contexts. The uniformity law is retained
as separate evidence; an operation alone does not certify a family. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

structure LocalFilling {Γ : Context.{u}} (A : Family Γ) where
  fill : {I : Cube} → (p : total (interval (representable.{u} I)) ⟶ Γ) →
    (φ : Cofibration (representable.{u} I)) → OpenBox (reindex A p) φ → Term (reindex A p)

structure LocalFilling.Lawful {Γ : Context.{u}} {A : Family Γ} (F : LocalFilling A) : Prop where
  fills : ∀ {I : Cube} (p : total (interval (representable.{u} I)) ⟶ Γ)
    (φ : Cofibration (representable.{u} I)) (b : OpenBox (reindex A p) φ),
    b.Fills (F.fill p φ b)
  uniform : ∀ {I J : Cube} (p : total (interval (representable.{u} I)) ⟶ Γ)
    (φ : Cofibration (representable.{u} I)) (b : OpenBox (reindex A p) φ) (f : J ⟶ I),
    F.fill (liftSub (interval (representable I)) (representableMap f) ≫ p)
      (φ.reindex (representableMap f)) (b.reindex (representableMap f)) =
      (F.fill p φ b).reindex (liftSub (interval (representable I)) (representableMap f))

def Filling.toLocal {Γ : Context.{u}} {A : Family Γ} (F : Filling A) : LocalFilling A where
  fill := F.fill

theorem Filling.toLocal_lawful {Γ : Context.{u}} {A : Family Γ} {F : Filling A}
    (h : F.Lawful) : F.toLocal.Lawful where
  fills := h.fills
  uniform p φ b f := h.uniform p φ b (representableMap f)

def LocalFilling.reindex {Γ Δ : Context.{u}} {A : Family Γ} (F : LocalFilling A)
    (σ : Δ ⟶ Γ) : LocalFilling (Presheaf.reindex A σ) where
  fill p φ b := F.fill (p ≫ σ) φ b

theorem LocalFilling.Lawful.reindex {Γ Δ : Context.{u}} {A : Family Γ}
    {F : LocalFilling A} (hF : F.Lawful) (σ : Δ ⟶ Γ) : (F.reindex σ).Lawful where
  fills p φ b := hF.fills (p ≫ σ) φ b
  uniform p φ b f := hF.uniform (p ≫ σ) φ b f

end SquareKit.Cubical.Presheaf

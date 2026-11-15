import SquareKit.Internal.Cubical.DependentFilling

/-! Uniform filling operations and their laws are separate. The discrete
instance below constructs both; arbitrary families need their own filler. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

structure Filling {Γ : Context.{u}} (A : Family Γ) where
  fill : {Δ : Context.{u}} → (p : total (interval Δ) ⟶ Γ) →
    (φ : Cofibration Δ) → OpenBox (Presheaf.reindex A p) φ → Term (Presheaf.reindex A p)

structure Filling.Lawful {Γ : Context.{u}} {A : Family Γ} (F : Filling A) : Prop where
  fills : ∀ {Δ : Context.{u}} (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (Presheaf.reindex A p) φ), b.Fills (F.fill p φ b)
  uniform : ∀ {Δ Θ : Context.{u}} (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (Presheaf.reindex A p) φ) (σ : Θ ⟶ Δ),
    F.fill (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ) =
      (F.fill p φ b).reindex (liftSub (interval Δ) σ)

def Filling.reindex {Γ Δ : Context.{u}} {A : Family Γ} (F : Filling A) (σ : Δ ⟶ Γ) :
    Filling (Presheaf.reindex A σ) where
  fill p φ b := F.fill (p ≫ σ) φ b

theorem Filling.Lawful.reindex {Γ Δ : Context.{u}} {A : Family Γ}
    {F : Filling A} (h : F.Lawful) (σ : Δ ⟶ Γ) : (F.reindex σ).Lawful where
  fills p φ b := h.fills (p ≫ σ) φ b
  uniform p φ b τ := h.uniform (p ≫ σ) φ b τ

def discreteFilling {Γ : Context.{u}} {T : Type u}
    (q : Term (constantFamily Γ T)) (S : T → Type u) : Filling (discreteFamily q S) where
  fill p _φ b := OpenBox.discreteFill (q := q.reindex p) (S := S) b

theorem discreteFilling_lawful {Γ : Context.{u}} {T : Type u}
    (q : Term (constantFamily Γ T)) (S : T → Type u) : (discreteFilling q S).Lawful where
  fills p _φ b := OpenBox.discreteFill_fills (q := q.reindex p) (S := S) b
  uniform p _φ b σ := OpenBox.discreteFill_reindex (q := q.reindex p) (S := S) b σ

/-- Composition observes the far face of the chosen filler. -/
def Filling.comp {Γ Δ : Context.{u}} {A : Family Γ} (F : Filling A)
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ) (b : OpenBox (Presheaf.reindex A p) φ) :
    Term (Presheaf.reindex A (endpointSub Δ true ≫ p)) :=
  (F.fill p φ b).reindex (endpointSub Δ true)

theorem Filling.comp_boundary {Γ Δ : Context.{u}} {A : Family Γ} {F : Filling A}
    (h : F.Lawful) (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (Presheaf.reindex A p) φ) (x : Δ.Elements) (hx : φ.full x) :
    (F.comp p φ b).val x = b.tube.val ((endpointSub Δ true).mapElements.obj x) hx :=
  (h.fills p φ b).2 ((endpointSub Δ true).mapElements.obj x) hx

theorem Filling.comp_reindex {Γ Δ Θ : Context.{u}} {A : Family Γ} {F : Filling A}
    (h : F.Lawful) (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (Presheaf.reindex A p) φ) (σ : Θ ⟶ Δ) :
    F.comp (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ) =
      (F.comp p φ b).reindex σ :=
  congrArg (fun t => t.reindex (endpointSub Θ true)) (h.uniform p φ b σ)

/-- Homogeneous composition keeps the ambient type fixed along the interval. -/
def Filling.hcomp {Γ : Context.{u}} {A : Family Γ} (F : Filling A)
    (φ : Cofibration Γ) (b : OpenBox (Presheaf.reindex A (projection (interval Γ))) φ) : Term A :=
  F.comp (projection (interval Γ)) φ b

theorem Filling.hcomp_boundary {Γ : Context.{u}} {A : Family Γ} {F : Filling A}
    (h : F.Lawful) (φ : Cofibration Γ)
    (b : OpenBox (Presheaf.reindex A (projection (interval Γ))) φ) (x : Γ.Elements) (hx : φ.full x) :
    (F.hcomp φ b).val x = b.tube.val ((endpointSub Γ true).mapElements.obj x) hx :=
  Filling.comp_boundary h (projection (interval Γ)) φ b x hx

theorem Filling.hcomp_reindex {Γ Δ : Context.{u}} {A : Family Γ} {F : Filling A}
    (h : F.Lawful) (φ : Cofibration Γ)
    (b : OpenBox (Presheaf.reindex A (projection (interval Γ))) φ) (σ : Δ ⟶ Γ) :
    (F.reindex σ).hcomp (φ.reindex σ) (b.reindex σ) = (F.hcomp φ b).reindex σ :=
  Filling.comp_reindex h (projection (interval Γ)) φ b σ

end SquareKit.Cubical.Presheaf

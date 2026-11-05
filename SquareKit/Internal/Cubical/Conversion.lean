import SquareKit.Internal.Cubical.NormalizedProducts

/-! Conversion transports sections along literal equality of semantic families. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def Term.convert {Γ : Context.{u}} {A B : Family Γ} (h : A = B) (t : Term A) : Term B := h ▸ t

theorem Term.convert_refl {Γ : Context.{u}} {A : Family Γ} (t : Term A) :
    t.convert rfl = t := rfl

theorem Term.convert_trans {Γ : Context.{u}} {A B C : Family Γ}
    (h : A = B) (k : B = C) (t : Term A) :
    (t.convert h).convert k = t.convert (h.trans k) := by
  cases h
  cases k
  rfl

theorem Term.convert_independent {Γ : Context.{u}} {A B : Family Γ}
    (h k : A = B) (t : Term A) : t.convert h = t.convert k := rfl

theorem Term.convert_reindex {Γ Δ : Context.{u}} {A B : Family Γ}
    (h : A = B) (t : Term A) (σ : Δ ⟶ Γ) :
    (t.convert h).reindex σ = (t.reindex σ).convert (congrArg (fun A : Family Γ => Presheaf.reindex A σ) h) := by
  cases h
  rfl

theorem Term.hext {Γ : Context.{u}} {A B : Family Γ} (h : A = B)
    (s : Term A) (t : Term B) (hv : ∀ x, HEq (s.val x) (t.val x)) : HEq s t := by
  cases h
  apply heq_of_eq
  apply Term.ext
  intro x
  exact eq_of_heq (hv x)

theorem Term.convert_eq {Γ : Context.{u}} {A B : Family Γ} (h : A = B)
    (s : Term A) (t : Term B) (hst : HEq s t) : s.convert h = t := by
  cases h
  exact eq_of_heq hst

def normalizedLam {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (b : Term B) : Term (normalizedPi A B) := Term.map (normalizedPiIso A B).hom (lam b)

def normalizedApp {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (p : Term (normalizedPi A B)) : Term B := app (Term.map (normalizedPiIso A B).inv p)

theorem normalizedLam_reindex {Γ Δ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (b : Term B) (σ : Δ ⟶ Γ) :
    ((normalizedLam b).reindex σ).convert (normalizedPi_reindex A B σ) =
      normalizedLam (b.reindex (liftSub A σ)) := by
  apply Term.convert_eq
  apply Term.hext (normalizedPi_reindex A B σ)
  intro x
  exact (toLocal_substitution A B σ x ((lam b).val (σ.mapElements.obj x))).symm

theorem normalizedApp_lam {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (b : Term B) : normalizedApp (normalizedLam b) = b := by
  have h : Term.map (normalizedPiIso A B).inv (Term.map (normalizedPiIso A B).hom (lam b)) = lam b :=
    Term.map_iso_roundtrip (normalizedPiIso A B) (lam b)
  exact (congrArg app h).trans (app_lam b)

theorem normalizedLam_app {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (p : Term (normalizedPi A B)) : normalizedLam (normalizedApp p) = p := by
  have h := lam_app (Term.map (normalizedPiIso A B).inv p)
  apply Term.ext
  intro x
  exact (congrArg (fun t : Term (pi A B) => (t.val x).toLocal) h).trans
    ((p.val x).toLocal_fromLocal)

theorem normalizedApp_reindex {Γ Δ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (p : Term (normalizedPi A B)) (σ : Δ ⟶ Γ) :
    normalizedApp ((p.reindex σ).convert (normalizedPi_reindex A B σ)) =
      (normalizedApp p).reindex (liftSub A σ) := by
  have h := congrArg (fun q : Term (normalizedPi A B) =>
    normalizedApp ((q.reindex σ).convert (normalizedPi_reindex A B σ))) (normalizedLam_app p)
  exact h.symm.trans ((congrArg normalizedApp
    (normalizedLam_reindex (normalizedApp p) σ)).trans
      (normalizedApp_lam ((normalizedApp p).reindex (liftSub A σ))))

end SquareKit.Cubical.Presheaf

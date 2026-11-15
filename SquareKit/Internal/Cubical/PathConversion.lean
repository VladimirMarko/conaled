import SquareKit.Internal.Cubical.NormalizedPaths

/-! Path introduction, elimination, and literal conversion under substitution. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

variable {Γ : Context.{u}} {B : Family (total (interval Γ))}
  {a₀ : Term (reindex B (endpointSub Γ false))}
  {a₁ : Term (reindex B (endpointSub Γ true))}

def normalizedPathLam (b : Term B) (h₀ : b.reindex (endpointSub Γ false) = a₀)
    (h₁ : b.reindex (endpointSub Γ true) = a₁) : Term (normalizedPath B a₀ a₁) :=
  Term.map (normalizedPathIso B a₀ a₁).hom (pathLam b h₀ h₁)

def normalizedPathApp (p : Term (normalizedPath B a₀ a₁)) : Term B :=
  pathApp (Term.map (normalizedPathIso B a₀ a₁).inv p)

theorem normalizedPathApp_lam (b : Term B) (h₀ : b.reindex (endpointSub Γ false) = a₀)
    (h₁ : b.reindex (endpointSub Γ true) = a₁) :
    normalizedPathApp (normalizedPathLam b h₀ h₁) = b := by
  exact (congrArg pathApp
    (Term.map_iso_roundtrip (normalizedPathIso B a₀ a₁) (pathLam b h₀ h₁))).trans
      (pathApp_lam b h₀ h₁)

theorem normalizedPathApp_zero (p : Term (normalizedPath B a₀ a₁)) :
    (normalizedPathApp p).reindex (endpointSub Γ false) = a₀ :=
  pathApp_zero (Term.map (normalizedPathIso B a₀ a₁).inv p)

theorem normalizedPathApp_one (p : Term (normalizedPath B a₀ a₁)) :
    (normalizedPathApp p).reindex (endpointSub Γ true) = a₁ :=
  pathApp_one (Term.map (normalizedPathIso B a₀ a₁).inv p)

theorem normalizedPathLam_app (p : Term (normalizedPath B a₀ a₁)) :
    normalizedPathLam (normalizedPathApp p) (normalizedPathApp_zero p) (normalizedPathApp_one p) = p := by
  have h := pathLam_app (Term.map (normalizedPathIso B a₀ a₁).inv p)
  apply Term.ext
  intro x
  exact (congrArg (fun t : Term (path B a₀ a₁) => (t.val x).toLocal) h).trans
    ((p.val x).toLocal_fromLocal)

theorem normalizedPathLam_reindex {Δ : Context.{u}} (b : Term B)
    (h₀ : b.reindex (endpointSub Γ false) = a₀)
    (h₁ : b.reindex (endpointSub Γ true) = a₁) (σ : Δ ⟶ Γ) :
    ((normalizedPathLam b h₀ h₁).reindex σ).convert (normalizedPath_reindex B a₀ a₁ σ) =
      normalizedPathLam (b.reindex (liftSub (interval Γ) σ))
        (congrArg (fun t => Term.reindex t σ) h₀)
        (congrArg (fun t => Term.reindex t σ) h₁) := by
  apply Term.convert_eq
  apply Term.hext (normalizedPath_reindex B a₀ a₁ σ)
  intro x
  exact pathToLocal_substitution B a₀ a₁ σ x ((pathLam b h₀ h₁).val (σ.mapElements.obj x))

theorem normalizedPathApp_reindex {Δ : Context.{u}}
    (p : Term (normalizedPath B a₀ a₁)) (σ : Δ ⟶ Γ) :
    normalizedPathApp ((p.reindex σ).convert (normalizedPath_reindex B a₀ a₁ σ)) =
      (normalizedPathApp p).reindex (liftSub (interval Γ) σ) := by
  have h := congrArg (fun q : Term (normalizedPath B a₀ a₁) =>
    normalizedPathApp ((q.reindex σ).convert (normalizedPath_reindex B a₀ a₁ σ)))
      (normalizedPathLam_app p)
  exact h.symm.trans ((congrArg normalizedPathApp
    (normalizedPathLam_reindex (normalizedPathApp p)
      (normalizedPathApp_zero p) (normalizedPathApp_one p) σ)).trans
        (normalizedPathApp_lam _ _ _))

end SquareKit.Cubical.Presheaf

import SquareKit.Internal.Cubical.DependentFaces
import SquareKit.Internal.Cubical.IdentitySubstitution
import SquareKit.Internal.Cubical.FillingTransport
import SquareKit.Internal.Cubical.PathFilling
import SquareKit.Internal.Cubical.CompositionFilling

/-! Compose the underlying path and retain the endpoint constancy face on the
original tube. Dependent face composition makes this choice natural. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u
namespace IdentityComposition
variable {Γ Δ : Context.{u}} {A : Family Γ} {a₀ a₁ : Term A}

abbrev paths := Presheaf.path (reindex A (projection (interval Γ))) a₀ a₁

def pathBox (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (identity A a₀ a₁) p) φ) : OpenBox (reindex (paths (A := A) (a₀ := a₀) (a₁ := a₁)) p) φ :=
  b.map (Functor.whiskerLeft p.mapElements (identityPath A a₀ a₁))

def endpointIdentity (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (identity A a₀ a₁) p) φ) :
    Term (identity (reindex A (restrictInclusion φ ≫ endpointSub Δ true ≫ p))
      (a₀.reindex (restrictInclusion φ ≫ endpointSub Δ true ≫ p))
      (a₁.reindex (restrictInclusion φ ≫ endpointSub Δ true ≫ p))) :=
  Term.map (identityReindex A a₀ a₁ (restrictInclusion φ ≫ endpointSub Δ true ≫ p))
    (b.tube.reindex (endpointSub Δ true)).toRestricted

def endpointFace (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (identity A a₀ a₁) p) φ) : Cofibration (restrictContext φ) :=
  identityFace (endpointIdentity p φ b)

def resultFace (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (identity A a₀ a₁) p) φ) : Cofibration Δ :=
  φ.dependent (endpointFace p φ b)

def normalizePath (p : total (interval Δ) ⟶ Γ)
    (r : Term (reindex (paths (A := A) (a₀ := a₀) (a₁ := a₁)) (endpointSub Δ true ≫ p))) :
    Term (Presheaf.path (reindex (reindex A (endpointSub Δ true ≫ p)) (projection (interval Δ)))
      (a₀.reindex (endpointSub Δ true ≫ p)) (a₁.reindex (endpointSub Δ true ≫ p))) :=
  Term.map (pathReindex (reindex A (projection (interval Γ))) a₀ a₁ (endpointSub Δ true ≫ p)) r

theorem result_constant (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (identity A a₀ a₁) p) φ)
    (r : Term (reindex (paths (A := A) (a₀ := a₀) (a₁ := a₁)) (endpointSub Δ true ≫ p)))
    (hr : ∀ x hx, r.val x = (pathBox p φ b).tube.val ((endpointSub Δ true).mapElements.obj x) hx)
    (x : Δ.Elements) (hx : (resultFace p φ b).full x) (i : (interval Δ).obj x) :
    ((normalizePath p r).val x).val.val (𝟙 _) i = (a₀.reindex (endpointSub Δ true ≫ p)).val x := by
  obtain ⟨hφ,hψ⟩ := (Cofibration.dependent_full φ (endpointFace p φ b) x).mp hx
  have hp := congrArg (fun q : PathElement (reindex A (projection (interval Γ))) a₀ a₁
      ((endpointSub Δ true ≫ p).mapElements.obj x) => q.val.val (𝟙 _) i) (hr x hφ)
  exact hp.trans ((b.tube.val ((endpointSub Δ true).mapElements.obj x) hφ).constant (𝟙 _) hψ i)

def result (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (identity A a₀ a₁) p) φ)
    (r : Term (reindex (paths (A := A) (a₀ := a₀) (a₁ := a₁)) (endpointSub Δ true ≫ p)))
    (hr : ∀ x hx, r.val x = (pathBox p φ b).tube.val ((endpointSub Δ true).mapElements.obj x) hx) :
    Term (reindex (identity A a₀ a₁) (endpointSub Δ true ≫ p)) :=
  Term.map (identityReindexIso A a₀ a₁ (endpointSub Δ true ≫ p)).inv
    (identityIntro (normalizePath p r) (resultFace p φ b) (result_constant p φ b r hr))

theorem result_path (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (identity A a₀ a₁) p) φ)
    (r : Term (reindex (paths (A := A) (a₀ := a₀) (a₁ := a₁)) (endpointSub Δ true ≫ p)))
    (hr : ∀ x hx, r.val x = (pathBox p φ b).tube.val ((endpointSub Δ true).mapElements.obj x) hx) :
    Term.map (Functor.whiskerLeft (endpointSub Δ true ≫ p).mapElements (identityPath A a₀ a₁))
      (result p φ b r hr) = r := by
  apply Term.ext
  intro x
  apply Subtype.ext
  exact piInverse_reindex (endpointSub Δ true ≫ p) (r.val x).val

theorem result_face (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (identity A a₀ a₁) p) φ)
    (r : Term (reindex (paths (A := A) (a₀ := a₀) (a₁ := a₁)) (endpointSub Δ true ≫ p)))
    (hr : ∀ x hx, r.val x = (pathBox p φ b).tube.val ((endpointSub Δ true).mapElements.obj x) hx)
    (x : Δ.Elements) : ((result p φ b r hr).val x).face = ((resultFace p φ b).app x.obj x.val).down := rfl


def composition (G : Composition (paths (A := A) (a₀ := a₀) (a₁ := a₁)))
    (hG : G.Lawful) : Composition (identity A a₀ a₁) where
  comp p φ b := result p φ b (G.comp p φ (pathBox p φ b)) (hG.boundary p φ (pathBox p φ b))

theorem composition_boundary (G : Composition (paths (A := A) (a₀ := a₀) (a₁ := a₁)))
    (hG : G.Lawful) (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (identity A a₀ a₁) p) φ) (x : Δ.Elements) (hx : φ.full x) :
    ((composition G hG).comp p φ b).val x = b.tube.val ((endpointSub Δ true).mapElements.obj x) hx := by
  apply IdentityElement.ext
  · have h := congrArg (fun t => t.val x) (result_path p φ b (G.comp p φ (pathBox p φ b))
      (hG.boundary p φ (pathBox p φ b)))
    exact h.trans (hG.boundary p φ (pathBox p φ b) x hx)
  · exact congrArg (fun χ : Cofibration (restrictContext φ) => (χ.app x.obj ⟨x.val,hx⟩).down)
      (Cofibration.dependent_restrict φ (endpointFace p φ b))

theorem resultFace_reindex {Θ : Context.{u}} (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (identity A a₀ a₁) p) φ) (σ : Θ ⟶ Δ) :
    resultFace (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ) =
      (resultFace p φ b).reindex σ :=
  (Cofibration.dependent_reindex φ (endpointFace p φ b) σ).symm

theorem composition_uniform (G : Composition (paths (A := A) (a₀ := a₀) (a₁ := a₁)))
    (hG : G.Lawful) {Θ : Context.{u}} (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (identity A a₀ a₁) p) φ) (σ : Θ ⟶ Δ) :
    (composition G hG).comp (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ) =
      ((composition G hG).comp p φ b).reindex σ := by
  apply Term.ext
  intro x
  apply IdentityElement.ext
  · have h₁ := congrArg (fun t => t.val x)
      (result_path (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ)
        (G.comp (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (pathBox (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ)))
        (hG.boundary (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (pathBox (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ))))
    have h₂ := congrArg (fun t => t.val (σ.mapElements.obj x))
      (result_path p φ b (G.comp p φ (pathBox p φ b)) (hG.boundary p φ (pathBox p φ b)))
    exact h₁.trans ((congrArg (fun t => t.val x) (hG.uniform p φ (pathBox p φ b) σ)).trans h₂.symm)
  · exact congrArg (fun χ : Cofibration Θ => (χ.app x.obj x.val).down) (resultFace_reindex p φ b σ)

theorem composition_lawful (G : Composition (paths (A := A) (a₀ := a₀) (a₁ := a₁)))
    (hG : G.Lawful) : (composition G hG).Lawful where
  boundary := composition_boundary G hG
  uniform := composition_uniform G hG

end IdentityComposition
end SquareKit.Cubical.Presheaf

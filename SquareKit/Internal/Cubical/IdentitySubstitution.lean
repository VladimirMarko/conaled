import SquareKit.Internal.Cubical.Identity
import SquareKit.Internal.Cubical.Substitution

/-! Identity substitution retains the chosen constancy face as well as the path. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def identityReindex {Γ Δ : Context.{u}} (A : Family Γ) (a b : Term A) (σ : Δ ⟶ Γ) :
    reindex (identity A a b) σ ⟶ identity (reindex A σ) (a.reindex σ) (b.reindex σ) where
  app x := TypeCat.ofHom (fun p => {
    path := (pathReindex (reindex A (projection (interval Γ))) a b σ).app x p.path
    face := p.face
    constant f hf r := p.constant (σ.mapElements.map f) hf r })
  naturality _ _ _ := rfl

def identityReindexInv {Γ Δ : Context.{u}} (A : Family Γ) (a b : Term A) (σ : Δ ⟶ Γ) :
    identity (reindex A σ) (a.reindex σ) (b.reindex σ) ⟶ reindex (identity A a b) σ where
  app x := TypeCat.ofHom (fun p => {
    path := (pathReindexInv (reindex A (projection (interval Γ))) a b σ).app x p.path
    face := p.face
    constant := by
      intro y f hf r
      obtain ⟨⟨y',f'⟩,he⟩ := (substitutionArrowEquiv σ x).surjective ⟨y,f⟩
      change (⟨σ.mapElements.obj y', σ.mapElements.map f'⟩ :
        Σ y, σ.mapElements.obj x ⟶ y) = ⟨y,f⟩ at he
      cases he
      exact (piInverseValue_map (A := interval Γ) (B := reindex A (projection (interval Γ)))
        σ p.path.val f' r).trans (p.constant f' hf r) })
  naturality x y f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply IdentityElement.ext
    · exact congrArg (fun h => h p.path)
        ((pathReindexInv (reindex A (projection (interval Γ))) a b σ).naturality f)
    · rfl

def identityReindexIso {Γ Δ : Context.{u}} (A : Family Γ) (a b : Term A) (σ : Δ ⟶ Γ) :
    reindex (identity A a b) σ ≅ identity (reindex A σ) (a.reindex σ) (b.reindex σ) where
  hom := identityReindex A a b σ
  inv := identityReindexInv A a b σ
  hom_inv_id := by
    ext x p
    apply IdentityElement.ext
    · exact congrArg (fun h => h.app x p.path)
        (pathReindexIso (reindex A (projection (interval Γ))) a b σ).hom_inv_id
    · rfl
  inv_hom_id := by
    ext x p
    apply IdentityElement.ext
    · exact congrArg (fun h => h.app x p.path)
        (pathReindexIso (reindex A (projection (interval Γ))) a b σ).inv_hom_id
    · rfl

theorem identityRefl_reindex {Γ Δ : Context.{u}} (A : Family Γ) (a : Term A) (σ : Δ ⟶ Γ) :
    Term.map (identityReindex A a a σ) ((identityRefl a).reindex σ) = identityRefl (a.reindex σ) := rfl

theorem identityFace_reindex {Γ Δ : Context.{u}} (A : Family Γ) (a b : Term A)
    (p : Term (identity A a b)) (σ : Δ ⟶ Γ) :
    identityFace (Term.map (identityReindex A a b σ) (p.reindex σ)) = (identityFace p).reindex σ := rfl

end SquareKit.Cubical.Presheaf

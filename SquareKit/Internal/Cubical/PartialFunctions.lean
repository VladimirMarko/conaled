import SquareKit.Internal.Cubical.PartialPaths
import SquareKit.Internal.Cubical.Substitution

/-! Application of partial dependent functions on their actual support. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def restrictedComprehension {Γ : Context.{u}} (A : Family Γ) (φ : Cofibration Γ) :
    restrictContext (φ.reindex (projection A)) ⟶ total (reindex A (restrictInclusion φ)) where
  app _ := TypeCat.ofHom (fun z => ⟨⟨z.val.1,z.property⟩,z.val.2⟩)
  naturality _ _ _ := rfl

def PartialSection.app {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {φ : Cofibration Γ} (s : PartialSection (pi A B) φ) :
    PartialSection B (φ.reindex (projection A)) :=
  PartialSection.ofRestricted
    ((Presheaf.app (Term.map (piReindex A B (restrictInclusion φ)) s.toRestricted)).reindex
      (restrictedComprehension A φ))

theorem PartialSection.app_val {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {φ : Cofibration Γ} (s : PartialSection (pi A B) φ) (x : (total A).Elements)
    (h : (φ.reindex (projection A)).full x) :
    s.app.val x h = (s.val ((projection A).mapElements.obj x) h).val (𝟙 _) x.val.2 := rfl

theorem PartialSection.app_reindex {Γ Δ : Context.{u}} {A : Family Γ}
    {B : Family (total A)} {φ : Cofibration Γ} (s : PartialSection (pi A B) φ)
    (σ : Δ ⟶ Γ) :
    ((s.reindex σ).map (piReindex A B σ)).app = s.app.reindex (liftSub A σ) := rfl

end SquareKit.Cubical.Presheaf

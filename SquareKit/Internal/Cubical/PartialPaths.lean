import SquareKit.Internal.Cubical.IntervalSquare
import SquareKit.Internal.Cubical.Paths

/-! Evaluate partial paths and retain their fixed endpoint sections. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def restrictedInterval {Γ : Context.{u}} (φ : Cofibration Γ) :
    restrictContext (φ.reindex (projection (interval Γ))) ⟶ total (interval (restrictContext φ)) where
  app _ := TypeCat.ofHom (fun z => ⟨⟨z.val.1,z.property⟩,z.val.2⟩)
  naturality _ _ _ := rfl

def PartialSection.map {Γ : Context.{u}} {A B : Family Γ} {φ : Cofibration Γ}
    (η : A ⟶ B) (s : PartialSection A φ) : PartialSection B φ where
  val x h := η.app x (s.val x h)
  property f h := by rw [← η.naturality_apply, s.property f h]

def PartialSection.pathApp {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (Presheaf.reindex B (endpointSub Γ false))}
    {a₁ : Term (Presheaf.reindex B (endpointSub Γ true))} {φ : Cofibration Γ}
    (s : PartialSection (path B a₀ a₁) φ) :
    PartialSection B (φ.reindex (projection (interval Γ))) :=
  PartialSection.ofRestricted
    ((Presheaf.pathApp (Term.map (pathReindex B a₀ a₁ (restrictInclusion φ)) s.toRestricted)).reindex
      (restrictedInterval φ))

theorem PartialSection.pathApp_val {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (Presheaf.reindex B (endpointSub Γ false))}
    {a₁ : Term (Presheaf.reindex B (endpointSub Γ true))} {φ : Cofibration Γ}
    (s : PartialSection (path B a₀ a₁) φ) (x : (total (interval Γ)).Elements)
    (h : (φ.reindex (projection (interval Γ))).full x) :
    s.pathApp.val x h =
      (s.val ((projection (interval Γ)).mapElements.obj x) h).val.val (𝟙 _) x.val.2 := rfl

theorem PartialSection.pathApp_reindex {Γ Δ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (Presheaf.reindex B (endpointSub Γ false))}
    {a₁ : Term (Presheaf.reindex B (endpointSub Γ true))} {φ : Cofibration Γ}
    (s : PartialSection (path B a₀ a₁) φ) (σ : Δ ⟶ Γ) :
    ((s.reindex σ).map (pathReindex B a₀ a₁ σ)).pathApp =
      s.pathApp.reindex (liftSub (interval Γ) σ) := rfl

theorem PartialSection.pathApp_zero {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (Presheaf.reindex B (endpointSub Γ false))}
    {a₁ : Term (Presheaf.reindex B (endpointSub Γ true))} {φ : Cofibration Γ}
    (s : PartialSection (path B a₀ a₁) φ) (x : (total (interval Γ)).Elements)
    (h : (φ.reindex (projection (interval Γ))).full x) (h₀ : (intervalFace Γ false).full x) :
    HEq (s.pathApp.val x h) (a₀.val ((projection (interval Γ)).mapElements.obj x)) := by
  rcases x with @⟨I,⟨γ,r⟩⟩
  have hr := (Cofibration.full_endpoint (generic (interval Γ)) false
    ((total (interval Γ)).elementsMk I ⟨γ,r⟩)).mp h₀
  change r = (endpoint Γ false).val (Γ.elementsMk I γ) at hr
  subst r
  exact heq_of_eq ((s.val (Γ.elementsMk I γ) h).property (𝟙 _)).1

theorem PartialSection.pathApp_one {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (Presheaf.reindex B (endpointSub Γ false))}
    {a₁ : Term (Presheaf.reindex B (endpointSub Γ true))} {φ : Cofibration Γ}
    (s : PartialSection (path B a₀ a₁) φ) (x : (total (interval Γ)).Elements)
    (h : (φ.reindex (projection (interval Γ))).full x) (h₁ : (intervalFace Γ true).full x) :
    HEq (s.pathApp.val x h) (a₁.val ((projection (interval Γ)).mapElements.obj x)) := by
  rcases x with @⟨I,⟨γ,r⟩⟩
  have hr := (Cofibration.full_endpoint (generic (interval Γ)) true
    ((total (interval Γ)).elementsMk I ⟨γ,r⟩)).mp h₁
  change r = (endpoint Γ true).val (Γ.elementsMk I γ) at hr
  subst r
  exact heq_of_eq ((s.val (Γ.elementsMk I γ) h).property (𝟙 _)).2

end SquareKit.Cubical.Presheaf

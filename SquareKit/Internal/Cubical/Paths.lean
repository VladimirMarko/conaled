import SquareKit.Internal.Cubical.Interval

/-! Dependent paths as sections over the represented interval with prescribed
endpoints. No filling, transport or identity-elimination principle is assumed. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

abbrev PathElement {Γ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) (x : Γ.Elements) :=
  { p : PiElement (interval Γ) B x // ∀ {y} (f : x ⟶ y),
    p.val f ((endpoint Γ false).val y) = a₀.val y ∧
    p.val f ((endpoint Γ true).val y) = a₁.val y }

def path {Γ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) : Family Γ where
  obj x := PathElement B a₀ a₁ x
  map f := TypeCat.ofHom (fun p => ⟨p.val.restrict f, fun g => p.property (f ≫ g)⟩)
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    apply PiElement.ext
    intro y f a
    simp [PiElement.restrict]
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    apply PiElement.ext
    intro y h a
    simp [PiElement.restrict]

def pathInclusion {Γ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) : path B a₀ a₁ ⟶ pi (interval Γ) B where
  app _ := TypeCat.ofHom Subtype.val
  naturality _ _ _ := rfl

def pathLam {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ : Term (reindex B (endpointSub Γ true))}
    (b : Term B) (h₀ : Term.reindex b (endpointSub Γ false) = a₀)
    (h₁ : Term.reindex b (endpointSub Γ true) = a₁) : Term (path B a₀ a₁) where
  val x := ⟨(lam b).val x, fun {y} _ =>
    ⟨congrArg (fun t : Term (reindex B (endpointSub Γ false)) => t.val y) h₀,
      congrArg (fun t : Term (reindex B (endpointSub Γ true)) => t.val y) h₁⟩⟩
  property _ := rfl

def pathApp {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ : Term (reindex B (endpointSub Γ true))} (p : Term (path B a₀ a₁)) : Term B :=
  app (Term.map (pathInclusion B a₀ a₁) p)

@[simp] theorem pathApp_lam {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ : Term (reindex B (endpointSub Γ true))}
    (b : Term B) (h₀ : Term.reindex b (endpointSub Γ false) = a₀)
    (h₁ : Term.reindex b (endpointSub Γ true) = a₁) : pathApp (pathLam b h₀ h₁) = b := rfl

theorem pathApp_zero {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ : Term (reindex B (endpointSub Γ true))} (p : Term (path B a₀ a₁)) :
    Term.reindex (pathApp p) (endpointSub Γ false) = a₀ := by
  apply Term.ext
  intro x
  exact ((p.val x).property (𝟙 x)).1

theorem pathApp_one {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ : Term (reindex B (endpointSub Γ true))} (p : Term (path B a₀ a₁)) :
    Term.reindex (pathApp p) (endpointSub Γ true) = a₁ := by
  apply Term.ext
  intro x
  exact ((p.val x).property (𝟙 x)).2

theorem pathLam_app {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ : Term (reindex B (endpointSub Γ true))} (p : Term (path B a₀ a₁)) :
    pathLam (pathApp p) (pathApp_zero p) (pathApp_one p) = p := by
  apply Term.ext
  intro x
  apply Subtype.ext
  have h := congrArg (fun t : Term (pi (interval Γ) B) => t.val x)
    (lam_app (Term.map (pathInclusion B a₀ a₁) p))
  exact h

def pathReindex {Γ Δ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) (σ : Δ ⟶ Γ) :
    reindex (path B a₀ a₁) σ ⟶
      path (reindex B (liftSub (interval Γ) σ)) (Term.reindex a₀ σ) (Term.reindex a₁ σ) where
  app x := TypeCat.ofHom (fun p => ⟨(piReindex (interval Γ) B σ).app x p.val,
    fun f => p.property (σ.mapElements.map f)⟩)
  naturality _ _ _ := rfl

theorem pathLam_reindex {Γ Δ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ : Term (reindex B (endpointSub Γ true))}
    (b : Term B) (h₀ : Term.reindex b (endpointSub Γ false) = a₀)
    (h₁ : Term.reindex b (endpointSub Γ true) = a₁) (σ : Δ ⟶ Γ) :
    Term.map (pathReindex B a₀ a₁ σ) (Term.reindex (pathLam b h₀ h₁) σ) =
      pathLam (Term.reindex b (liftSub (interval Γ) σ))
        (congrArg (fun t => Term.reindex t σ) h₀)
        (congrArg (fun t => Term.reindex t σ) h₁) := rfl

end SquareKit.Cubical.Presheaf

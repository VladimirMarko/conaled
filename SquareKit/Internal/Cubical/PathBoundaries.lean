import SquareKit.Internal.Cubical.PartialPaths

/-! Compatible path systems include both endpoint faces throughout filling. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

noncomputable def endpointBoundary {Γ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) :
    PartialSection B ((intervalFace Γ false).join (intervalFace Γ true)) :=
  (endpointSection B false a₀).glue (endpointSection B true a₁)
    (fun x h₀ h₁ => (intervalFace_disjoint x h₀ h₁).elim)

theorem endpointBoundary_zero {Γ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) (x : (total (interval Γ)).Elements)
    (h : ((intervalFace Γ false).join (intervalFace Γ true)).full x)
    (h₀ : (intervalFace Γ false).full x) :
    (endpointBoundary B a₀ a₁).val x h = (endpointSection B false a₀).val x h₀ :=
  glueValue_left _ _ x h h₀

theorem endpointBoundary_one {Γ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) (x : (total (interval Γ)).Elements)
    (h : ((intervalFace Γ false).join (intervalFace Γ true)).full x)
    (h₁ : (intervalFace Γ true).full x) :
    (endpointBoundary B a₀ a₁).val x h = (endpointSection B true a₁).val x h₁ :=
  glueValue_right _ _ (fun x h₀ h₁ => (intervalFace_disjoint x h₀ h₁).elim) x h h₁

def pathBoundaryFace {Γ : Context.{u}} (φ : Cofibration Γ) : Cofibration (total (interval Γ)) :=
  (φ.reindex (projection (interval Γ))).join ((intervalFace Γ false).join (intervalFace Γ true))

theorem PartialSection.pathApp_boundary_compatible {Γ : Context.{u}}
    {B : Family (total (interval Γ))}
    {a₀ : Term (Presheaf.reindex B (endpointSub Γ false))}
    {a₁ : Term (Presheaf.reindex B (endpointSub Γ true))} {φ : Cofibration Γ}
    (s : PartialSection (path B a₀ a₁) φ) : s.pathApp.Compatible (endpointBoundary B a₀ a₁) := by
  intro x h p
  rcases (Cofibration.full_join _ _ x).mp p with h₀ | h₁
  · rw [endpointBoundary_zero B a₀ a₁ x p h₀]
    exact eq_of_heq ((s.pathApp_zero x h h₀).trans (endpointSection_val B false a₀ x h₀).symm)
  · rw [endpointBoundary_one B a₀ a₁ x p h₁]
    exact eq_of_heq ((s.pathApp_one x h h₁).trans (endpointSection_val B true a₁ x h₁).symm)

noncomputable def PartialSection.pathBoundary {Γ : Context.{u}}
    {B : Family (total (interval Γ))}
    {a₀ : Term (Presheaf.reindex B (endpointSub Γ false))}
    {a₁ : Term (Presheaf.reindex B (endpointSub Γ true))} {φ : Cofibration Γ}
    (s : PartialSection (path B a₀ a₁) φ) : PartialSection B (pathBoundaryFace φ) :=
  s.pathApp.glue (endpointBoundary B a₀ a₁) s.pathApp_boundary_compatible

theorem PartialSection.pathBoundary_old {Γ : Context.{u}}
    {B : Family (total (interval Γ))}
    {a₀ : Term (Presheaf.reindex B (endpointSub Γ false))}
    {a₁ : Term (Presheaf.reindex B (endpointSub Γ true))} {φ : Cofibration Γ}
    (s : PartialSection (path B a₀ a₁) φ) (x : (total (interval Γ)).Elements)
    (p : (pathBoundaryFace φ).full x) (h : (φ.reindex (projection (interval Γ))).full x) :
    s.pathBoundary.val x p = s.pathApp.val x h := glueValue_left _ _ x p h

theorem PartialSection.pathBoundary_zero {Γ : Context.{u}}
    {B : Family (total (interval Γ))}
    {a₀ : Term (Presheaf.reindex B (endpointSub Γ false))}
    {a₁ : Term (Presheaf.reindex B (endpointSub Γ true))} {φ : Cofibration Γ}
    (s : PartialSection (path B a₀ a₁) φ) (x : (total (interval Γ)).Elements)
    (p : (pathBoundaryFace φ).full x) (h₀ : (intervalFace Γ false).full x) :
    HEq (s.pathBoundary.val x p) (a₀.val ((projection (interval Γ)).mapElements.obj x)) := by
  have h := (Cofibration.full_join (intervalFace Γ false) (intervalFace Γ true) x).mpr (Or.inl h₀)
  exact (heq_of_eq (glueValue_right _ _ s.pathApp_boundary_compatible x p h)).trans
    ((heq_of_eq (endpointBoundary_zero B a₀ a₁ x h h₀)).trans (endpointSection_val B false a₀ x h₀))

theorem PartialSection.pathBoundary_one {Γ : Context.{u}}
    {B : Family (total (interval Γ))}
    {a₀ : Term (Presheaf.reindex B (endpointSub Γ false))}
    {a₁ : Term (Presheaf.reindex B (endpointSub Γ true))} {φ : Cofibration Γ}
    (s : PartialSection (path B a₀ a₁) φ) (x : (total (interval Γ)).Elements)
    (p : (pathBoundaryFace φ).full x) (h₁ : (intervalFace Γ true).full x) :
    HEq (s.pathBoundary.val x p) (a₁.val ((projection (interval Γ)).mapElements.obj x)) := by
  have h := (Cofibration.full_join (intervalFace Γ false) (intervalFace Γ true) x).mpr (Or.inr h₁)
  exact (heq_of_eq (glueValue_right _ _ s.pathApp_boundary_compatible x p h)).trans
    ((heq_of_eq (endpointBoundary_one B a₀ a₁ x h h₁)).trans (endpointSection_val B true a₁ x h₁))

theorem endpointBoundary_reindex {Γ Δ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) (σ : Δ ⟶ Γ) :
    (endpointBoundary B a₀ a₁).reindex (liftSub (interval Γ) σ) =
      endpointBoundary (reindex B (liftSub (interval Γ) σ)) (a₀.reindex σ) (a₁.reindex σ) := by
  exact (PartialSection.glue_reindex _ _ _ (liftSub (interval Γ) σ)).trans
    (PartialSection.glue_congr (endpointSection_reindex B false a₀ σ)
      (endpointSection_reindex B true a₁ σ) _ _)

theorem PartialSection.pathBoundary_reindex {Γ Δ : Context.{u}}
    {B : Family (total (interval Γ))}
    {a₀ : Term (Presheaf.reindex B (endpointSub Γ false))}
    {a₁ : Term (Presheaf.reindex B (endpointSub Γ true))} {φ : Cofibration Γ}
    (s : PartialSection (path B a₀ a₁) φ) (σ : Δ ⟶ Γ) :
    s.pathBoundary.reindex (liftSub (interval Γ) σ) =
      ((s.reindex σ).map (pathReindex B a₀ a₁ σ)).pathBoundary := by
  exact (PartialSection.glue_reindex _ _ _ (liftSub (interval Γ) σ)).trans
    (PartialSection.glue_congr (s.pathApp_reindex σ).symm
      (endpointBoundary_reindex B a₀ a₁ σ) _ _)

theorem pathBoundaryFace_endpoint {Γ : Context.{u}} (φ : Cofibration Γ) (b : Bool)
    (x : Γ.Elements) : (pathBoundaryFace φ).full ((endpointSub Γ b).mapElements.obj x) := by
  apply (Cofibration.full_join _ _ _).mpr
  apply Or.inr
  apply (Cofibration.full_join _ _ _).mpr
  cases b
  · exact Or.inl ((Cofibration.full_endpoint (generic (interval Γ)) false _).mpr rfl)
  · exact Or.inr ((Cofibration.full_endpoint (generic (interval Γ)) true _).mpr rfl)

end SquareKit.Cubical.Presheaf

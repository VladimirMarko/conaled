import SquareKit.Internal.PathTransport.ComparisonCompositionRelations

/-! Comprehension substitutions preserve the horizontal composition relation. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

private theorem weaken_heq {C D : Grpd.{u,u}} (h : C = D)
    {A : C ⥤ Grpd.{u,u}} {B : D ⥤ Grpd.{u,u}} (hA : HEq A B) :
    HEq (GroupoidModel.weaken A) (GroupoidModel.weaken B) := by
  cases h; cases eq_of_heq hA; rfl

theorem Family.Composes.weaken {Γ Δ Θ : Context.{u}}
    {A : Family Γ} {B : Family Δ} {C : Family Θ} (h : A.Composes B C) :
    A.weaken.Composes B.weaken C.weaken :=
  Substitution.Composes.of_endpoints h.context h.extend A.weaken B.weaken C.weaken
    (weaken_heq h.context.middle h.middle)
    (weaken_heq h.context.left h.endpoints.1) (weaken_heq h.context.right h.endpoints.2)

private theorem pre_heq {C C' D D' : Grpd.{u,u}} (hC : C = C') (hD : D = D')
    {A : C ⥤ Grpd.{u,u}} {B : C' ⥤ Grpd.{u,u}} (hA : HEq A B)
    {F : D ⥤ C} {G : D' ⥤ C'} (hF : HEq F G) :
    HEq (Grothendieck.pre (A ⋙ Grpd.forgetToCat) F)
      (Grothendieck.pre (B ⋙ Grpd.forgetToCat) G) := by
  cases hC; cases hD; cases eq_of_heq hA; cases eq_of_heq hF; rfl

theorem Family.Composes.lift {Γ₀ Γ₁ Γ₂ Δ₀ Δ₁ Δ₂ : Context.{u}}
    {A : Family Γ₀} {B : Family Γ₁} {C : Family Γ₂}
    {σ : Substitution Δ₀ Γ₀} {τ : Substitution Δ₁ Γ₁} {ρ : Substitution Δ₂ Γ₂}
    (hA : A.Composes B C) (hσ : σ.Composes τ ρ) :
    (A.lift σ).Composes (B.lift τ) (C.lift ρ) :=
  Substitution.Composes.of_endpoints hA.extend (hA.reindex hσ).extend
    (A.lift σ) (B.lift τ) (C.lift ρ)
    (pre_heq hA.context.middle hσ.source.middle hA.middle hσ.middle)
    (pre_heq hA.context.left hσ.source.left hA.endpoints.1 hσ.endpoints.1)
    (pre_heq hA.context.right hσ.source.right hA.endpoints.2 hσ.endpoints.2)

private theorem variable_heq {C D : Grpd.{u,u}} (h : C = D)
    {A : C ⥤ Grpd.{u,u}} {B : D ⥤ Grpd.{u,u}} (hA : HEq A B) :
    HEq (GroupoidModel.«variable» A) (GroupoidModel.«variable» B) := by
  cases h; cases eq_of_heq hA; rfl

theorem Family.Composes.variable {Γ Δ Θ : Context.{u}}
    {A : Family Γ} {B : Family Δ} {C : Family Θ} (h : A.Composes B C) :
    A.variable.Composes B.variable C.variable :=
  Section.Composes.of_endpoints (h.reindex h.weaken) A.variable B.variable C.variable
    (variable_heq h.context.middle h.middle)
    (variable_heq h.context.left h.endpoints.1) (variable_heq h.context.right h.endpoints.2)

private theorem section_endpoints_heq {Γ Δ : Context.{u}} (hΓ : Γ = Δ)
    {A : Family Γ} {B : Family Δ} (hA : HEq A B) {s : Section A} {t : Section B}
    (hs : HEq s t) : HEq s.left t.left ∧ HEq s.right t.right := by
  cases hΓ; cases eq_of_heq hA; cases eq_of_heq hs
  exact ⟨HEq.rfl, HEq.rfl⟩

theorem Section.Composes.endpoints {Γ Δ Θ : Context.{u}}
    {A : Family Γ} {B : Family Δ} {C : Family Θ}
    {s : Section A} {t : Section B} {v : Section C} (h : s.Composes t v) :
    HEq s.left v.left ∧ HEq t.right v.right := by
  have hc := section_endpoints_heq h.family.context.equation h.family.equation h.equation
  have he := s.horizontal_endpoints t h.family.context.middle h.family.middle h.middle
  exact ⟨he.1.symm.trans hc.1, he.2.symm.trans hc.2⟩

private theorem section_reindex_heq {C C' D D' : Grpd.{u,u}} (hC : C = C') (hD : D = D')
    {A : C ⥤ Grpd.{u,u}} {B : C' ⥤ Grpd.{u,u}} (hA : HEq A B)
    {s : GroupoidModel.Section A} {t : GroupoidModel.Section B} (hs : HEq s t)
    {F : D ⥤ C} {G : D' ⥤ C'} (hF : HEq F G) : HEq (s.reindex F) (t.reindex G) := by
  cases hC; cases hD; cases eq_of_heq hA; cases eq_of_heq hs; cases eq_of_heq hF; rfl

theorem Section.Composes.reindex {Γ₀ Γ₁ Γ₂ Δ₀ Δ₁ Δ₂ : Context.{u}}
    {A : Family Γ₀} {B : Family Γ₁} {C : Family Γ₂}
    {s : Section A} {t : Section B} {v : Section C}
    {σ : Substitution Δ₀ Γ₀} {τ : Substitution Δ₁ Γ₁} {ρ : Substitution Δ₂ Γ₂}
    (hs : s.Composes t v) (hσ : σ.Composes τ ρ) :
    (s.reindex σ).Composes (t.reindex τ) (v.reindex ρ) :=
  Section.Composes.of_endpoints (hs.family.reindex hσ) _ _ _
    (section_reindex_heq hs.family.context.middle hσ.source.middle hs.family.middle hs.middle hσ.middle)
    (section_reindex_heq hs.family.context.left hσ.source.left hs.family.endpoints.1 hs.endpoints.1 hσ.endpoints.1)
    (section_reindex_heq hs.family.context.right hσ.source.right hs.family.endpoints.2 hs.endpoints.2 hσ.endpoints.2)

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison

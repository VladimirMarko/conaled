import SquareKit.Internal.PathTransport.ComparisonHorizontalIdentity
import SquareKit.Internal.PathTransport.ComparisonHorizontalFiber

/-! Relations expressing horizontal composition in the existing comparison
model. The equations retain complete functors and natural transformations. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

structure Context.Composes (Γ Δ Θ : Context.{u}) : Prop where
  middle : Γ.right = Δ.left
  equation : Γ.horizontal Δ middle = Θ

structure Family.Composes {Γ Δ Θ : Context.{u}} (A : Family Γ) (B : Family Δ)
    (C : Family Θ) : Prop where
  context : Γ.Composes Δ Θ
  middle : HEq A.right B.left
  equation : HEq (A.horizontal B context.middle middle) C

theorem Family.extend_heq {Γ Δ : Context.{u}} (hΓ : Γ = Δ)
    {A : Family Γ} {B : Family Δ} (hA : HEq A B) : A.extend = B.extend := by
  cases hΓ; cases eq_of_heq hA; rfl

theorem Family.Composes.extend {Γ Δ Θ : Context.{u}}
    {A : Family Γ} {B : Family Δ} {C : Family Θ} (h : A.Composes B C) :
    A.extend.Composes B.extend C.extend where
  middle := A.horizontal_middle B h.context.middle h.middle
  equation := (A.horizontal_extend B h.context.middle h.middle).symm.trans
    (Family.extend_heq h.context.equation h.equation)

structure Substitution.Composes {Γ₀ Γ₁ Γ₂ Δ₀ Δ₁ Δ₂ : Context.{u}}
    (σ : Substitution Δ₀ Γ₀) (τ : Substitution Δ₁ Γ₁) (ρ : Substitution Δ₂ Γ₂) : Prop where
  source : Δ₀.Composes Δ₁ Δ₂
  target : Γ₀.Composes Γ₁ Γ₂
  middle : HEq σ.right τ.left
  equation : HEq (σ.horizontal τ target.middle source.middle middle) ρ

theorem Family.Composes.reindex {Γ₀ Γ₁ Γ₂ Δ₀ Δ₁ Δ₂ : Context.{u}}
    {A : Family Γ₀} {B : Family Γ₁} {C : Family Γ₂}
    {σ : Substitution Δ₀ Γ₀} {τ : Substitution Δ₁ Γ₁} {ρ : Substitution Δ₂ Γ₂}
    (hA : A.Composes B C) (hσ : σ.Composes τ ρ) :
    (A.reindex σ).Composes (B.reindex τ) (C.reindex ρ) where
  context := hσ.source
  middle := A.horizontal_reindex_middle B σ τ hA.context.middle hσ.source.middle hA.middle hσ.middle
  equation := (heq_of_eq (A.horizontal_reindex B σ τ hA.context.middle hσ.source.middle
    hA.middle hσ.middle).symm).trans
      (Family.reindex_heq hA.context.equation hσ.source.equation hA.equation hσ.equation)

theorem Section.horizontal_endpoints {Γ Δ : Context.{u}} {A : Family Γ} {B : Family Δ}
    (s : Section A) (t : Section B) (h : Γ.right = Δ.left)
    (hA : HEq A.right B.left) (hs : HEq s.right t.left) :
    HEq (s.horizontal t h hA hs).left s.left ∧ HEq (s.horizontal t h hA hs).right t.right := by
  cases Γ; cases Δ; dsimp at h; cases h
  cases A; cases B; dsimp at hA; cases eq_of_heq hA
  cases s; cases t; dsimp at hs; cases eq_of_heq hs
  exact ⟨HEq.rfl, HEq.rfl⟩

structure Section.Composes {Γ Δ Θ : Context.{u}}
    {A : Family Γ} {B : Family Δ} {C : Family Θ}
    (s : Section A) (t : Section B) (v : Section C) : Prop where
  family : A.Composes B C
  middle : HEq s.right t.left
  equation : HEq (s.horizontal t family.context.middle family.middle middle) v

/-- Once the family comparison is known, full section composition is forced
by the two retained endpoint sections. -/
theorem Section.Composes.of_endpoints {Γ Δ Θ : Context.{u}}
    {A : Family Γ} {B : Family Δ} {C : Family Θ}
    (hA : A.Composes B C) (s : Section A) (t : Section B) (v : Section C)
    (hm : HEq s.right t.left) (hl : HEq s.left v.left) (hr : HEq t.right v.right) :
    s.Composes t v := by
  refine ⟨hA, hm, ?_⟩
  have he := s.horizontal_endpoints t hA.context.middle hA.middle hm
  rcases hA with ⟨⟨hmiddle, hcontext⟩, hmiddleA, hfamily⟩
  cases hcontext
  cases eq_of_heq hfamily
  exact heq_of_eq (Section.ext (eq_of_heq (he.1.trans hl)) (eq_of_heq (he.2.trans hr)))

theorem Family.identity_heq {Γ Δ : Context.{u}} (hΓ : Γ = Δ)
    {A : Family Γ} {B : Family Δ} (hA : HEq A B)
    {x y : Section A} {x' y' : Section B} (hx : HEq x x') (hy : HEq y y') :
    HEq (A.identity x y) (B.identity x' y') := by
  cases hΓ; cases eq_of_heq hA; cases eq_of_heq hx; cases eq_of_heq hy; rfl

theorem Section.Composes.identity {Γ Δ Θ : Context.{u}}
    {A : Family Γ} {B : Family Δ} {C : Family Θ}
    {s s' : Section A} {t t' : Section B} {v v' : Section C}
    (hs : s.Composes t v) (ht : s'.Composes t' v') :
    (A.identity s s').Composes (B.identity t t') (C.identity v v') where
  context := hs.family.context
  middle := A.horizontal_identity_middle B s s' t t' hs.family.context.middle
    hs.family.middle hs.middle ht.middle
  equation := (heq_of_eq (A.horizontal_identity B s s' t t' hs.family.context.middle
    hs.family.middle hs.middle ht.middle).symm).trans
      (Family.identity_heq hs.family.context.equation hs.family.equation hs.equation ht.equation)

theorem Signature.baseFamily_heq (S : Signature.{u}) {Γ Δ : Context.{u}} (h : Γ = Δ) :
    HEq (S.baseFamily Γ) (S.baseFamily Δ) := by cases h; rfl

theorem Signature.baseFamily_composes (S T : Signature.{u})
    (h : S.base.right = T.base.left) (hB : HEq S.rightFiber T.leftFiber)
    {Γ Δ Θ : Context.{u}} (hΓ : Γ.Composes Δ Θ) :
    (S.baseFamily Γ).Composes (T.baseFamily Δ) ((S.horizontal T h hB).baseFamily Θ) where
  context := hΓ
  middle := S.horizontal_baseFamily_middle T h hΓ.middle
  equation := (heq_of_eq (S.horizontal_baseFamily T h hB hΓ.middle).symm).trans
    ((S.horizontal T h hB).baseFamily_heq hΓ.equation)

theorem Substitution.horizontal_endpoints {Γ₀ Γ₁ Δ₀ Δ₁ : Context.{u}}
    (σ : Substitution Δ₀ Γ₀) (τ : Substitution Δ₁ Γ₁)
    (hΓ : Γ₀.right = Γ₁.left) (hΔ : Δ₀.right = Δ₁.left) (hσ : HEq σ.right τ.left) :
    HEq (σ.horizontal τ hΓ hΔ hσ).left σ.left ∧
      HEq (σ.horizontal τ hΓ hΔ hσ).right τ.right := by
  cases Γ₀; cases Γ₁; cases Δ₀; cases Δ₁
  dsimp at hΓ hΔ; cases hΓ; cases hΔ
  cases σ; cases τ; dsimp at hσ; cases eq_of_heq hσ
  exact ⟨HEq.rfl, HEq.rfl⟩

theorem Substitution.Composes.of_endpoints {Γ₀ Γ₁ Γ₂ Δ₀ Δ₁ Δ₂ : Context.{u}}
    (hΓ : Γ₀.Composes Γ₁ Γ₂) (hΔ : Δ₀.Composes Δ₁ Δ₂)
    (σ : Substitution Δ₀ Γ₀) (τ : Substitution Δ₁ Γ₁) (ρ : Substitution Δ₂ Γ₂)
    (hm : HEq σ.right τ.left) (hl : HEq σ.left ρ.left) (hr : HEq τ.right ρ.right) :
    σ.Composes τ ρ where
  source := hΔ
  target := hΓ
  middle := hm
  equation := Substitution.context_hext hΓ.equation hΔ.equation
    ((σ.horizontal_endpoints τ hΓ.middle hΔ.middle hm).1.trans hl)
    ((σ.horizontal_endpoints τ hΓ.middle hΔ.middle hm).2.trans hr)

theorem Signature.fiber_heq (S : Signature.{u}) {Γ Δ : Context.{u}} (hΓ : Γ = Δ)
    {x : Section (S.baseFamily Γ)} {y : Section (S.baseFamily Δ)} (hx : HEq x y) :
    HEq (S.fiber x) (S.fiber y) := by
  cases hΓ; cases eq_of_heq hx; rfl

theorem Signature.fiber_composes (S T : Signature.{u})
    (h : S.base.right = T.base.left) (hB : HEq S.rightFiber T.leftFiber)
    {Γ Δ Θ : Context.{u}}
    {s : Section (S.baseFamily Γ)} {t : Section (T.baseFamily Δ)}
    {v : Section ((S.horizontal T h hB).baseFamily Θ)} (hs : s.Composes t v) :
    (S.fiber s).Composes (T.fiber t) ((S.horizontal T h hB).fiber v) where
  context := hs.family.context
  middle := S.horizontal_fiber_middle T h hB hs.family.context.middle s t hs.middle
  equation := (heq_of_eq (S.horizontal_fiber T h hB hs.family.context.middle s t hs.middle).symm).trans
    ((S.horizontal T h hB).fiber_heq hs.family.context.equation
      ((cast_heq _ _).trans hs.equation))

theorem Context.Composes.left {Γ Δ Θ : Context.{u}} (h : Γ.Composes Δ Θ) : Γ.left = Θ.left := by
  have he := congrArg Context.left h.equation
  exact he

theorem Context.Composes.right {Γ Δ Θ : Context.{u}} (h : Γ.Composes Δ Θ) : Δ.right = Θ.right := by
  have he := congrArg Context.right h.equation
  exact he

theorem Family.horizontal_endpoints {Γ Δ : Context.{u}} (A : Family Γ) (B : Family Δ)
    (h : Γ.right = Δ.left) (hA : HEq A.right B.left) :
    HEq (A.horizontal B h hA).left A.left ∧ HEq (A.horizontal B h hA).right B.right := by
  cases Γ; cases Δ; dsimp at h; cases h
  cases A; cases B; dsimp at hA; cases eq_of_heq hA
  exact ⟨HEq.rfl, HEq.rfl⟩

private theorem family_endpoints_heq {Γ Δ : Context.{u}} (hΓ : Γ = Δ)
    {A : Family Γ} {B : Family Δ} (hA : HEq A B) :
    HEq A.left B.left ∧ HEq A.right B.right := by
  cases hΓ; cases eq_of_heq hA
  exact ⟨HEq.rfl, HEq.rfl⟩

theorem Family.Composes.endpoints {Γ Δ Θ : Context.{u}}
    {A : Family Γ} {B : Family Δ} {C : Family Θ} (h : A.Composes B C) :
    HEq A.left C.left ∧ HEq B.right C.right := by
  have hc := family_endpoints_heq h.context.equation h.equation
  have he := A.horizontal_endpoints B h.context.middle h.middle
  exact ⟨he.1.symm.trans hc.1, he.2.symm.trans hc.2⟩

private theorem substitution_endpoints_heq {Γ Γ' Δ Δ' : Context.{u}}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') {σ : Substitution Δ Γ} {τ : Substitution Δ' Γ'}
    (hσ : HEq σ τ) : HEq σ.left τ.left ∧ HEq σ.right τ.right := by
  cases hΓ; cases hΔ; cases eq_of_heq hσ
  exact ⟨HEq.rfl, HEq.rfl⟩

theorem Substitution.Composes.endpoints {Γ₀ Γ₁ Γ₂ Δ₀ Δ₁ Δ₂ : Context.{u}}
    {σ : Substitution Δ₀ Γ₀} {τ : Substitution Δ₁ Γ₁} {ρ : Substitution Δ₂ Γ₂}
    (h : σ.Composes τ ρ) : HEq σ.left ρ.left ∧ HEq τ.right ρ.right := by
  have hc := substitution_endpoints_heq h.target.equation h.source.equation h.equation
  have he := σ.horizontal_endpoints τ h.target.middle h.source.middle h.middle
  exact ⟨he.1.symm.trans hc.1, he.2.symm.trans hc.2⟩

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison

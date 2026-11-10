import SquareKit.SmoothQuotientGeneratedSectionDescent

/-! General dependent-tail consumers of actual canonical restriction descent. -/
noncomputable section
namespace Examples.GeneratedDescentClosure
open CategoryTheory SquareKit SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]

/-- The tail length and each dependent binder remain arbitrary. -/
example (hΓ : Typed.CtxDeriv.{2} Γ γ) (hT : Typed.TelDeriv.{2} Γ γ n Δ T) :
    (SmoothQuotientGeneratedMatching.restrictionFunctor a (.telescope hΓ hT) A).IsEquivalence :=
  SmoothQuotientGeneratedMatching.restriction_isEquivalence a A (.telescope hΓ hT)

/-- A pulled tail requires no equivalence assumption on its substitution. -/
example (hΩ : Typed.CtxDeriv.{2} Ω ω) (hT : Typed.TelDeriv.{2} Γ γ n Δ T)
    (hs : Typed.SubDeriv.{2} Ω ω Γ γ σ s) :
    (SmoothQuotientGeneratedMatching.restrictionFunctor a
      (.telescope hΩ (.pullback hT hs)) A).IsEquivalence :=
  SmoothQuotientGeneratedMatching.restriction_isEquivalence a A _

/-- Reindexing the complete path tail retains every dependent binder. -/
example (hΓ : Typed.CtxDeriv.{2} Γ γ) (hΩ : Typed.CtxDeriv.{2} Ω ω)
    (hB : Typed.TyDeriv.{2} Γ γ B b) (hx : Typed.TmDeriv.{2} Γ γ B b x ξ)
    (hT : Typed.TelDeriv.{2} (pathCtx Γ B x) (Typed.pathCode b ξ) n Δ T)
    (hs : Typed.SubDeriv.{2} Ω ω Γ γ σ s) :
    (SmoothQuotientGeneratedMatching.restrictionFunctor a
      (.telescope (.path hΩ (.sub hB hs) (.sub hx hs))
        (.pathReindex hΓ hB hx hT hs)) A).IsEquivalence :=
  SmoothQuotientGeneratedMatching.restriction_isEquivalence a A _

/-- The reflexive branch uses its complete pulled-back dependent tail. -/
example (hΓ : Typed.CtxDeriv.{2} Γ γ)
    (hB : Typed.TyDeriv.{2} Γ γ B b) (hx : Typed.TmDeriv.{2} Γ γ B b x ξ)
    (hT : Typed.TelDeriv.{2} (pathCtx Γ B x) (Typed.pathCode b ξ) n Δ T) :
    (SmoothQuotientGeneratedMatching.restrictionFunctor a (.branch hΓ hB hx hT) A).IsEquivalence :=
  SmoothQuotientGeneratedMatching.restriction_isEquivalence a A _

/-- Every independently supplied matching datum is recovered, including its overlap. -/
example (hΓ : Typed.CtxDeriv.{2} Γ γ)
    (d : SmoothQuotientGeneratedMatching.Datum a hΓ A) :
    (SmoothQuotientGeneratedMatching.restrictionFunctor a hΓ A).obj
      ((SmoothQuotientGeneratedMatching.descentEquivalence a A hΓ).inverse.obj d) ≅ d :=
  (SmoothQuotientGeneratedMatching.descentEquivalence a A hΓ).counitIso.app d

/-- Full matching sections descend to the original direct global model. -/
example (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b)
    (s : Section (SmoothQuotientGeneratedMatching.relativeMatchingFamily a hΓ hB A)) :
    Section (b (SmoothQuotientSource.model a X)) :=
  (SmoothQuotientGeneratedMatching.sectionDescent a A hΓ hB).reconstruct s

/-- Recovery is an isomorphism of complete lifted sections through actual restriction. -/
example (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b)
    (s : Section (SmoothQuotientGeneratedMatching.relativeMatchingFamily a hΓ hB A)) :
    ((SmoothQuotientGeneratedMatching.sectionDescent a A hΓ hB).reconstruct s).lift ⋙
        (SmoothQuotientGeneratedMatching.sectionTotalEquivalence a A hΓ hB).functor ≅
      SmoothQuotientGeneratedMatching.restrictionFunctor a hΓ A ⋙ s.lift :=
  (SmoothQuotientGeneratedMatching.sectionDescent a A hΓ hB).recovery s

/-- A supplied vertical transformation has exactly one descended preimage. -/
example (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b)
    (s t : Section (SmoothQuotientGeneratedMatching.relativeMatchingFamily a hΓ hB A))
    (η : {η : s.lift ⟶ t.lift // ∀ d, (η.app d).base = 𝟙 d}) :
    ∃! ξ, (SmoothQuotientGeneratedMatching.sectionDescent a A hΓ hB).verticalEquiv s t ξ = η := by
  let e := (SmoothQuotientGeneratedMatching.sectionDescent a A hΓ hB).verticalEquiv s t
  exact ⟨e.symm η, e.apply_symm_apply η, fun ξ h => e.injective (h.trans (e.apply_symm_apply η).symm)⟩

end Examples.GeneratedDescentClosure

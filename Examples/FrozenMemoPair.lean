import Examples.MemoPairEvaluation
import Examples.FrozenMemoRealization

/-! The frozen memo's selected value and eta witness form an object dependent
pair in every contextual model supplying the sum capability. -/
noncomputable section
namespace Examples.FrozenMemoRealization
open SquareKit.GuardedTheory SquareKit.Internal.DependentJudgments
open Contextual Contextual.Memo Contextual.DerivedSemantics
open Examples.GuardedGroupoidMemo
set_option backward.isDefEq.respectTransparency false
universe u
variable {M : SquareKit.Internal.PathTransport.Typed.Model.{u}} {V : Type}
variable {Ω : List (Contextual.Judgment V)} {ρ : V → Value M.toStructuralModel}
variable {F : Frozen.Input Ω}
namespace InputRealization
variable (R : InputRealization M ρ F)
variable (S : Sigma.Capability M.toStructuralModel)
variable (hΩ : ∀ j ∈ Ω, j.eval (Contextual.algebra M) ρ)

abbrev resultFamily := M.subTy R.fiber (M.toStructuralModel.sectionSub R.family R.z)

def selectedPair := MemoPair.pair M.toStructuralModel R.resultFamily R.selectedComposite
  S R.selectedValue R.selectedCertificate

include hΩ in
theorem resultFamily_eval : (F.parameters.fiber F.p).eval (Contextual.algebra M) ρ =
    .family R.context R.resultFamily := by
  have hs := sectionSub_eval M ρ F.Γ F.A F.z R.context R.family R.z
    R.context_eval R.family_eval R.z_eval
  exact (Contextual.interpret (F.parameters.fiber_atPath F.hp) M ρ hΩ).trans
    (subTy_eval M ρ F.B _ _ _ R.fiber _ R.fiber_eval hs)

include hΩ in
theorem pair_eval :
    (MemoPair.sourcePair F.Γ (F.parameters.fiber F.p) (F.parameters.compositeValue F.p)
      (F.parameters.value F.p) (F.parameters.certificate F.p)).eval (Sigma.algebra M S) ρ =
      .term R.context _ (R.selectedPair S) :=
  Examples.MemoPairEvaluation.pair_eval M S ρ _ _ _ _ _ R.context R.resultFamily
    R.selectedComposite R.selectedValue R.selectedCertificate R.context_eval
    (R.resultFamily_eval hΩ) (R.composite_eval hΩ) (R.value_eval hΩ) (R.certificate_eval hΩ)

/-- The source pair is typed using the retained original memo derivations. -/
noncomputable def pair_typed :
    Sigma.Tm (Ω := Ω.map (Atom.inl Sigma.extraSignature)) (F.Γ.inl Sigma.extraSignature)
      (Sigma.sigma ((F.parameters.fiber F.p).inl Sigma.extraSignature)
        ((MemoPair.sourceCertificateFamily F.Γ (F.parameters.fiber F.p)
          (F.parameters.compositeValue F.p)).inl Sigma.extraSignature))
      (MemoPair.sourcePair F.Γ (F.parameters.fiber F.p) (F.parameters.compositeValue F.p)
        (F.parameters.value F.p) (F.parameters.certificate F.p)) :=
  MemoPair.sourcePair_typed
    (F.parameters.varyingCompositeValue_typed.substitute F.hp.section)
    (F.parameters.value_typed F.hp)
    ((F.parameters.certificate_typed F.hp).convert (F.parameters.certificateType_eq F.hp))


include hΩ in
theorem pair_twice_eval {D T : M.Context} (s t : Contextual.Expression V)
    (σ : M.Substitution D R.context) (τ : M.Substitution T D)
    (hs : s.eval (Contextual.algebra M) ρ = .substitution D R.context σ)
    (ht : t.eval (Contextual.algebra M) ρ = .substitution T D τ) :
    (Sigma.subTm (Sigma.subTm
      (MemoPair.sourcePair F.Γ (F.parameters.fiber F.p) (F.parameters.compositeValue F.p)
        (F.parameters.value F.p) (F.parameters.certificate F.p))
      (s.inl Sigma.extraSignature)) (t.inl Sigma.extraSignature)).eval (Sigma.algebra M S) ρ =
      .term T _ (M.subTm (M.subTm (R.selectedPair S) σ) τ) :=
  Examples.MemoPairEvaluation.subTm_eval M S ρ τ
    (Examples.MemoPairEvaluation.subTm_eval M S ρ σ (R.pair_eval S hΩ)
      ((Sigma.eval_old M S _ ρ).trans hs))
    ((Sigma.eval_old M S _ ρ).trans ht)

end InputRealization
namespace FrozenSignature
variable (M : SquareKit.Internal.PathTransport.Typed.Model.{u})
  (S : Sigma.Capability M.toStructuralModel) {V : Type}
  {Ω : List (Contextual.Judgment V)} (ρ : V → Value M.toStructuralModel)
  (hΩ : ∀ j ∈ Ω, j.eval (Contextual.algebra M) ρ)
  (F : Frozen.Signature Ω) (R : InputRealization M ρ F.input)

include hΩ in
theorem pair_twice : ∃ (D T : M.Context) (σ : M.Substitution D R.context)
    (τ : M.Substitution T D),
    F.sigma.eval (Contextual.algebra M) ρ = .substitution D R.context σ ∧
    F.tau.eval (Contextual.algebra M) ρ = .substitution T D τ ∧
    (Sigma.subTm (Sigma.subTm
      (MemoPair.sourcePair F.input.Γ (F.input.parameters.fiber F.input.p)
        (F.input.parameters.compositeValue F.input.p) (F.input.parameters.value F.input.p)
        (F.input.parameters.certificate F.input.p))
      (F.sigma.inl Sigma.extraSignature)) (F.tau.inl Sigma.extraSignature)).eval (Sigma.algebra M S) ρ =
      .term T _ (M.subTm (M.subTm (R.selectedPair S) σ) τ) := by
  rcases Contextual.interpret F.sigma_typed M ρ hΩ with ⟨D,G,σ,hD,hG,hs⟩
  have eG := Value.context.inj (hG.symm.trans R.context_eval)
  subst G
  rcases Contextual.interpret F.tau_typed M ρ hΩ with ⟨T,D',τ,hT,hD',ht⟩
  have eD := Value.context.inj (hD'.symm.trans hD)
  subst D'
  exact ⟨D,T,σ,τ,hs,ht,R.pair_twice_eval S hΩ F.sigma F.tau σ τ hs ht⟩
end FrozenSignature

end Examples.FrozenMemoRealization

import SquareKit.Internal.DependentJudgments.ComprehensionEtaRule
import SquareKit.Internal.DependentJudgments.ComprehensionMaps

/-! One generated source theory and its interpretation in every contextual
model. The interpretation is supplied by library builders, not by authors of
individual derivations. -/
namespace SquareKit.Internal.DependentJudgments.Contextual
set_option backward.isDefEq.respectTransparency false
open GuardedTheory PathTransport.Typed
universe u

inductive Axiom where
  | pairEta | pathSubDef
  | pathTailNil | pathTailMapNil | reindexBranchNil
  | pairComp | pathDef | rootDef | rootProjection | rootTailNil | totalNil | pullbackNil
  | subTy | subTm | comp | compIdLeft | compIdRight | compAssoc
  | subTyId | subTmId | subTyComp | subTmComp | termFamily | familyContext
  | identity | identitySub | reflexivity | reflSub | path | root | pathSub
  | telNil | telCons (n : Nat) | total (n : Nat) | projection (n : Nat)
  | pullback (n : Nat) | tailMap (n : Nat) | rootTail (n : Nat)
  | pathTail (n : Nat) | pathTailMap (n : Nat) | branchMap (n : Nat)
  | reindexBranch (n : Nat) | j (n : Nat) | jBeta (n : Nat) | jSub (n : Nat)

def rule : Axiom → Rule signature
  | .pairEta => pairEtaRule
  | .pathSubDef => pathSubDefRule
  | .pathTailNil => pathTailNilRule
  | .pathTailMapNil => pathTailMapNilRule
  | .reindexBranchNil => reindexBranchNilRule
  | .pairComp => pairCompRule
  | .pathDef => pathDefRule
  | .rootDef => rootDefRule
  | .rootProjection => rootProjectionRule
  | .rootTailNil => rootTailNilRule
  | .totalNil => totalNilRule
  | .pullbackNil => pullbackNilRule
  | .subTy => subTyRule
  | .subTm => subTmRule
  | .comp => compRule
  | .compIdLeft => compIdLeftRule
  | .compIdRight => compIdRightRule
  | .compAssoc => compAssocRule
  | .subTyId => subTyIdRule
  | .subTmId => subTmIdRule
  | .subTyComp => subTyCompRule
  | .subTmComp => subTmCompRule
  | .termFamily => termFamilyRule
  | .familyContext => familyContextRule
  | .identity => identityRule
  | .identitySub => identitySubRule
  | .reflexivity => reflexivityRule
  | .reflSub => reflSubRule
  | .path => pathRule
  | .root => rootRule
  | .pathSub => pathSubRule
  | .telNil => telNilRule
  | .telCons n => telConsRule n
  | .total n => totalRule n
  | .projection n => projectionRule n
  | .pullback n => pullbackRule n
  | .tailMap n => tailMapRule n
  | .rootTail n => rootTailRule n
  | .pathTail n => pathTailRule n
  | .pathTailMap n => pathTailMapRule n
  | .branchMap n => branchMapRule n
  | .reindexBranch n => reindexBranchRule n
  | .j n => jRule n
  | .jBeta n => jBetaRule n
  | .jSub n => jSubRule n

abbrev theory := comprehensionTheory.extend extraSignature Axiom rule

theorem rule_valid (M : PathTransport.Typed.Model.{u}) : ∀ a, Satisfies (algebra M) (rule a)
  | .pairEta => pairEta_valid M
  | .pathSubDef => pathSubDef_valid M
  | .pathTailNil => pathTailNil_valid M
  | .pathTailMapNil => pathTailMapNil_valid M
  | .reindexBranchNil => reindexBranchNil_valid M
  | .pairComp => pairComp_valid M
  | .pathDef => pathDef_valid M
  | .rootDef => rootDef_valid M
  | .rootProjection => rootProjection_valid M
  | .rootTailNil => rootTailNil_valid M
  | .totalNil => totalNil_valid M
  | .pullbackNil => pullbackNil_valid M
  | .subTy => subTy_valid M
  | .subTm => subTm_valid M
  | .comp => comp_valid M
  | .compIdLeft => compIdLeft_valid M
  | .compIdRight => compIdRight_valid M
  | .compAssoc => compAssoc_valid M
  | .subTyId => subTyId_valid M
  | .subTmId => subTmId_valid M
  | .subTyComp => subTyComp_valid M
  | .subTmComp => subTmComp_valid M
  | .termFamily => termFamily_valid M
  | .familyContext => familyContext_valid M
  | .identity => identity_valid M
  | .identitySub => identitySub_valid M
  | .reflexivity => reflexivity_valid M
  | .reflSub => reflSub_valid M
  | .path => path_valid M
  | .root => root_valid M
  | .pathSub => pathSub_valid M
  | .telNil => telNil_valid M
  | .telCons n => telCons_valid M n
  | .total n => total_valid M n
  | .projection n => projection_valid M n
  | .pullback n => pullback_valid M n
  | .tailMap n => tailMap_valid M n
  | .rootTail n => rootTail_valid M n
  | .pathTail n => pathTail_valid M n
  | .pathTailMap n => pathTailMap_valid M n
  | .branchMap n => branchMap_valid M n
  | .reindexBranch n => reindexBranch_valid M n
  | .j n => j_valid M n
  | .jBeta n => jBeta_valid M n
  | .jSub n => jSub_valid M n

noncomputable def model (M : PathTransport.Typed.Model.{u}) : GuardedTheory.Model theory where
  toAlgebra := algebra M
  rules
    | .inl a => by
      intro ρ h
      simp only [theory, Theory.extend, Rule.inl, Atom.eval_inl] at h ⊢
      exact (comprehensionModel M.toStructuralModel).rules a ρ h
    | .inr a => rule_valid M a

variable {V : Type} {Ω : List (Judgment V)}

abbrev Ctx (Γ : Expression V) := Derivation theory Ω (context Γ)
abbrev Ty (Γ A : Expression V) := Derivation theory Ω (family Γ A)
abbrev Tm (Γ A t : Expression V) := Derivation theory Ω (term Γ A t)
abbrev Sub (Δ Γ σ : Expression V) := Derivation theory Ω (substitution Δ Γ σ)
abbrev Tel (n : Nat) (Γ T : Expression V) := Derivation theory Ω (telescope n Γ T)
abbrev Equal (a b : Expression V) := Derivation theory Ω (.eq a b)

/-- Interpretation applies to the same source derivation at a newly supplied
model and schematic assignment. Assumptions are source typing/equality guards. -/
theorem interpret {a : Judgment V} (d : Derivation theory Ω a)
    (M : PathTransport.Typed.Model.{u}) (ρ : V → Value M.toStructuralModel)
    (h : ∀ p ∈ Ω, p.eval (algebra M) ρ) : a.eval (algebra M) ρ :=
  d.sound (model M) ρ h

/-- Simultaneous source substitution preserves every admitted derivation. -/
noncomputable def substitute {W : Type} {a : Judgment V} (d : Derivation theory Ω a)
    (σ : V → Expression W) :
    Derivation theory (Ω.map (Atom.subst σ)) (a.subst σ) := d.substitute σ

end SquareKit.Internal.DependentJudgments.Contextual

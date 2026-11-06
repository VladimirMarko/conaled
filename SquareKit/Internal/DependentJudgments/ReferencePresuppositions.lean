import SquareKit.Internal.DependentJudgments.ReferenceCalculus

/-! Syntactic presuppositions of the reference judgments. Equalities retain
both operands at their common boundary; raw target equality does not. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Reference
variable {V : Type} {Ξ : List (Declaration V)}

namespace Derives
noncomputable section

def pathFamilyType {Γ A x : Expression V} (hx : Derives Ξ (.has (.tm Γ A) x)) :
    Derives Ξ (.has (.ty (Contextual.extend Γ A)) (pathFamily Γ A x)) :=
  .identity (.subTm hx (.weaken (.termFamily hx))) (.generic (.termFamily hx))

private def Presupposition : Claim V → Type
  | .has (.sub Δ Γ) _ => Derives Ξ (.has .ctx Δ) × Derives Ξ (.has .ctx Γ)
  | .eq b s t => Derives Ξ (.has b s) × Derives Ξ (.has b t)
  | .has (.tel _ Γ) _ => Derives Ξ (.has .ctx Γ)
  | .tail Γ _ => Derives Ξ (.has .ctx Γ)
  | _ => PUnit

private def presupposition {c : Claim V} (h : Derives Ξ c) : Presupposition (Ξ := Ξ) c := by
  induction h <;> try exact PUnit.unit
  case nil hΓ _ => exact hΓ
  case cons hA _ _ _ => exact .typeContext hA
  case tailCode _ ih => exact ih
  case contextConvertTel _ _ _ ih => exact ih.2
  case identitySub hΓ _ => exact ⟨hΓ, hΓ⟩
  case comp hσ hτ ihσ ihτ => exact ⟨ihτ.1, ihσ.2⟩
  case weaken hA _ => exact ⟨.extend hA, .typeContext hA⟩
  case pair hA hσ _ _ ihσ _ => exact ⟨ihσ.1, .extend hA⟩
  case root hx _ => exact ⟨.typeContext (.termFamily hx), .path hx⟩
  case branchMap _ _ _ hdom hcod _ _ _ _ _ => exact ⟨hdom, hcod⟩
  case branchSquare _ _ _ hl hr _ _ _ _ _ => exact ⟨hl, hr⟩
  case jSub _ _ _ _ _ hl hr _ _ _ _ _ _ _ => exact ⟨hl, hr⟩
  case jBeta _ _ _ hd hl _ _ _ _ _ => exact ⟨hl, hd⟩
  case pathSub hx hs _ _ => exact ⟨.path (.subTm hx hs), .path hx⟩
  case contextConvertSub _ _ _ _ ihΔ ihΓ => exact ⟨ihΔ.2, ihΓ.2⟩
  case pathDef hx _ => exact ⟨.path hx, .extend (pathFamilyType hx)⟩
  case rootDef hx hr _ _ => exact ⟨.root hx, hr⟩
  case pairEta _ hσ hl _ _ _ => exact ⟨hl, hσ⟩
  case familyEqDecl _ hA hB _ _ => exact ⟨hA, hB⟩
  case termEqDecl _ hs ht _ _ => exact ⟨hs, ht⟩
  case eqRefl ht _ => exact ⟨ht, ht⟩
  case eqSymm h ih => exact ⟨ih.2, ih.1⟩
  case eqTrans h h' ih ih' => exact ⟨ih.1, ih'.2⟩
  case congruence _ _ hs ht _ _ _ _ => exact ⟨hs, ht⟩
  case pairComp hA hσ ht hτ _ _ _ _ =>
    exact ⟨.comp (.pair hA hσ ht) hτ,
      .pair hA (.comp hσ hτ) (.convert (.subTm ht hτ) (.subTyComp hA hσ hτ))⟩
  case subTyId hA _ => exact ⟨.subTy hA (.identitySub (.typeContext hA)), hA⟩
  case subTyComp hA hσ hτ _ _ _ => exact ⟨.subTy (.subTy hA hσ) hτ, .subTy hA (.comp hσ hτ)⟩
  case subTmId ht _ => exact ⟨.convert (.subTm ht (.identitySub (.typeContext (.termFamily ht))))
      (.subTyId (.termFamily ht)), ht⟩
  case subTmComp ht hσ hτ _ _ _ => exact ⟨.convert (.subTm (.subTm ht hσ) hτ)
      (.subTyComp (.termFamily ht) hσ hτ), .subTm ht (.comp hσ hτ)⟩
  case subIdLeft hσ ihσ => exact ⟨.comp (.identitySub ihσ.2) hσ, hσ⟩
  case subIdRight hσ ihσ => exact ⟨.comp hσ (.identitySub ihσ.1), hσ⟩
  case subAssoc hσ hτ hυ _ _ _ => exact ⟨.comp (.comp hσ hτ) hυ, .comp hσ (.comp hτ hυ)⟩
  case weakenPair hA hσ ht _ _ _ => exact ⟨.comp (.weaken hA) (.pair hA hσ ht), hσ⟩
  case genericPair _ _ ht hl _ _ _ _ => exact ⟨hl, ht⟩
  case identitySubLaw hx hy hσ _ _ _ => exact ⟨.subTy (.identity hx hy) hσ,
      .identity (.subTm hx hσ) (.subTm hy hσ)⟩
  case reflexivitySubLaw hx hσ _ _ => exact ⟨.convert (.subTm (.reflexivity hx) hσ)
      (.identitySubLaw hx hx hσ), .reflexivity (.subTm hx hσ)⟩

def telescopeContext {n : Nat} {Γ T : Expression V}
    (h : Derives Ξ (.has (.tel n Γ) T)) : Derives Ξ (.has .ctx Γ) := presupposition h

def tailContext {Γ : Expression V} {T : Tail V}
    (h : Derives Ξ (.tail Γ T)) : Derives Ξ (.has .ctx Γ) := presupposition h

def subContexts {Δ Γ σ : Expression V} (h : Derives Ξ (.has (.sub Δ Γ) σ)) :
    Derives Ξ (.has .ctx Δ) × Derives Ξ (.has .ctx Γ) := presupposition h

def eqOperands {b : Boundary V} {s t : Expression V}
    (h : Derives Ξ (.eq b s t)) :
    Derives Ξ (.has b s) × Derives Ξ (.has b t) := presupposition h

end
end Derives
end SquareKit.Internal.DependentJudgments.Contextual.Reference

import SquareKit.Internal.DependentJudgments.ReferenceTranslation
import SquareKit.Internal.DependentJudgments.ReferencePresuppositions

/-! Schematic instantiation replaces free syntax leaves. Object substitution
is instead an explicitly typed constructor of the calculus. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Reference
open GuardedTheory
variable {V W : Type}

@[simp] theorem subst_liftSyntax (Δ A σ : Expression V) (θ : V → Expression W) :
    (liftSyntax Δ A σ).subst θ = liftSyntax (Δ.subst θ) (A.subst θ) (σ.subst θ) := by
  simp [liftSyntax]

namespace Tail
@[simp] theorem instantiate_reindex (T : Tail V) (Δ σ : Expression V) (θ : V → Expression W) :
    (T.reindex Δ σ).instantiate θ =
      (T.instantiate θ).reindex (Δ.subst θ) (σ.subst θ) := by
  induction T generalizing Δ σ with
  | nil => rfl
  | cons A T ih => simp [reindex, instantiate, ih]

@[simp] theorem instantiate_map (T : Tail V) (Δ σ : Expression V) (θ : V → Expression W) :
    (T.map Δ σ).subst θ = (T.instantiate θ).map (Δ.subst θ) (σ.subst θ) := by
  induction T generalizing Δ σ with
  | nil => rfl
  | cons A T ih => simp [map, instantiate, ih]
end Tail

def Boundary.instantiate (θ : V → Expression W) : Boundary V → Boundary W
  | .ctx => .ctx
  | .ty Γ => .ty (Γ.subst θ)
  | .tm Γ A => .tm (Γ.subst θ) (A.subst θ)
  | .sub Δ Γ => .sub (Δ.subst θ) (Γ.subst θ)

def Claim.instantiate (θ : V → Expression W) : Claim V → Claim W
  | .has b t => .has (b.instantiate θ) (t.subst θ)
  | .eq b s t => .eq (b.instantiate θ) (s.subst θ) (t.subst θ)
  | .tail Γ T => .tail (Γ.subst θ) (T.instantiate θ)

def Declaration.instantiate (θ : V → Expression W) : Declaration V → Declaration W
  | .family Γ A => .family (Γ.subst θ) (A.subst θ)
  | .term Γ A t => .term (Γ.subst θ) (A.subst θ) (t.subst θ)
  | .familyEq Γ A B => .familyEq (Γ.subst θ) (A.subst θ) (B.subst θ)
  | .termEq Γ A s t => .termEq (Γ.subst θ) (A.subst θ) (s.subst θ) (t.subst θ)

noncomputable def Derives.instantiate {Ξ : List (Declaration V)} {c : Claim V}
    (h : Derives Ξ c) (θ : V → Expression W) :
    Derives (Ξ.map (Declaration.instantiate θ)) (c.instantiate θ) := by
  induction h <;> simp only [Claim.instantiate, Boundary.instantiate] at *
  case empty => simpa using (Derives.empty (Ξ := Ξ.map (Declaration.instantiate θ)))
  case extend _ ih => simpa using Derives.extend ih
  case familyDecl hm _ ih => exact .familyDecl (List.mem_map.mpr ⟨_, hm, rfl⟩) ih
  case termDecl hm _ ih => exact .termDecl (List.mem_map.mpr ⟨_, hm, rfl⟩) ih
  case typeContext _ ih => exact .typeContext ih
  case termFamily _ ih => exact .termFamily ih
  case subTy _ _ ih ih' => simpa using Derives.subTy ih ih'
  case subTm _ _ ih ih' => simpa using Derives.subTm ih ih'
  case identitySub _ ih => simpa using Derives.identitySub ih
  case comp _ _ ih ih' => simpa using Derives.comp ih ih'
  case weaken _ ih => simpa using Derives.weaken ih
  case generic _ ih => simpa using Derives.generic ih
  case pair _ _ _ ih ih' ih'' => simpa using Derives.pair ih ih' (by simpa [Claim.instantiate, Boundary.instantiate] using ih'')
  case identity _ _ ih ih' => simpa using Derives.identity ih ih'
  case reflexivity _ ih => simpa using Derives.reflexivity ih
  case path _ ih => simpa using Derives.path ih
  case root _ ih => simpa using Derives.root ih
  case pathSub _ _ ih ih' => simpa using Derives.pathSub ih ih'
  case nil _ ih => exact .nil ih
  case cons _ _ ih ih' => simpa [Tail.instantiate] using Derives.cons ih (by simpa [Claim.instantiate, Boundary.instantiate] using ih')
  case tailTotal _ ih0 =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.alongPath, Tail.alongPathMap, Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      Derives.tailTotal (by simpa [Claim.instantiate, Boundary.instantiate, Tail.alongPath, Tail.alongPathMap, Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using ih0)
  case branchMap _ _ _ _ _ ih0 ih1 ih2 ih3 ih4 =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.alongPath, Tail.alongPathMap, Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      Derives.branchMap (by simpa [Claim.instantiate, Boundary.instantiate, Tail.alongPath, Tail.alongPathMap, Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using ih0)
        (by simpa [Claim.instantiate, Boundary.instantiate, Tail.alongPath, Tail.alongPathMap, Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using ih1)
        (by simpa [Claim.instantiate, Boundary.instantiate, Tail.alongPath, Tail.alongPathMap, Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using ih2)
        (by simpa [Claim.instantiate, Boundary.instantiate, Tail.alongPath, Tail.alongPathMap, Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using ih3)
        (by simpa [Claim.instantiate, Boundary.instantiate, Tail.alongPath, Tail.alongPathMap, Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using ih4)
  case branchSquare _ _ _ _ _ ih0 ih1 ih2 ih3 ih4 =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.alongPath, Tail.alongPathMap, Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      Derives.branchSquare (by simpa [Claim.instantiate, Boundary.instantiate, Tail.alongPath, Tail.alongPathMap, Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using ih0)
        (by simpa [Claim.instantiate, Boundary.instantiate, Tail.alongPath, Tail.alongPathMap, Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using ih1)
        (by simpa [Claim.instantiate, Boundary.instantiate, Tail.alongPath, Tail.alongPathMap, Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using ih2)
        (by simpa [Claim.instantiate, Boundary.instantiate, Tail.alongPath, Tail.alongPathMap, Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using ih3)
        (by simpa [Claim.instantiate, Boundary.instantiate, Tail.alongPath, Tail.alongPathMap, Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using ih4)
  case jSub _ _ _ _ _ _ _ ih0 ih1 ih2 ih3 ih4 ih5 ih6 =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.alongPath, Tail.alongPathMap, Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      Derives.jSub (by simpa [Claim.instantiate, Boundary.instantiate, Tail.alongPath, Tail.alongPathMap, Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using ih0)
        (by simpa [Claim.instantiate, Boundary.instantiate, Tail.alongPath, Tail.alongPathMap, Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using ih1)
        (by simpa [Claim.instantiate, Boundary.instantiate, Tail.alongPath, Tail.alongPathMap, Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using ih2)
        (by simpa [Claim.instantiate, Boundary.instantiate, Tail.alongPath, Tail.alongPathMap, Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using ih3)
        (by simpa [Claim.instantiate, Boundary.instantiate, Tail.alongPath, Tail.alongPathMap, Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using ih4)
        (by simpa [Claim.instantiate, Boundary.instantiate, Tail.alongPath, Tail.alongPathMap, Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using ih5)
        (by simpa [Claim.instantiate, Boundary.instantiate, Tail.alongPath, Tail.alongPathMap, Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using ih6)
  case j _ _ _ _ ih ih' ih'' ih''' =>
    simpa [← Tail.instantiate_total, ← Tail.instantiate_code] using
      Derives.j ih (by simpa [Claim.instantiate, Boundary.instantiate] using ih')
        (by simpa [Claim.instantiate, Boundary.instantiate, ← Tail.instantiate_total] using ih'')
        (by simpa [Claim.instantiate, Boundary.instantiate, ← Tail.instantiate_total] using ih''')
  case jBeta _ _ _ _ _ ih ih' ih'' ih''' ih'''' =>
    simpa [← Tail.instantiate_total, ← Tail.instantiate_code] using
      Derives.jBeta ih (by simpa [Claim.instantiate, Boundary.instantiate] using ih')
        (by simpa [Claim.instantiate, Boundary.instantiate, ← Tail.instantiate_total] using ih'')
        (by simpa [Claim.instantiate, Boundary.instantiate, ← Tail.instantiate_total] using ih''')
        (by simpa [Claim.instantiate, Boundary.instantiate, ← Tail.instantiate_total,
          ← Tail.instantiate_code] using ih'''')
  case convert _ _ ih ih' => exact .convert ih ih'
  case contextConvertType _ _ ih ie => exact .contextConvertType ih ie
  case contextConvertTerm _ _ ih ie => exact .contextConvertTerm ih ie
  case contextConvertSub _ _ _ ih ie ie' => exact .contextConvertSub ih ie ie'
  case pathDef _ ih => simpa [pathFamily] using Derives.pathDef ih
  case rootDef _ _ ih ih' =>
    simpa [pathFamily, sectionSub] using Derives.rootDef ih
      (by simpa [Claim.instantiate, Boundary.instantiate, pathFamily, sectionSub] using ih')
  case pairEta _ _ _ ih ih' ih'' =>
    simpa using Derives.pairEta ih
      (by simpa [Claim.instantiate, Boundary.instantiate] using ih')
      (by simpa [Claim.instantiate, Boundary.instantiate] using ih'')
  case familyEqDecl hm _ _ ih ih' => exact .familyEqDecl (List.mem_map.mpr ⟨_, hm, rfl⟩) ih ih'
  case termEqDecl hm _ _ ih ih' => exact .termEqDecl (List.mem_map.mpr ⟨_, hm, rfl⟩) ih ih'
  case pairComp _ _ _ _ ihA ihσ iht ihτ =>
    simpa using Derives.pairComp ihA ihσ
      (by simpa [Claim.instantiate, Boundary.instantiate] using iht) ihτ
  case subTyId _ ih => simpa using Derives.subTyId ih
  case subTyComp _ _ _ ih ih' ih'' => simpa using Derives.subTyComp ih ih' (by simpa [Claim.instantiate, Boundary.instantiate] using ih'')
  case subTmId _ ih => simpa using Derives.subTmId ih
  case subTmComp _ _ _ ih ih' ih'' => simpa using Derives.subTmComp ih ih' (by simpa [Claim.instantiate, Boundary.instantiate] using ih'')
  case subIdLeft _ ih => simpa using Derives.subIdLeft ih
  case subIdRight _ ih => simpa using Derives.subIdRight ih
  case subAssoc _ _ _ ih ih' ih'' => simpa using Derives.subAssoc ih ih' (by simpa [Claim.instantiate, Boundary.instantiate] using ih'')
  case weakenPair _ _ _ ih ih' ih'' => simpa using Derives.weakenPair ih ih' (by simpa [Claim.instantiate, Boundary.instantiate] using ih'')
  case genericPair _ _ _ _ ih ih' ih'' ih''' => simpa using Derives.genericPair ih ih' (by simpa [Claim.instantiate, Boundary.instantiate] using ih'') (by simpa [Claim.instantiate, Boundary.instantiate] using ih''')
  case identitySubLaw _ _ _ ih ih' ih'' => simpa using Derives.identitySubLaw ih ih' (by simpa [Claim.instantiate, Boundary.instantiate] using ih'')
  case reflexivitySubLaw _ _ ih ih' => simpa using Derives.reflexivitySubLaw ih ih'
  case eqRefl _ ih => exact .eqRefl ih
  case eqSymm _ ih => exact .eqSymm ih
  case eqTrans _ _ ih ih' => exact .eqTrans ih ih'
  case congruence => apply Derives.congruence <;> assumption

end SquareKit.Internal.DependentJudgments.Contextual.Reference

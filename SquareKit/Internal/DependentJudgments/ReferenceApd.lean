import SquareKit.Internal.DependentJudgments.ReferencePath
import SquareKit.Internal.DependentJudgments.DerivedCertificates

/-! Dependent action on paths is derived from the independent reference J
rules. The expression is the retained native recipe, not a new primitive. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Reference
open GuardedTheory
variable {V : Type} {Ξ : List (Declaration V)}
variable {Γ A B x y p t u : Expression V}
namespace Derives
noncomputable section

def transportGeneric (hB : Derives Ξ (.has (.ty (Contextual.extend Γ A)) B))
    (hx : Derives Ξ (.has (.tm Γ A) x))
    (hu : Derives Ξ (.has (.tm Γ (Contextual.subTy B (Contextual.sectionSub Γ A x))) u)) :
    Derives Ξ (.has (.tm (Contextual.path A x) (Contextual.transportMotive Γ A B x))
      (Contextual.transportGeneric Γ A B x u)) :=
  basedJ hx (.subTy hB (pathProjection hx)) (.convert hu (.eqSymm (transportRoot hB hx)))

def transportGenericRoot (hB : Derives Ξ (.has (.ty (Contextual.extend Γ A)) B))
    (hx : Derives Ξ (.has (.tm Γ A) x))
    (hu : Derives Ξ (.has (.tm Γ (Contextual.subTy B (Contextual.sectionSub Γ A x))) u)) :
    Derives Ξ (.eq (.tm Γ (Contextual.subTy B (Contextual.sectionSub Γ A x)))
      (Contextual.subTm (Contextual.transportGeneric Γ A B x u) (Contextual.root A x)) u) :=
  termEqualityAt
    (basedJBeta hx (.subTy hB (pathProjection hx)) (.convert hu (.eqSymm (transportRoot hB hx))))
    (.convert (.subTm (transportGeneric hB hx hu) (.root hx)) (transportRoot hB hx)) hu

def apdMotive (ht : Derives Ξ (.has (.tm (Contextual.extend Γ A) B) t))
    (hx : Derives Ξ (.has (.tm Γ A) x)) :
    Derives Ξ (.has (.ty (Contextual.path A x)) (Contextual.apdMotive Γ A B x t)) :=
  .identity (transportGeneric ht.termFamily hx (.subTm ht (sectionMap hx)))
    (.subTm ht (pathProjection hx))

def apdMotiveRoot (ht : Derives Ξ (.has (.tm (Contextual.extend Γ A) B) t))
    (hx : Derives Ξ (.has (.tm Γ A) x)) :
    Derives Ξ (.eq (.ty Γ)
      (Contextual.subTy (Contextual.apdMotive Γ A B x t) (Contextual.root A x))
      (Contextual.identity (Contextual.subTy B (Contextual.sectionSub Γ A x))
        (Contextual.subTm t (Contextual.sectionSub Γ A x))
        (Contextual.subTm t (Contextual.sectionSub Γ A x)))) := by
  have hs := Derives.subTm ht (sectionMap hx)
  have e := Derives.identitySubLaw (transportGeneric ht.termFamily hx hs)
    (.subTm ht (pathProjection hx)) (.root hx)
  apply Derives.eqTrans e
  exact .congruence (.inr .identity)
    ![.ty Γ, .tm Γ (Contextual.subTy B (Contextual.sectionSub Γ A x)),
      .tm Γ (Contextual.subTy B (Contextual.sectionSub Γ A x))]
    e.eqOperands.2 (.identity hs hs)
    (Fin.cases (transportRoot ht.termFamily hx)
      (Fin.cases (transportGenericRoot ht.termFamily hx hs)
        (Fin.cases (subTmComposeAlong ht (pathProjection hx) (.root hx) (rootProjection hx))
          (fun i => nomatch i))))

def apdBranch (ht : Derives Ξ (.has (.tm (Contextual.extend Γ A) B) t))
    (hx : Derives Ξ (.has (.tm Γ A) x)) :
    Derives Ξ (.has (.tm Γ (Contextual.subTy (Contextual.apdMotive Γ A B x t) (Contextual.root A x)))
      (Contextual.apdBranch Γ A B x t)) :=
  .convert (.reflexivity (.subTm ht (sectionMap hx))) (.eqSymm (apdMotiveRoot ht hx))

def apdMotiveEndpoint (ht : Derives Ξ (.has (.tm (Contextual.extend Γ A) B) t))
    (hx : Derives Ξ (.has (.tm Γ A) x)) (hy : Derives Ξ (.has (.tm Γ A) y))
    (hp : Derives Ξ (.has (.tm Γ (Contextual.identity A x y)) p)) :
    Derives Ξ (.eq (.ty Γ)
      (Contextual.subTy (Contextual.apdMotive Γ A B x t) (Contextual.endpoint Γ A x y p))
      (Contextual.identity (Contextual.subTy B (Contextual.sectionSub Γ A y))
        (Contextual.transport Γ A B x y p (Contextual.subTm t (Contextual.sectionSub Γ A x)))
        (Contextual.subTm t (Contextual.sectionSub Γ A y)))) := by
  have hs := Derives.subTm ht (sectionMap hx)
  have hl := transport ht.termFamily hx hy hp hs
  have hr := Derives.subTm ht (sectionMap hy)
  have e := Derives.identitySubLaw (transportGeneric ht.termFamily hx hs)
    (.subTm ht (pathProjection hx)) (endpoint hx hy hp)
  apply Derives.eqTrans e
  exact .congruence (.inr .identity)
    ![.ty Γ, .tm Γ (Contextual.subTy B (Contextual.sectionSub Γ A y)),
      .tm Γ (Contextual.subTy B (Contextual.sectionSub Γ A y))]
    e.eqOperands.2 (.identity hl hr)
    (Fin.cases (transportEndpoint ht.termFamily hx hy hp)
      (Fin.cases (.eqRefl hl)
        (Fin.cases (subTmComposeAlong ht (pathProjection hx) (endpoint hx hy hp)
          (endpointProjection hx hy hp)) (fun i => nomatch i))))

/-- The selected dependent action uses J and retains its witness expression. -/
def apd (ht : Derives Ξ (.has (.tm (Contextual.extend Γ A) B) t))
    (hx : Derives Ξ (.has (.tm Γ A) x)) (hy : Derives Ξ (.has (.tm Γ A) y))
    (hp : Derives Ξ (.has (.tm Γ (Contextual.identity A x y)) p)) :
    Derives Ξ (.has (.tm Γ
      (Contextual.identity (Contextual.subTy B (Contextual.sectionSub Γ A y))
        (Contextual.transport Γ A B x y p (Contextual.subTm t (Contextual.sectionSub Γ A x)))
        (Contextual.subTm t (Contextual.sectionSub Γ A y))))
      (Contextual.apd Γ A B x y p t)) :=
  .convert (.subTm (basedJ hx (apdMotive ht hx) (apdBranch ht hx)) (endpoint hx hy hp))
    (apdMotiveEndpoint ht hx hy hp)

end
end Derives
end SquareKit.Internal.DependentJudgments.Contextual.Reference

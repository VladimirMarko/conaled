import SquareKit.Internal.DependentJudgments.ReferenceSubstitution

/-! Typed derived constructions for explicit finite dependent contexts. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Reference
open GuardedTheory
variable {V : Type} {Ξ : List (Declaration V)}
variable {Γ Δ A σ τ t : Expression V}
namespace Derives

noncomputable def subTyCongruence (hA : Derives Ξ (.has (.ty Γ) A))
    (e : Derives Ξ (.eq (.sub Δ Γ) σ τ)) :
    Derives Ξ (.eq (.ty Δ) (Contextual.subTy A σ) (Contextual.subTy A τ)) :=
  .congruence (.inl .subTy) ![.ty Γ, .sub Δ Γ]
    (.subTy hA e.eqOperands.1) (.subTy hA e.eqOperands.2)
    (Fin.cases (.eqRefl hA) (Fin.cases e (fun i => nomatch i)))

noncomputable def lift (hA : Derives Ξ (.has (.ty Γ) A))
    (hs : Derives Ξ (.has (.sub Δ Γ) σ)) :
    Derives Ξ (.has (.sub (Contextual.extend Δ (Contextual.subTy A σ)) (Contextual.extend Γ A)) (liftSyntax Δ A σ)) := by
  have hB := Derives.subTy hA hs
  have hw := Derives.weaken hB
  have hv := Derives.generic hB
  exact .pair hA (.comp hs hw) (.convert hv (.subTyComp hA hs hw))

noncomputable def genericPairBeta (hA : Derives Ξ (.has (.ty Γ) A))
    (hs : Derives Ξ (.has (.sub Δ Γ) σ))
    (ht : Derives Ξ (.has (.tm Δ (Contextual.subTy A σ)) t)) :
    Derives Ξ (.eq (.tm Δ (Contextual.subTy A σ)) (Contextual.subTm (Contextual.generic Γ A) (Contextual.pair A σ t)) t) := by
  have hp := Derives.pair hA hs ht
  have e := Derives.eqTrans (.subTyComp hA (.weaken hA) hp)
    (subTyCongruence hA (.weakenPair hA hs ht))
  exact .genericPair hA hs ht (.convert (.subTm (.generic hA) hp) e)

noncomputable def pairEtaLaw (hA : Derives Ξ (.has (.ty Γ) A))
    (hs : Derives Ξ (.has (.sub Δ (Contextual.extend Γ A)) σ)) :
    Derives Ξ (.eq (.sub Δ (Contextual.extend Γ A))
      (Contextual.pair A (Contextual.comp (Contextual.weaken Γ A) σ)
        (Contextual.subTm (Contextual.generic Γ A) σ)) σ) :=
  .pairEta hA hs (.pair hA (.comp (.weaken hA) hs)
    (.convert (.subTm (.generic hA) hs) (.subTyComp hA (.weaken hA) hs)))

private def TailData (Ξ : List (Declaration V)) : Claim V → Type
  | .tail Γ T => ∀ {Δ σ}, Derives Ξ (.has (.sub Δ Γ) σ) →
      Derives Ξ (.tail Δ (T.reindex Δ σ)) ×
      Derives Ξ (.has (.sub ((T.reindex Δ σ).total Δ) (T.total Γ)) (T.map Δ σ))
  | _ => PUnit

private noncomputable def tailData {c : Claim V} (h : Derives Ξ c) : TailData Ξ c := by
  induction h <;> try exact PUnit.unit
  case nil hΓ _ =>
    intro Δ σ hs
    exact ⟨.nil hs.subContexts.1, hs⟩
  case cons hA hT _ ih =>
    intro Δ σ hs
    have r := ih (lift hA hs)
    exact ⟨.cons (.subTy hA hs) r.1, r.2⟩

noncomputable def reindexTail {T : Tail V} (hT : Derives Ξ (.tail Γ T))
    (hs : Derives Ξ (.has (.sub Δ Γ) σ)) :
    Derives Ξ (.tail Δ (T.reindex Δ σ)) := (tailData hT hs).1

noncomputable def tailMap {T : Tail V} (hT : Derives Ξ (.tail Γ T))
    (hs : Derives Ξ (.has (.sub Δ Γ) σ)) :
    Derives Ξ (.has (.sub ((T.reindex Δ σ).total Δ) (T.total Γ)) (T.map Δ σ)) :=
  (tailData hT hs).2

noncomputable def branchMapping {x : Expression V} {T : Tail V}
    (hx : Derives Ξ (.has (.tm Γ A) x)) (hT : Derives Ξ (.tail (Contextual.path A x) T))
    (hs : Derives Ξ (.has (.sub Δ Γ) σ)) :
    Derives Ξ (.has (.sub ((T.alongPath A x σ).rootDomain Δ (Contextual.subTy A σ) (Contextual.subTm x σ))
      (T.rootDomain Γ A x)) (Contextual.branchMap A x (T.code (Contextual.path A x)) σ)) :=
  .branchMap hx hT hs
    (.tailTotal (reindexTail (reindexTail hT (.pathSub hx hs)) (.root (.subTm hx hs))))
    (.tailTotal (reindexTail hT (.root hx)))

noncomputable def branchCommutingSquare {x : Expression V} {T : Tail V}
    (hx : Derives Ξ (.has (.tm Γ A) x)) (hT : Derives Ξ (.tail (Contextual.path A x) T))
    (hs : Derives Ξ (.has (.sub Δ Γ) σ)) :
    Derives Ξ (.eq (.sub ((T.alongPath A x σ).rootDomain Δ (Contextual.subTy A σ) (Contextual.subTm x σ))
      (T.total (Contextual.path A x)))
      (Contextual.comp (T.alongPathMap A x σ)
        ((T.alongPath A x σ).map Δ (Contextual.root (Contextual.subTy A σ) (Contextual.subTm x σ))))
      (Contextual.comp (T.map Γ (Contextual.root A x))
        (Contextual.branchMap A x (T.code (Contextual.path A x)) σ))) :=
  .branchSquare hx hT hs
    (.comp (tailMap hT (.pathSub hx hs))
      (tailMap (reindexTail hT (.pathSub hx hs)) (.root (.subTm hx hs))))
    (.comp (tailMap hT (.root hx)) (branchMapping hx hT hs))

noncomputable def jNaturality {x D d : Expression V} {T : Tail V}
    (hx : Derives Ξ (.has (.tm Γ A) x)) (hT : Derives Ξ (.tail (Contextual.path A x) T))
    (hD : Derives Ξ (.has (.ty (T.total (Contextual.path A x))) D))
    (hd : Derives Ξ (.has (.tm (T.rootDomain Γ A x) (Contextual.subTy D (T.map Γ (Contextual.root A x)))) d))
    (hs : Derives Ξ (.has (.sub Δ Γ) σ)) :
    Derives Ξ (.eq (.tm ((T.alongPath A x σ).total (Contextual.path (Contextual.subTy A σ) (Contextual.subTm x σ)))
      (Contextual.subTy D (T.alongPathMap A x σ)))
      (Contextual.subTm (Contextual.j A x (T.code (Contextual.path A x)) D d) (T.alongPathMap A x σ))
      (Contextual.j (Contextual.subTy A σ) (Contextual.subTm x σ)
        ((T.alongPath A x σ).code (Contextual.path (Contextual.subTy A σ) (Contextual.subTm x σ)))
        (Contextual.subTy D (T.alongPathMap A x σ))
        (Contextual.subTm d (Contextual.branchMap A x (T.code (Contextual.path A x)) σ)))) := by
  have hT' := reindexTail hT (.pathSub hx hs)
  have hm := tailMap hT (.pathSub hx hs)
  have hr := tailMap hT (.root hx)
  have hr' := tailMap hT' (.root (.subTm hx hs))
  have hb := branchMapping hx hT hs
  have e := Derives.eqTrans (.subTyComp hD hr hb)
    (.eqTrans (subTyCongruence hD (.eqSymm (branchCommutingSquare hx hT hs)))
      (.eqSymm (.subTyComp hD hm hr')))
  exact .jSub hx hT hD hd hs (.subTm (.j hx hT hD hd) hm)
    (.j (.subTm hx hs) hT' (.subTy hD hm) (.convert (.subTm hd hb) e))

noncomputable def jComputation {x D d : Expression V} {T : Tail V}
    (hx : Derives Ξ (.has (.tm Γ A) x)) (hT : Derives Ξ (.tail (Contextual.path A x) T))
    (hD : Derives Ξ (.has (.ty (T.total (Contextual.path A x))) D))
    (hd : Derives Ξ (.has (.tm ((T.reindex Γ (Contextual.root A x)).total Γ)
      (Contextual.subTy D (T.map Γ (Contextual.root A x)))) d)) :
    Derives Ξ (.eq (.tm ((T.reindex Γ (Contextual.root A x)).total Γ)
      (Contextual.subTy D (T.map Γ (Contextual.root A x))))
      (Contextual.subTm (Contextual.j A x (T.code (Contextual.path A x)) D d) (T.map Γ (Contextual.root A x))) d) :=
  .jBeta hx hT hD hd (.subTm (.j hx hT hD hd) (tailMap hT (.root hx)))

end Derives
end SquareKit.Internal.DependentJudgments.Contextual.Reference

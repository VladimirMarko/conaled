import SquareKit.Internal.DependentJudgments.LeftConcatJReindex

/-! Fresh object substitution of the complete left-path operation. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
open GuardedTheory LeftConcatFrame
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ Δ A x y z p q σ : Expression V}
namespace LeftConcatReindex
variable (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y) (hz : Tm (Ω := Ω) Γ A z)
  (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p)
  (hq : Tm (Ω := Ω) Γ (Contextual.identity A y z) q) (hs : Sub (Ω := Ω) Δ Γ σ)
def pathArgument := (hp.substitute hs).convert (hx.identitySub hy hs)
def finalArgument := (hq.substitute hs).convert (hy.identitySub hz hs)
def zSquare : Equal (Ω := Ω)
    (comp (atZ (Γ := Γ) (A := A) (x := x) (σ := σ))
      (LeftConcatArguments.atZ Δ (subTy A σ) (subTm x σ) (subTm y σ) (subTm z σ) (subTm p σ)))
    (comp (LeftConcatArguments.atZ Γ A x y z p) σ) := by
  have hτ := (hx.substitute hs).endpoint (hy.substitute hs) (pathArgument hx hy hp hs)
  have hv := (LeftConcatArguments.zArgument (hx.substitute hs) (hy.substitute hs)
    (hz.substitute hs) (pathArgument hx hy hp hs)).convert
      (Equal.subTy (pathTypeSub hx hs).symmetric (.reflexive _))
  exact (Equal.comp (.reflexive _)
    (Equal.pair (pathTypeSub hx hs).symmetric (.reflexive _) (.reflexive _))).transitive
      (((hx.pathSub hs).liftPair (pathTypeTyped hx) hτ hv).transitive
        ((Equal.pair (.reflexive _) (hx.pathSubEndpoint hy hp hs) (.reflexive _)).transitive
          ((pathTypeTyped hx).pairComp (hx.endpoint hy hp)
            (LeftConcatArguments.zArgument hx hy hz hp) hs).symmetric))
def qSquare : Equal (Ω := Ω)
    (comp (atQ (Γ := Γ) (Δ := Δ) (A := A) (x := x) (σ := σ))
      (LeftConcatArguments.atQ Δ (subTy A σ) (subTm x σ) (subTm y σ) (subTm z σ) (subTm p σ) (subTm q σ)))
    (comp (LeftConcatArguments.atQ Γ A x y z p q) σ) := by
  have hτ := LeftConcatArguments.atZTyped (hx.substitute hs) (hy.substitute hs)
    (hz.substitute hs) (pathArgument hx hy hp hs)
  have hv := (LeftConcatArguments.qArgument (hx.substitute hs) (hy.substitute hs)
    (hz.substitute hs) (pathArgument hx hy hp hs) (finalArgument hy hz hq hs)).convert
      (Equal.subTy (qTypeSub hx hs).symmetric (.reflexive _))
  exact (Equal.comp (.reflexive _)
    (Equal.pair (qTypeSub hx hs).symmetric (.reflexive _) (.reflexive _))).transitive
      (((atZTyped hx hs).liftPair (qTypeTyped hx) hτ hv).transitive
        ((Equal.pair (.reflexive _) (zSquare hx hy hz hp hs) (.reflexive _)).transitive
          ((qTypeTyped hx).pairComp (LeftConcatArguments.atZTyped hx hy hz hp)
            (LeftConcatArguments.qArgument hx hy hz hp hq) hs).symmetric))
def fresh : Equal (Ω := Ω) (subTm (leftConcat Γ A x y z p q) σ)
    (leftConcat Δ (subTy A σ) (subTm x σ) (subTm y σ) (subTm z σ) (subTm p σ) (subTm q σ)) :=
  ((genericConcat hx).subComp (LeftConcatArguments.atQTyped hx hy hz hp hq) hs).transitive
    ((Equal.subTm (.reflexive _) (qSquare hx hy hz hp hq hs).symmetric).transitive
      (((genericConcat hx).subComp (atQTyped hx hs)
        (LeftConcatArguments.atQTyped (hx.substitute hs) (hy.substitute hs) (hz.substitute hs)
          (pathArgument hx hy hp hs) (finalArgument hy hz hq hs))).symmetric.transitive
        (Equal.subTm (genericSub hx hs) (.reflexive _))))
end LeftConcatReindex
namespace Tm
def leftConcatSub (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y) (hz : Tm (Ω := Ω) Γ A z)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p)
    (hq : Tm (Ω := Ω) Γ (Contextual.identity A y z) q) (hs : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTm (TelescopePresentation.leftConcat Γ A x y z p q) σ)
      (TelescopePresentation.leftConcat Δ (subTy A σ) (subTm x σ) (subTm y σ) (subTm z σ) (subTm p σ) (subTm q σ)) :=
  LeftConcatReindex.fresh hx hy hz hp hq hs
end Tm
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation

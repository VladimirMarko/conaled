import SquareKit.Internal.DependentJudgments.LeftConcatenationBeta

/-! Generated source substitution equations for the left-J frame. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
open GuardedTheory LeftConcatFrame
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ Δ A x σ : Expression V}
namespace LeftConcatReindex
variable (hx : Tm (Ω := Ω) Γ A x) (hs : Sub (Ω := Ω) Δ Γ σ)
def pathTypeSub : Equal (Ω := Ω)
    (subTy (pathType Γ A x) (pathSub A x σ))
    (pathType Δ (subTy A σ) (subTm x σ)) :=
  ((hx.family.substitute hx.family.weaken).subComp hx.pathProjection (hx.pathSub hs)).transitive
    ((Equal.subTy (.reflexive _) (hx.pathSubProjection hs)).transitive
      (((hx.family.substitute hx.family.weaken).subComp (hs.lift hx.family)
        (hx.substitute hs).pathProjection).symmetric.transitive
        (Equal.subTy (hx.family.weakenLift hx.family hs) (.reflexive _))))
def fixedSub : Equal (Ω := Ω)
    (subTm (fixed Γ A x) (pathSub A x σ))
    (fixed Δ (subTy A σ) (subTm x σ)) :=
  ((hx.substitute hx.family.weaken).subComp hx.pathProjection (hx.pathSub hs)).transitive
    ((Equal.subTm (.reflexive _) (hx.pathSubProjection hs)).transitive
      (((hx.substitute hx.family.weaken).subComp (hs.lift hx.family)
        (hx.substitute hs).pathProjection).symmetric.transitive
        (Equal.subTm (hx.weakenLift hx.family hs) (.reflexive _))))
def movingSub : Equal (Ω := Ω)
    (subTm (moving Γ A x) (pathSub A x σ))
    (moving Δ (subTy A σ) (subTm x σ)) :=
  (hx.family.generic.subComp hx.pathProjection (hx.pathSub hs)).transitive
    ((Equal.subTm (.reflexive _) (hx.pathSubProjection hs)).transitive
      ((hx.family.generic.subComp (hs.lift hx.family)
        (hx.substitute hs).pathProjection).symmetric.transitive
        (Equal.subTm (hs.liftGeneric hx.family) (.reflexive _))))
abbrev atZ := liftSyntax (path (subTy A σ) (subTm x σ)) (pathType Γ A x) (pathSub A x σ)
def atZTyped : Sub (Ω := Ω) (withZ Δ (subTy A σ) (subTm x σ)) (withZ Γ A x)
    (atZ (Γ := Γ) (A := A) (x := x) (σ := σ)) :=
  ((hx.pathSub hs).lift (pathTypeTyped hx)).resource
    (Equal.extend (.reflexive _) (pathTypeSub hx hs))
def zTypeSub : Equal (Ω := Ω)
    (subTy (zType Γ A x) (atZ (Γ := Γ) (A := A) (x := x) (σ := σ)))
    (zType Δ (subTy A σ) (subTm x σ)) :=
  ((pathTypeTyped hx).weakenLift (pathTypeTyped hx) (hx.pathSub hs)).transitive
    (Equal.subTy (pathTypeSub hx hs) (Equal.weaken (.reflexive _) (pathTypeSub hx hs)))
def fixedZSub : Equal (Ω := Ω)
    (subTm (fixedZ Γ A x) (atZ (Γ := Γ) (A := A) (x := x) (σ := σ)))
    (fixedZ Δ (subTy A σ) (subTm x σ)) :=
  ((fixedTyped hx).weakenLift (pathTypeTyped hx) (hx.pathSub hs)).transitive
    (Equal.subTm (fixedSub hx hs) (Equal.weaken (.reflexive _) (pathTypeSub hx hs)))
def movingZSub : Equal (Ω := Ω)
    (subTm (movingZ Γ A x) (atZ (Γ := Γ) (A := A) (x := x) (σ := σ)))
    (movingZ Δ (subTy A σ) (subTm x σ)) :=
  ((movingTyped hx).weakenLift (pathTypeTyped hx) (hx.pathSub hs)).transitive
    (Equal.subTm (movingSub hx hs) (Equal.weaken (.reflexive _) (pathTypeSub hx hs)))
def zSub : Equal (Ω := Ω)
    (subTm (z Γ A x) (atZ (Γ := Γ) (A := A) (x := x) (σ := σ)))
    (z Δ (subTy A σ) (subTm x σ)) :=
  ((hx.pathSub hs).liftGeneric (pathTypeTyped hx)).transitive
    (Equal.generic (.reflexive _) (pathTypeSub hx hs))
def qTypeSub : Equal (Ω := Ω)
    (subTy (qType Γ A x) (atZ (Γ := Γ) (A := A) (x := x) (σ := σ)))
    (qType Δ (subTy A σ) (subTm x σ)) :=
  ((movingZTyped hx).identitySub (zTyped hx) (atZTyped hx hs)).transitive
    (Equal.identity (zTypeSub hx hs) (movingZSub hx hs) (zSub hx hs))

abbrev atQ := liftSyntax (withZ Δ (subTy A σ) (subTm x σ)) (qType Γ A x)
  (atZ (Γ := Γ) (A := A) (x := x) (σ := σ))
def atQTyped : Sub (Ω := Ω) (withQ Δ (subTy A σ) (subTm x σ)) (withQ Γ A x)
    (atQ (Γ := Γ) (Δ := Δ) (A := A) (x := x) (σ := σ)) :=
  ((atZTyped hx hs).lift (qTypeTyped hx)).resource
    (Equal.extend (.reflexive _) (qTypeSub hx hs))
def finalTypeSub : Equal (Ω := Ω)
    (subTy (finalType Γ A x) (atQ (Γ := Γ) (Δ := Δ) (A := A) (x := x) (σ := σ)))
    (finalType Δ (subTy A σ) (subTm x σ)) :=
  ((zTyped hx).family.weakenLift (qTypeTyped hx) (atZTyped hx hs)).transitive
    (Equal.subTy (zTypeSub hx hs) (Equal.weaken (.reflexive _) (qTypeSub hx hs)))
def finalFixedSub : Equal (Ω := Ω)
    (subTm (finalFixed Γ A x) (atQ (Γ := Γ) (Δ := Δ) (A := A) (x := x) (σ := σ)))
    (finalFixed Δ (subTy A σ) (subTm x σ)) :=
  ((fixedZTyped hx).weakenLift (qTypeTyped hx) (atZTyped hx hs)).transitive
    (Equal.subTm (fixedZSub hx hs) (Equal.weaken (.reflexive _) (qTypeSub hx hs)))
def finalMovingSub : Equal (Ω := Ω)
    (subTm (finalMoving Γ A x) (atQ (Γ := Γ) (Δ := Δ) (A := A) (x := x) (σ := σ)))
    (finalMoving Δ (subTy A σ) (subTm x σ)) :=
  ((movingZTyped hx).weakenLift (qTypeTyped hx) (atZTyped hx hs)).transitive
    (Equal.subTm (movingZSub hx hs) (Equal.weaken (.reflexive _) (qTypeSub hx hs)))
def finalZSub : Equal (Ω := Ω)
    (subTm (finalZ Γ A x) (atQ (Γ := Γ) (Δ := Δ) (A := A) (x := x) (σ := σ)))
    (finalZ Δ (subTy A σ) (subTm x σ)) :=
  ((zTyped hx).weakenLift (qTypeTyped hx) (atZTyped hx hs)).transitive
    (Equal.subTm (zSub hx hs) (Equal.weaken (.reflexive _) (qTypeSub hx hs)))
def qSub : Equal (Ω := Ω)
    (subTm (q Γ A x) (atQ (Γ := Γ) (Δ := Δ) (A := A) (x := x) (σ := σ)))
    (q Δ (subTy A σ) (subTm x σ)) :=
  ((atZTyped hx hs).liftGeneric (qTypeTyped hx)).transitive
    (Equal.generic (.reflexive _) (qTypeSub hx hs))
def motiveSub : Equal (Ω := Ω)
    (subTy (motive Γ A x) (atQ (Γ := Γ) (Δ := Δ) (A := A) (x := x) (σ := σ)))
    (motive Δ (subTy A σ) (subTm x σ)) :=
  ((finalFixedTyped hx).identitySub (finalZTyped hx) (atQTyped hx hs)).transitive
    (Equal.identity (finalTypeSub hx hs) (finalFixedSub hx hs) (finalZSub hx hs))

def presentedMap : Equal (Ω := Ω)
    ((LeftConcatFrame.tail Γ A x).map (path (subTy A σ) (subTm x σ)) (pathSub A x σ))
    (atQ (Γ := Γ) (Δ := Δ) (A := A) (x := x) (σ := σ)) :=
  Equal.liftSyntax (Equal.extend (.reflexive _) (pathTypeSub hx hs)) (.reflexive _) (.reflexive _)
def presentedCode : Equal (Ω := Ω)
    (((LeftConcatFrame.tail Γ A x).reindex (path (subTy A σ) (subTm x σ)) (pathSub A x σ)).code
      (path (subTy A σ) (subTm x σ)))
    ((LeftConcatFrame.tail Δ (subTy A σ) (subTm x σ)).code (path (subTy A σ) (subTm x σ))) :=
  Equal.telCons (pathTypeSub hx hs) (Equal.telCons (qTypeSub hx hs)
    (Equal.telNil (Equal.extend (Equal.extend (.reflexive _) (pathTypeSub hx hs)) (qTypeSub hx hs))))
def pathTailMapEq : Equal (Ω := Ω)
    (pathTailMap A x ((LeftConcatFrame.tail Γ A x).code (path A x)) σ)
    (atQ (Γ := Γ) (Δ := Δ) (A := A) (x := x) (σ := σ)) := by
  have e := Derivation.rule (T := theory) (Sum.inr (.pathTailMapDef 2))
    ![Γ, A, x, (LeftConcatFrame.tail Γ A x).code (path A x), Δ, σ]
    (Fin.cases (by simpa [Tm, theory, extraRule] using hx)
      (Fin.cases (by simpa [Reference.Target, theory, extraRule, LeftConcatFrame.tail, Reference.Tail.length] using (tailTyped hx).typing)
        (Fin.cases (by simpa [Sub, theory, extraRule] using hs) (fun i => nomatch i))))
  have h : Equal (Ω := Ω)
      (pathTailMap A x ((LeftConcatFrame.tail Γ A x).code (path A x)) σ)
      (tailMap ((LeftConcatFrame.tail Γ A x).code (path A x)) (pathSub A x σ)) := by
    simpa [Equal, theory, extraRule, Atom.subst] using e
  exact h.transitive (((tailTyped hx).map_eq (hx.substitute hs).path (hx.pathSub hs)).transitive
    (presentedMap hx hs))
def pathTailEq : Equal (Ω := Ω)
    (pathTail A x ((LeftConcatFrame.tail Γ A x).code (path A x)) σ)
    ((LeftConcatFrame.tail Δ (subTy A σ) (subTm x σ)).code (path (subTy A σ) (subTm x σ))) := by
  have e := Derivation.rule (T := theory) (Sum.inr (.pathTailDef 2))
    ![Γ, A, x, (LeftConcatFrame.tail Γ A x).code (path A x), Δ, σ]
    (Fin.cases (by simpa [Tm, theory, extraRule] using hx)
      (Fin.cases (by simpa [Reference.Target, theory, extraRule, LeftConcatFrame.tail, Reference.Tail.length] using (tailTyped hx).typing)
        (Fin.cases (by simpa [Sub, theory, extraRule] using hs) (fun i => nomatch i))))
  have h : Equal (Ω := Ω)
      (pathTail A x ((LeftConcatFrame.tail Γ A x).code (path A x)) σ)
      (pullback ((LeftConcatFrame.tail Γ A x).code (path A x)) (pathSub A x σ)) := by
    simpa [Equal, theory, extraRule, Atom.subst] using e
  exact h.transitive (((tailTyped hx).pullback_eq (hx.substitute hs).path (hx.pathSub hs)).transitive
    (presentedCode hx hs))

end LeftConcatReindex
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation

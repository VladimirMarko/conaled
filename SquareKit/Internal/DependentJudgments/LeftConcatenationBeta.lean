import SquareKit.Internal.DependentJudgments.LeftConcatenation

/-! Source computation of left concatenation at the reflexive first path.
The root argument environment is constructed by dependent pairing. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ A x z q : Expression V}
namespace LeftConcatBeta
open LeftConcatFrame LeftConcatArguments
variable (hx : Tm (Ω := Ω) Γ A x) (hz : Tm (Ω := Ω) Γ A z)
  (hq : Tm (Ω := Ω) Γ (Contextual.identity A x z) q)

abbrev zArgs (Γ A x z : Expression V) :=
  Contextual.pair (subTy (pathType Γ A x) (root A x)) (identitySub Γ) z

def zTypeRoot : Equal (Ω := Ω) (subTy (pathType Γ A x) (root A x)) A :=
  (Equal.subTy (.reflexive _) hx.rootDef).transitive
    (pathTypeAt hx hx hx.reflexivity)
def zArg := hz.convert
  (((pathTypeTyped hx).substitute hx.root).subId.transitive (zTypeRoot hx)).symmetric
def zArgsTyped := Sub.pair ((pathTypeTyped hx).substitute hx.root) hx.family.context.identity (zArg hx hz)
def zSquare : Equal (Ω := Ω)
    (comp (liftSyntax Γ (pathType Γ A x) (root A x)) (zArgs Γ A x z))
    (atZ Γ A x x z (Contextual.reflexivity A x)) :=
  (hx.root.liftPair (pathTypeTyped hx) hx.family.context.identity (zArg hx hz)).transitive
    (Equal.pair (.reflexive _) (hx.root.idRight.transitive hx.rootDef) (.reflexive _))

def qTypeRoot : Equal (Ω := Ω)
    (subTy (subTy (qType Γ A x) (liftSyntax Γ (pathType Γ A x) (root A x))) (zArgs Γ A x z))
    (Contextual.identity A x z) :=
  ((qTypeTyped hx).subComp (rootLiftZ hx) (zArgsTyped hx hz)).transitive
    ((Equal.subTy (.reflexive _) (zSquare hx hz)).transitive
      (qTypeAt hx hx hz hx.reflexivity))
def qArg := hq.convert (qTypeRoot hx hz).symmetric
abbrev qArgs (Γ A x z q : Expression V) :=
  Contextual.pair (subTy (qType Γ A x) (liftSyntax Γ (pathType Γ A x) (root A x)))
    (zArgs Γ A x z) q

def argsTyped := Sub.pair ((qTypeTyped hx).substitute (rootLiftZ hx)) (zArgsTyped hx hz) (qArg hx hz hq)
def square : Equal (Ω := Ω)
    (comp ((LeftConcatFrame.tail Γ A x).map Γ (root A x)) (qArgs Γ A x z q))
    (atQ Γ A x x z (Contextual.reflexivity A x) q) :=
  ((rootLiftZ hx).liftPair (qTypeTyped hx) (zArgsTyped hx hz) (qArg hx hz hq)).transitive
    (Equal.pair (.reflexive _) (zSquare hx hz) (.reflexive _))

def qAt : Equal (Ω := Ω)
    (subTm (LeftConcatFrame.q Γ A x) (atQ Γ A x x z (Contextual.reflexivity A x) q)) q :=
  (qTypeTyped hx).variablePair (atZTyped hx hx hz hx.reflexivity) (qArgument hx hx hz hx.reflexivity hq)

/-- This generated equation observes the selected q itself. -/
def computation : Equal (Ω := Ω)
    (TelescopePresentation.leftConcat Γ A x x z (Contextual.reflexivity A x) q) q := by
  have hj := genericConcat hx
  have hr := rootLiftQ hx
  have ha := argsTyped hx hz hq
  have js := hj.subComp hr ha
  have qs := (qTyped hx).subComp hr ha
  exact (Equal.subTm (.reflexive _) (square hx hz hq).symmetric).transitive
    (js.symmetric.transitive
      ((Equal.subTm (genericBeta hx) (.reflexive _)).transitive
        (qs.transitive ((Equal.subTm (.reflexive _) (square hx hz hq)).transitive (qAt hx hz hq)))))
end LeftConcatBeta

def Tm.leftConcatReflLeft (hx : Tm (Ω := Ω) Γ A x) (hz : Tm (Ω := Ω) Γ A z)
    (hq : Tm (Ω := Ω) Γ (Contextual.identity A x z) q) : Equal (Ω := Ω)
    (TelescopePresentation.leftConcat Γ A x x z (Contextual.reflexivity A x) q) q :=
  LeftConcatBeta.computation hx hz hq
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation

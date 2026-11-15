import SquareKit.Internal.DependentJudgments.PresentedPath
import SquareKit.Internal.DependentJudgments.PresentedSoundness
import Examples.GuardedLeftConcatenation

/-! Independent #108 attempt. The upstream inv/inv-inv declarations are from
agda-unimath 75518656f287c203b41cb7f71df46e02b987a084, MIT, copyright (c) 2022
Egbert Maarten Rijke. The full notice is retained in ../inputs/upstream/LICENSE.md. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation.IndependentInv
open GuardedTheory LeftConcatFrame
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ Δ A x y p σ D d : Expression V}

-- Generic public based-J operations imported into the named presentation theory.
def basedTyped (hx : Tm (Ω := Ω) Γ A x) (hD : Ty (Ω := Ω) (path A x) D)
    (hd : Tm (Ω := Ω) Γ (subTy D (root A x)) d) :
    Tm (Ω := Ω) (path A x) D (basedJ A x D d) :=
  ternary (Contextual.Tm.basedJ (Γ := Γ) (.hypothesis (by simp)) (.hypothesis (by simp))
    (.hypothesis (by simp))) hx hD hd

def basedBeta (hx : Tm (Ω := Ω) Γ A x) (hD : Ty (Ω := Ω) (path A x) D)
    (hd : Tm (Ω := Ω) Γ (subTy D (root A x)) d) :
    Equal (Ω := Ω) (subTm (basedJ A x D d) (root A x)) d :=
  ternary (Contextual.Tm.basedJBeta (Γ := Γ) (.hypothesis (by simp)) (.hypothesis (by simp))
    (.hypothesis (by simp))) hx hD hd

def basedSub (hx : Tm (Ω := Ω) Γ A x) (hD : Ty (Ω := Ω) (path A x) D)
    (hd : Tm (Ω := Ω) Γ (subTy D (root A x)) d) (hs : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTm (basedJ A x D d) (pathSub A x σ))
      (basedJ (subTy A σ) (subTm x σ) (subTy D (pathSub A x σ)) (subTm d σ)) :=
  quaternary (Contextual.Tm.basedJSub (Γ := Γ) (Δ := Δ) (.hypothesis (by simp)) (.hypothesis (by simp))
    (.hypothesis (by simp)) (.hypothesis (by simp))) hx hD hd hs

abbrev reverseMotive (Γ A x : Expression V) :=
  Contextual.identity (pathType Γ A x) (moving Γ A x) (fixed Γ A x)
abbrev reverseGeneric (Γ A x : Expression V) :=
  basedJ A x (reverseMotive Γ A x) (Contextual.reflexivity A x)
abbrev reverse (Γ A x y p : Expression V) :=
  subTm (reverseGeneric Γ A x) (Contextual.endpoint Γ A x y p)

def motiveTyped (hx : Tm (Ω := Ω) Γ A x) :
    Ty (Ω := Ω) (path A x) (reverseMotive Γ A x) :=
  (movingTyped hx).identity (fixedTyped hx)

def motiveRoot (hx : Tm (Ω := Ω) Γ A x) :
    Equal (Ω := Ω) (subTy (reverseMotive Γ A x) (root A x)) (Contextual.identity A x x) :=
  ((movingTyped hx).identitySub (fixedTyped hx) hx.root).transitive
    (Equal.identity (PresentedPath.pathTypeRoot hx) (movingRoot hx) (fixedRoot hx))

def branchTyped (hx : Tm (Ω := Ω) Γ A x) :
    Tm (Ω := Ω) Γ (subTy (reverseMotive Γ A x) (root A x)) (Contextual.reflexivity A x) :=
  hx.reflexivity.convert (motiveRoot hx).symmetric

def genericTyped (hx : Tm (Ω := Ω) Γ A x) :
    Tm (Ω := Ω) (path A x) (reverseMotive Γ A x) (reverseGeneric Γ A x) :=
  basedTyped hx (motiveTyped hx) (branchTyped hx)

def reverseTyped (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) :
    Tm (Ω := Ω) Γ (Contextual.identity A y x) (reverse Γ A x y p) :=
  ((genericTyped hx).substitute (hx.endpoint hy hp)).convert
    (((movingTyped hx).identitySub (fixedTyped hx) (hx.endpoint hy hp)).transitive
      (Equal.identity (LeftConcatArguments.pathTypeAt hx hy hp)
        (LeftConcatArguments.movingAt hx hy hp) (LeftConcatArguments.fixedAt hx hy hp)))

def reverseRefl (hx : Tm (Ω := Ω) Γ A x) :
    Equal (Ω := Ω) (reverse Γ A x x (Contextual.reflexivity A x)) (Contextual.reflexivity A x) :=
  (Equal.subTm (.reflexive _) hx.rootDef.symmetric).transitive
    (basedBeta hx (motiveTyped hx) (branchTyped hx))

end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation.IndependentInv

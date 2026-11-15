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


def genericSub (hx : Tm (Ω := Ω) Γ A x) (hs : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTm (reverseGeneric Γ A x) (pathSub A x σ))
      (reverseGeneric Δ (subTy A σ) (subTm x σ)) :=
  (basedSub hx (motiveTyped hx) (branchTyped hx) hs).transitive
    (Equal.j (.reflexive _) (.reflexive _) (.reflexive _)
      (((movingTyped hx).identitySub (fixedTyped hx) (hx.pathSub hs)).transitive
        (Equal.identity (LeftConcatReindex.pathTypeSub hx hs)
          (LeftConcatReindex.movingSub hx hs) (LeftConcatReindex.fixedSub hx hs)))
      (hx.reflSub hs))

def reverseSub (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) (hs : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTm (reverse Γ A x y p) σ)
      (reverse Δ (subTy A σ) (subTm x σ) (subTm y σ) (subTm p σ)) :=
  ((genericTyped hx).subComp (hx.endpoint hy hp) hs).transitive
    ((Equal.subTm (.reflexive _) (hx.pathSubEndpoint hy hp hs).symmetric).transitive
      (((genericTyped hx).subComp (hx.pathSub hs)
        ((hx.substitute hs).endpoint (hy.substitute hs)
          ((hp.substitute hs).convert (hx.identitySub hy hs)))).symmetric.transitive
        (Equal.subTm (genericSub hx hs) (.reflexive _))))

theorem reflexivity_subst {W : Type} (s : V → Expression W) (a x : Expression V) :
    (Contextual.reflexivity a x).subst s = Contextual.reflexivity (a.subst s) (x.subst s) := by
  apply congrArg (@FinitaryTerm.node signature.Operation signature.arity W (.inr .reflexivity))
  funext i
  fin_cases i <;> rfl

theorem reverse_subst {W : Type} (s : V → Expression W) (g a x y p : Expression V) :
    (reverse g a x y p).subst s = reverse (g.subst s) (a.subst s) (x.subst s) (y.subst s) (p.subst s) := by
  simp only [reverse, reverseGeneric, reverseMotive, basedJ, pathType, moving, fixed,
    LeftConcatFrame.pathProjection, Contextual.endpoint, Contextual.pathFamily, Contextual.sectionSub,
    LeftConcatRecipe.subTm_subst, LeftConcatRecipe.subTy_subst, LeftConcatRecipe.path_subst,
    LeftConcatRecipe.telNil_subst, LeftConcatRecipe.pair_subst, LeftConcatRecipe.extend_subst,
    LeftConcatRecipe.weaken_subst, LeftConcatRecipe.generic_subst, LeftConcatRecipe.identity_subst,
    LeftConcatRecipe.identitySub_subst, LeftConcatRecipe.j_subst, reflexivity_subst]

def reverseCongr {g g' a a' x x' y y' p p' : Expression V}
    (hg : Equal (Ω := Ω) g g') (ha : Equal (Ω := Ω) a a')
    (hx : Equal (Ω := Ω) x x') (hy : Equal (Ω := Ω) y y') (hp : Equal (Ω := Ω) p p') :
    Equal (Ω := Ω) (reverse g a x y p) (reverse g' a' x' y' p') := by
  have e := Equal.recipe (reverse (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) : Expression (Fin 5))
    ![g,a,x,y,p] ![g',a',x',y',p']
    (Fin.cases hg (Fin.cases ha (Fin.cases hx (Fin.cases hy (Fin.cases hp (fun i => nomatch i))))))
  rw [reverse_subst, reverse_subst] at e
  simpa [Term.subst, Term.var, FinitaryTerm.bind] using e


abbrev doubled (Γ A x y p : Expression V) := reverse Γ A y x (reverse Γ A x y p)
def doubledTyped (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) :
    Tm (Ω := Ω) Γ (Contextual.identity A x y) (doubled Γ A x y p) :=
  reverseTyped hy hx (reverseTyped hx hy hp)
def doubledSub (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) (hs : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTm (doubled Γ A x y p) σ)
      (doubled Δ (subTy A σ) (subTm x σ) (subTm y σ) (subTm p σ)) :=
  (reverseSub hy hx (reverseTyped hx hy hp) hs).transitive
    (reverseCongr (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _)
      (reverseSub hx hy hp hs))
def doubledCongr {g g' a a' x x' y y' p p' : Expression V}
    (hg : Equal (Ω := Ω) g g') (ha : Equal (Ω := Ω) a a')
    (hx : Equal (Ω := Ω) x x') (hy : Equal (Ω := Ω) y y') (hp : Equal (Ω := Ω) p p') :
    Equal (Ω := Ω) (doubled g a x y p) (doubled g' a' x' y' p') :=
  reverseCongr hg ha hy hx (reverseCongr hg ha hx hy hp)
def doubledRefl (hx : Tm (Ω := Ω) Γ A x) :
    Equal (Ω := Ω) (doubled Γ A x x (Contextual.reflexivity A x)) (Contextual.reflexivity A x) :=
  (reverseCongr (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _)
    (reverseRefl hx)).transitive (reverseRefl hx)

open PresentedPath
abbrev genericDouble (Γ A x : Expression V) :=
  doubled (path A x) (pathType Γ A x) (fixed Γ A x) (moving Γ A x) (pathProof Γ A x)
abbrev involutionMotive (Γ A x : Expression V) :=
  Contextual.identity (Contextual.identity (pathType Γ A x) (fixed Γ A x) (moving Γ A x))
    (genericDouble Γ A x) (pathProof Γ A x)
def doubleTyped (hx : Tm (Ω := Ω) Γ A x) :=
  doubledTyped (fixedTyped hx) (movingTyped hx) (pathProofTyped hx)
def involutionMotiveTyped (hx : Tm (Ω := Ω) Γ A x) :
    Ty (Ω := Ω) (path A x) (involutionMotive Γ A x) :=
  (doubleTyped hx).identity (pathProofTyped hx)
def doubleRoot (hx : Tm (Ω := Ω) Γ A x) :
    Equal (Ω := Ω) (subTm (genericDouble Γ A x) (root A x)) (Contextual.reflexivity A x) :=
  (doubledSub (fixedTyped hx) (movingTyped hx) (pathProofTyped hx) hx.root).transitive
    ((doubledCongr (.reflexive _) (pathTypeRoot hx) (fixedRoot hx) (movingRoot hx)
      (pathProofRoot hx)).transitive (doubledRefl hx))
def involutionRoot (hx : Tm (Ω := Ω) Γ A x) :
    Equal (Ω := Ω) (subTy (involutionMotive Γ A x) (root A x))
      (Contextual.identity (Contextual.identity A x x) (Contextual.reflexivity A x) (Contextual.reflexivity A x)) :=
  ((doubleTyped hx).identitySub (pathProofTyped hx) hx.root).transitive
    (Equal.identity
      (((fixedTyped hx).identitySub (movingTyped hx) hx.root).transitive
        (Equal.identity (pathTypeRoot hx) (fixedRoot hx) (movingRoot hx)))
      (doubleRoot hx) (pathProofRoot hx))
def involutionBranch (hx : Tm (Ω := Ω) Γ A x) :
    Tm (Ω := Ω) Γ (subTy (involutionMotive Γ A x) (root A x))
      (Contextual.reflexivity (Contextual.identity A x x) (Contextual.reflexivity A x)) :=
  hx.reflexivity.reflexivity.convert (involutionRoot hx).symmetric
abbrev involutionGeneric (Γ A x : Expression V) :=
  basedJ A x (involutionMotive Γ A x)
    (Contextual.reflexivity (Contextual.identity A x x) (Contextual.reflexivity A x))
def involutionGenericTyped (hx : Tm (Ω := Ω) Γ A x) :
    Tm (Ω := Ω) (path A x) (involutionMotive Γ A x) (involutionGeneric Γ A x) :=
  basedTyped hx (involutionMotiveTyped hx) (involutionBranch hx)

def pathProofAt (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) :
    Equal (Ω := Ω) (subTm (pathProof Γ A x) (Contextual.endpoint Γ A x y p)) p :=
  hx.pathFamily.variablePair hy.section (hp.convert (hx.pathFamilySection hy).symmetric)
def doubleAt (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) :
    Equal (Ω := Ω) (subTm (genericDouble Γ A x) (Contextual.endpoint Γ A x y p))
      (doubled Γ A x y p) :=
  (doubledSub (fixedTyped hx) (movingTyped hx) (pathProofTyped hx) (hx.endpoint hy hp)).transitive
    (doubledCongr (.reflexive _) (LeftConcatArguments.pathTypeAt hx hy hp)
      (LeftConcatArguments.fixedAt hx hy hp) (LeftConcatArguments.movingAt hx hy hp)
      (pathProofAt hx hy hp))
def involutionAt (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) :
    Equal (Ω := Ω) (subTy (involutionMotive Γ A x) (Contextual.endpoint Γ A x y p))
      (Contextual.identity (Contextual.identity A x y) (doubled Γ A x y p) p) :=
  ((doubleTyped hx).identitySub (pathProofTyped hx) (hx.endpoint hy hp)).transitive
    (Equal.identity
      (((fixedTyped hx).identitySub (movingTyped hx) (hx.endpoint hy hp)).transitive
        (Equal.identity (LeftConcatArguments.pathTypeAt hx hy hp)
          (LeftConcatArguments.fixedAt hx hy hp) (LeftConcatArguments.movingAt hx hy hp)))
      (doubleAt hx hy hp) (pathProofAt hx hy hp))
abbrev involution (Γ A x y p : Expression V) :=
  subTm (involutionGeneric Γ A x) (Contextual.endpoint Γ A x y p)
/-- Generated arbitrary-path inv-inv, retaining the selected certificate. -/
def involutionTyped (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) :
    Tm (Ω := Ω) Γ (Contextual.identity (Contextual.identity A x y) (doubled Γ A x y p) p)
      (involution Γ A x y p) :=
  ((involutionGenericTyped hx).substitute (hx.endpoint hy hp)).convert (involutionAt hx hy hp)

end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation.IndependentInv

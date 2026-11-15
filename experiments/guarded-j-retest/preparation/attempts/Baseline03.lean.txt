import SquareKit.Internal.PathTransport.Authoring
import SquareKit.Internal.DependentJudgments.Sigma.Stability

namespace GuardedJRetest.BaselineReference
open SquareKit.Internal SquareKit.Internal.PathTransport Typed Authoring
universe u
variable {Γ : RawCtx} {γ : CtxCode.{u}} {A x : Expr} {a : TyCode γ}
  {ξ : TmCode γ a} {n : Nat} {Ξ : RawCtx} {T : TelCode (pathCode a ξ) n}
  {Q p : Expr} {q : TyCode (telTotal T)} {π : TmCode (telTotal T) q}
variable (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a) (hx : TmDeriv Γ γ A a x ξ)
  (hT : TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Ξ T)
  (hQ : TyDeriv (Ξ ++ pathCtx Γ A x) (telTotal T) Q q)
  (hp : TmDeriv (Ξ ++ pathCtx Γ A x) (telTotal T) Q q p π)

def inner := PathCommand.make hΓ hA hx hT (Motive.reflexivity hΓ hA hx hT hQ hp)
def outer := PathCommand.make hΓ hA hx hT
  (Motive.reflexivity hΓ hA hx hT (inner hΓ hA hx hT hQ hp).motive.typing
    (inner hΓ hA hx hT hQ hp).genericTerm)

private def rawTerm {Γ : RawCtx} {γ : CtxCode.{u}} {A t : Expr}
    {a : TyCode γ} {ξ : TmCode γ a} (_h : TmDeriv Γ γ A a t ξ) : Expr := t

theorem selectedRecipe : rawTerm (outer hΓ hA hx hT hQ hp).genericTerm =
    genericJRaw n A x
      (.identity (Expr.identity Q p p)
        (rawTerm (inner hΓ hA hx hT hQ hp).genericTerm)
        (rawTerm (inner hΓ hA hx hT hQ hp).genericTerm))
      (.refl ((rawTerm (inner hΓ hA hx hT hQ hp).genericTerm).sub
        (Expr.liftSubN n (reflexiveSub x)))) := rfl

def rootLeft := (outer hΓ hA hx hT hQ hp).reflexiveTerm
def rootBeta := (outer hΓ hA hx hT hQ hp).reflexiveBeta

def rootRight := ((outer hΓ hA hx hT hQ hp).motive.branchTyping.sub
  (outer hΓ hA hx hT hQ hp).branchArguments).convert
  (TyEqDeriv.subComp (outer hΓ hA hx hT hQ hp).motive.typing
    (SubDeriv.rootTail hΓ hA hx hT) (outer hΓ hA hx hT hQ hp).branchArguments)

variable {Δ : RawCtx} {δ : CtxCode.{u}} {σ : RawSub}
  {s : SubCode δ (SquareKit.Internal.PathTransport.Typed.branchCode a ξ T)}
variable (hσ : SubDeriv Δ δ (subTail (reflexiveSub x) Ξ ++ Γ)
  (SquareKit.Internal.PathTransport.Typed.branchCode a ξ T) σ s)

def substitutedLeft := (rootLeft hΓ hA hx hT hQ hp).sub hσ
def substitutedRight := (rootRight hΓ hA hx hT hQ hp).sub hσ
def substitutedBeta := TmEqDeriv.sub (rootBeta hΓ hA hx hT hQ hp) hσ

def dependentWeakening := SubDeriv.weaken (outer hΓ hA hx hT hQ hp).branchContext
  (TyDeriv.sub (inner hΓ hA hx hT hQ hp).motive.typing (SubDeriv.rootTail hΓ hA hx hT))
def workedLeft := substitutedLeft hΓ hA hx hT hQ hp (dependentWeakening hΓ hA hx hT hQ hp)
def workedRight := substitutedRight hΓ hA hx hT hQ hp (dependentWeakening hΓ hA hx hT hQ hp)
def workedBeta := substitutedBeta hΓ hA hx hT hQ hp (dependentWeakening hΓ hA hx hT hQ hp)

theorem comparisonSound (M : Model.{u}) :
    interpretTm M (substitutedLeft hΓ hA hx hT hQ hp hσ) =
      interpretTm M (substitutedRight hΓ hA hx hT hQ hp hσ) := by
  rw [interpretTm_agrees, interpretTm_agrees]
  exact congrFun (termSound (substitutedBeta hΓ hA hx hT hQ hp hσ)) M

/-- Exact root restriction of the selected outer section computes to its branch.
The typed source computation also retains the generated identity argument map. -/
theorem selectedRoot (M : Model.{u}) :
    HEq (M.subTm ((outer hΓ hA hx hT hQ hp).interpret M) (rootTailCode a ξ T M))
      ((outer hΓ hA hx hT hQ hp).motive.branchCode M) :=
  (outer hΓ hA hx hT hQ hp).beta M

theorem extensionSelected (M : Model.{u}) (_S : DependentJudgments.Sigma.Stable M.toStructuralModel) :
    interpretTm M (substitutedLeft hΓ hA hx hT hQ hp hσ) =
    subTmCode (subTmCode
      (jCode a ξ T (outer hΓ hA hx hT hQ hp).motive.code
        (outer hΓ hA hx hT hQ hp).motive.branchCode)
      (compCode (rootTailCode a ξ T) (idCode (SquareKit.Internal.PathTransport.Typed.branchCode a ξ T)))) s M :=
  interpretTm_agrees M _

end GuardedJRetest.BaselineReference

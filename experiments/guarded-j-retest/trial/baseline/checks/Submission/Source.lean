import SquareKit.Internal.PathTransport.Authoring
import SquareKit.Internal.DependentJudgments.Sigma.Stability
namespace GuardedJRetest.Baseline
open SquareKit.Internal.PathTransport
open SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.PathTransport.Typed.Authoring
universe u
variable {Γ : RawCtx} {γ : CtxCode.{u}} {A x : Expr} {a : TyCode γ}
  {ξ : TmCode γ a} {n : Nat} {Δ : RawCtx} {T : TelCode (pathCode a ξ) n}
  {Q p : Expr} {q : TyCode (telTotal T)} {π : TmCode (telTotal T) q}
  (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a) (hx : TmDeriv Γ γ A a x ξ)
  (hT : TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Δ T)
  (hQ : TyDeriv (Δ ++ pathCtx Γ A x) (telTotal T) Q q)
  (hp : TmDeriv (Δ ++ pathCtx Γ A x) (telTotal T) Q q p π)

def rootMap := SubDeriv.rootTail hΓ hA hx hT

def calibration : @PathCommand Γ γ A x a ξ n Δ T :=
  PathCommand.make hΓ hA hx hT (Motive.reflexivity hΓ hA hx hT hQ hp)

def inner : TmDeriv (Δ ++ pathCtx Γ A x) (telTotal T)
    (.identity Q p p) (identityCode q π π)
    (genericJRaw n A x (.identity Q p p)
      (.refl (p.sub (Expr.liftSubN n (reflexiveSub x)))))
    (jCode a ξ T (calibration hΓ hA hx hT hQ hp).motive.code
      (calibration hΓ hA hx hT hQ hp).motive.branchCode) :=
  (calibration hΓ hA hx hT hQ hp).genericTerm

def calibrationBranch := (calibration hΓ hA hx hT hQ hp).motive.branchTyping


def outer : @PathCommand Γ γ A x a ξ n Δ T :=
  PathCommand.make hΓ hA hx hT
    (Motive.reflexivity hΓ hA hx hT
      (calibration hΓ hA hx hT hQ hp).motive.typing
      (inner hΓ hA hx hT hQ hp))

def outerTerm := (outer hΓ hA hx hT hQ hp).genericTerm

def rawTerm {Γ γ A a t ξ} (_h : TmDeriv Γ γ A a t ξ) : Expr := t

theorem selectedRecipe : rawTerm (outerTerm hΓ hA hx hT hQ hp) =
    genericJRaw n A x
      (.identity (.identity Q p p)
        (genericJRaw n A x (.identity Q p p)
          (.refl (p.sub (Expr.liftSubN n (reflexiveSub x)))) )
        (genericJRaw n A x (.identity Q p p)
          (.refl (p.sub (Expr.liftSubN n (reflexiveSub x)))) ))
      (.refl ((genericJRaw n A x (.identity Q p p)
        (.refl (p.sub (Expr.liftSubN n (reflexiveSub x))))).sub
          (Expr.liftSubN n (reflexiveSub x)))) := rfl

def rootLeft := (outer hΓ hA hx hT hQ hp).reflexiveTerm

def rootRight := by
  let cmd := outer hΓ hA hx hT hQ hp
  let r := SubDeriv.rootTail hΓ hA hx hT
  have result := (TmDeriv.sub cmd.motive.branchTyping cmd.branchArguments).convert
    (TyEqDeriv.subComp cmd.motive.typing r cmd.branchArguments)
  change TmDeriv _ _ _ _ _
    (castCode (subTyComp_code cmd.motive.code (rootTailCode a ξ T)
      (idCode (branchCode a ξ T)))
      (subTmCode cmd.motive.branchCode (idCode (branchCode a ξ T)))) at result
  rw [reflexiveCompose] at result
  exact result

def typedEquation {Γ γ A a t ξ v ν}
    (_left : TmDeriv Γ γ A a t ξ) (_right : TmDeriv Γ γ A a v ν)
    (equation : TmEqDeriv Γ γ A a t ξ v ν) : TmEqDeriv Γ γ A a t ξ v ν := equation

def rootBeta := typedEquation (rootLeft hΓ hA hx hT hQ hp)
  (rootRight hΓ hA hx hT hQ hp) (outer hΓ hA hx hT hQ hp).reflexiveBeta

variable {Ω : RawCtx} {ω : CtxCode.{u}} {σ : RawSub}
  {s : SubCode ω (branchCode a ξ T)}
  (hσ : SubDeriv Ω ω (subTail (reflexiveSub x) Δ ++ Γ) (branchCode a ξ T) σ s)

def substitutedLeft := TmDeriv.sub (rootLeft hΓ hA hx hT hQ hp) hσ

def substitutedRight := TmDeriv.sub (rootRight hΓ hA hx hT hQ hp) hσ

def substitutedBeta := TmEqDeriv.sub (rootBeta hΓ hA hx hT hQ hp) hσ

def dependentWeakening :=
  SubDeriv.weaken (calibration hΓ hA hx hT hQ hp).branchContext
    (TyDeriv.sub (calibration hΓ hA hx hT hQ hp).motive.typing
      (rootMap hΓ hA hx hT))

def workedLeft := substitutedLeft hΓ hA hx hT hQ hp
  (dependentWeakening hΓ hA hx hT hQ hp)
def workedRight := substitutedRight hΓ hA hx hT hQ hp
  (dependentWeakening hΓ hA hx hT hQ hp)
def workedBeta := substitutedBeta hΓ hA hx hT hQ hp
  (dependentWeakening hΓ hA hx hT hQ hp)

theorem comparisonSound (M : Model.{u}) :
    interpretTm M (substitutedLeft hΓ hA hx hT hQ hp hσ) =
      interpretTm M (substitutedRight hΓ hA hx hT hQ hp hσ) := by
  rw [interpretTm_agrees, interpretTm_agrees]
  exact congrFun (termSound (substitutedBeta hΓ hA hx hT hQ hp hσ)) M

theorem selectedRoot (M : Model.{u}) :
    HEq (M.subTm ((outer hΓ hA hx hT hQ hp).interpret M)
      (rootTailCode a ξ T M))
      ((outer hΓ hA hx hT hQ hp).motive.branchCode M) :=
  (outer hΓ hA hx hT hQ hp).beta M

theorem workedSound (M : Model.{u}) :
    interpretTm M (workedLeft hΓ hA hx hT hQ hp) =
      interpretTm M (workedRight hΓ hA hx hT hQ hp) :=
  comparisonSound hΓ hA hx hT hQ hp (dependentWeakening hΓ hA hx hT hQ hp) M

/-- The two J selections and the root, identity and arbitrary substitutions
remain in the exact full model underlying the stable Sigma capability. -/
theorem extensionSelected (M : Model.{u})
    (_S : SquareKit.Internal.DependentJudgments.Sigma.Stable M.toStructuralModel) :
    interpretTm M (substitutedLeft hΓ hA hx hT hQ hp hσ) =
      subTmCode
        (subTmCode
          (jCode a ξ T
            (identityCode (identityCode q π π)
              (jCode a ξ T (identityCode q π π)
                (calibration hΓ hA hx hT hQ hp).motive.branchCode)
              (jCode a ξ T (identityCode q π π)
                (calibration hΓ hA hx hT hQ hp).motive.branchCode))
            (outer hΓ hA hx hT hQ hp).motive.branchCode)
          (compCode (rootTailCode a ξ T) (idCode (branchCode a ξ T)))) s M :=
  interpretTm_agrees M (substitutedLeft hΓ hA hx hT hQ hp hσ)

/-- Explicit family preservation, including both varying endpoints of the
inner identity and both occurrences of its selected J section. -/
def extensionFamily (M : Model.{u})
    (_S : SquareKit.Internal.DependentJudgments.Sigma.Stable M.toStructuralModel) :
    M.Section (ω M)
      (subTyCode
        (subTyCode
          (identityCode (identityCode q π π)
            (jCode a ξ T (identityCode q π π)
              (calibration hΓ hA hx hT hQ hp).motive.branchCode)
            (jCode a ξ T (identityCode q π π)
              (calibration hΓ hA hx hT hQ hp).motive.branchCode))
          (compCode (rootTailCode a ξ T) (idCode (branchCode a ξ T)))) s M) :=
  interpretTm M (substitutedLeft hΓ hA hx hT hQ hp hσ)

/-- A supplied dependent three-entry tail instantiates all source premises. -/
def populatedExample := workedBeta NamedCaller.earlier NamedCaller.base
  NamedCaller.x.deriv NamedCaller.generalized NamedCaller.qAtBType NamedCaller.qAtB

end GuardedJRetest.Baseline

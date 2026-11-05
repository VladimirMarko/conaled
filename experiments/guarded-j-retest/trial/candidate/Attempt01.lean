import SquareKit.Internal.DependentJudgments.Templates
namespace GuardedJRetest.Candidate
open SquareKit.Internal.DependentJudgments.Contextual
variable {V : Type} {Ω : List (Judgment V)} {Γ A x T Q p : Expression V} {n : Nat}
variable (hx : Tm (Ω := Ω) Γ A x) (hT : Tel (Ω := Ω) n (path A x) T)
variable (hp : Tm (Ω := Ω) (total T) Q p)
def calibration : Command Ω Γ A x := Command.reflexivity hx hT hp
def inner : Tm (Ω := Ω) (total T) (identity Q p p) (calibration hx hT hp).expression :=
  (calibration hx hT hp).typing
def rootMap : Sub (Ω := Ω) (total (pullback T (root A x))) (total T) (rootTail A x T) :=
  hx.rootTail hT
def calibrationBranch : Tm (Ω := Ω) (total (pullback T (root A x)))
    (subTy (identity Q p p) (rootTail A x T))
    (reflexivity (subTy Q (rootTail A x T)) (subTm p (rootTail A x T))) :=
  hp.reflexivitySub (rootMap hx hT)
theorem calibrationRecipe : (calibration hx hT hp).expression =
    j A x T (identity Q p p)
      (reflexivity (subTy Q (rootTail A x T)) (subTm p (rootTail A x T))) := rfl
end GuardedJRetest.Candidate

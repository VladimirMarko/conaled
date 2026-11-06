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


def outer : Command Ω Γ A x := Command.reflexivity hx hT (inner hx hT hp)
theorem selectedRecipe : (outer hx hT hp).expression =
    j A x T (identity (identity Q p p) (calibration hx hT hp).expression
      (calibration hx hT hp).expression)
      (reflexivity (subTy (identity Q p p) (rootTail A x T))
        (subTm (calibration hx hT hp).expression (rootTail A x T))) := rfl

def outerTyping : Tm (Ω := Ω) (total T)
    (identity (identity Q p p) (calibration hx hT hp).expression (calibration hx hT hp).expression)
    (outer hx hT hp).expression := (outer hx hT hp).typing

def rootLeft : Tm (Ω := Ω) (total (pullback T (root A x)))
    (subTy (outer hx hT hp).motive (rootTail A x T))
    (subTm (outer hx hT hp).expression (rootTail A x T)) :=
  (outer hx hT hp).typing.substitute (rootMap hx hT)
def rootRight : Tm (Ω := Ω) (total (pullback T (root A x)))
    (subTy (outer hx hT hp).motive (rootTail A x T)) (outer hx hT hp).branch :=
  (outer hx hT hp).branchTyping
def rootBeta : Equal (Ω := Ω) (subTm (outer hx hT hp).expression (rootTail A x T))
    (outer hx hT hp).branch :=
  hx.jBeta hT (outer hx hT hp).motiveTyping (outer hx hT hp).branchTyping

variable {Δ σ : Expression V}
variable (hσ : Sub (Ω := Ω) Δ (total (pullback T (root A x))) σ)
def substitutedLeft : Tm (Ω := Ω) Δ
    (subTy (subTy (outer hx hT hp).motive (rootTail A x T)) σ)
    (subTm (subTm (outer hx hT hp).expression (rootTail A x T)) σ) :=
  (rootLeft hx hT hp).substitute hσ
def substitutedRight : Tm (Ω := Ω) Δ
    (subTy (subTy (outer hx hT hp).motive (rootTail A x T)) σ)
    (subTm (outer hx hT hp).branch σ) :=
  (rootRight hx hT hp).substitute hσ
-- Congruence acts on the selected syntax; it does not use semantic equality.
def substitutedBeta : Equal (Ω := Ω)
    (subTm (subTm (outer hx hT hp).expression (rootTail A x T)) σ)
    (subTm (outer hx hT hp).branch σ) :=
  SquareKit.GuardedTheory.Derivation.congruence (T := theory) (Sum.inl SquareKit.Internal.DependentJudgments.Operation.subTm)
    (Fin.cases (rootBeta hx hT hp)
      (Fin.cases (.reflexive σ) (fun i => nomatch i)))

def dependentWeakening : Sub (Ω := Ω)
    (extend (total (pullback T (root A x))) (subTy (identity Q p p) (rootTail A x T)))
    (total (pullback T (root A x)))
    (weaken (total (pullback T (root A x))) (subTy (identity Q p p) (rootTail A x T))) :=
  ((inner hx hT hp).substitute (rootMap hx hT)).family.weaken

def workedLeft := substitutedLeft hx hT hp (dependentWeakening hx hT hp)
def workedRight := substitutedRight hx hT hp (dependentWeakening hx hT hp)
def workedBeta := substitutedBeta (σ := weaken (total (pullback T (root A x)))
  (subTy (identity Q p p) (rootTail A x T))) hx hT hp
end GuardedJRetest.Candidate

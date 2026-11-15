import SquareKit.Internal.DependentJudgments.Authoring

/-! Generated contextual commands retain their recipe. Fresh reindexing builds
new motive and branch judgments; compatibility is a theorem of that builder. -/
namespace SquareKit.Internal.DependentJudgments.Contextual
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ Δ A x σ : Expression V}

structure Command (Ω : List (Judgment V)) (Γ A x : Expression V) where
  point : Tm (Ω := Ω) Γ A x
  length : Nat
  tail : Expression V
  tailTyping : Tel (Ω := Ω) length (path A x) tail
  motive : Expression V
  motiveTyping : Ty (Ω := Ω) (total tail) motive
  branch : Expression V
  branchTyping : Tm (Ω := Ω) (total (pullback tail (root A x)))
    (subTy motive (rootTail A x tail)) branch

/-- A selected J certificate of reflexivity for a section over the whole
based path and dependent tail. The branch conversion is derived by the author
interface; callers supply only their source point, tail and section. -/
def Command.reflexivity {n : Nat} {T Q p : Expression V}
    (hx : Tm (Ω := Ω) Γ A x) (hT : Tel (Ω := Ω) n (path A x) T)
    (hp : Tm (Ω := Ω) (total T) Q p) : Command Ω Γ A x where
  point := hx
  length := n
  tail := T
  tailTyping := hT
  motive := identity Q p p
  motiveTyping := hp.identity hp
  branch := Contextual.reflexivity (subTy Q (rootTail A x T)) (subTm p (rootTail A x T))
  branchTyping := hp.reflexivitySub (hx.rootTail hT)

def Command.expression (c : Command Ω Γ A x) : Expression V := j A x c.tail c.motive c.branch

def Command.typing (c : Command Ω Γ A x) : Tm (Ω := Ω) (total c.tail) c.motive c.expression :=
  c.point.j c.tailTyping c.motiveTyping c.branchTyping

/-- The fresh command is constructed from the reindexed data. It is not a
judgmental equality or compatibility witness supplied by the caller. -/
def Command.fresh (c : Command Ω Γ A x) (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Command Ω Δ (subTy A σ) (subTm x σ) where
  point := c.point.substitute hσ
  length := c.length
  tail := pathTail A x c.tail σ
  tailTyping := c.point.pathTail c.tailTyping hσ
  motive := subTy c.motive (pathTailMap A x c.tail σ)
  motiveTyping := c.motiveTyping.substitute (c.point.pathTailMap c.tailTyping hσ)
  branch := reindexBranch A x c.tail σ c.motive c.branch
  branchTyping := c.point.reindexBranch c.tailTyping c.motiveTyping c.branchTyping hσ

/-- Substitution of a command and fresh construction have the same judgmental
meaning, by the generated J substitution derivation. -/
def Command.substituted_eq_fresh (c : Command Ω Γ A x) (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTm c.expression (pathTailMap A x c.tail σ)) (c.fresh hσ).expression :=
  c.point.jSub c.tailTyping c.motiveTyping c.branchTyping hσ

/-- The public discriminator observes different syntax heads. Their comparison
therefore cannot be furnished merely by definitional equality of recipes. -/
theorem Command.substituted_ne_fresh (c : Command Ω Γ A x) (hσ : Sub (Ω := Ω) Δ Γ σ) :
    subTm c.expression (pathTailMap A x c.tail σ) ≠ (c.fresh hσ).expression := by
  intro e
  cases e

/-- Judgmental equalities are accompanied by typing of both operands when
used as semantic comparison contracts. -/
structure TypedEquality (Ω : List (Judgment V)) (Γ A s t : Expression V) where
  left : Tm (Ω := Ω) Γ A s
  right : Tm (Ω := Ω) Γ A t
  equality : Equal (Ω := Ω) s t

def Command.comparison (c : Command Ω Γ A x) (hσ : Sub (Ω := Ω) Δ Γ σ) :
    TypedEquality Ω (total (pathTail A x c.tail σ))
      (subTy c.motive (pathTailMap A x c.tail σ))
      (subTm c.expression (pathTailMap A x c.tail σ)) (c.fresh hσ).expression where
  left := c.typing.substitute (c.point.pathTailMap c.tailTyping hσ)
  right := (c.fresh hσ).typing
  equality := c.substituted_eq_fresh hσ

end SquareKit.Internal.DependentJudgments.Contextual

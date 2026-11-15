import SquareKit.Internal.DependentJudgments.LeftAssociativityArguments

/-! General source associativity of the retained left-path concatenation.
The author supplies arbitrary typed p,q,r. The dependent tail, branch,
argument environment and result conversion are generated. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)} {Γ : Expression V}
namespace ThreePaths
variable (C : ThreePaths Ω Γ)
abbrev associator : Expression V :=
  let F := LeftAssociativityFrame.inputs C.first.first
  let R := (LeftAssociativityFrame.tail Γ C.first.A C.first.x).map Γ (root C.first.A C.first.x)
  subTm (j C.first.A C.first.x
    ((LeftAssociativityFrame.tail Γ C.first.A C.first.x).code (path C.first.A C.first.x)) F.motive
    (Contextual.reflexivity (Contextual.identity (subTy F.first.A R) (subTm F.first.x R) (subTm F.w R))
      (F.substitute (LeftAssociativityFrame.rootR C.first.first)).left))
    (LeftAssociativityArguments.atR C)
def associativity : Tm (Ω := Ω) Γ C.motive C.associator :=
  ((LeftAssociativityFrame.derivation C.first.first).substitute (LeftAssociativityArguments.atRTyped C)).convert
    (LeftAssociativityArguments.motiveAt C)
end ThreePaths
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation

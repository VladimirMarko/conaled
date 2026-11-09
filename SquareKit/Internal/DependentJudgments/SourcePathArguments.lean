import SquareKit.Internal.DependentJudgments.SourcePath

/-! Applying dependent argument environments transports path comparisons
through binders without caller-provided presentation equations. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)} {Γ Δ : Expression V}
structure PathArguments (P : SourcePath Ω Γ) (Q : SourcePath Ω Δ)
    {σ : Expression V} (hs : Sub (Ω := Ω) Δ Γ σ) where
  carrier : Equal (Ω := Ω) (subTy P.A σ) Q.A
  first : Equal (Ω := Ω) (subTm P.x σ) Q.x
  second : Equal (Ω := Ω) (subTm P.y σ) Q.y
  proof : Equal (Ω := Ω) (subTm P.p σ) Q.p
namespace PathArguments
variable {P : SourcePath Ω Γ} {Q : SourcePath Ω Δ} {σ B t : Expression V}
  {hs : Sub (Ω := Ω) Δ Γ σ}
def under (E : PathArguments P Q hs) (hB : Ty (Ω := Ω) Γ B)
    (ht : Tm (Ω := Ω) Δ (subTy B σ) t) :
    PathArguments (P.substitute hB.weaken) Q (Sub.pair hB hs ht) where
  carrier := (P.first.family.weakenPairType hB hs ht).transitive E.carrier
  first := (P.first.weakenPair hB hs ht).transitive E.first
  second := (P.second.weakenPair hB hs ht).transitive E.second
  proof := (P.proof.weakenPair hB hs ht).transitive E.proof

def generic (Q : SourcePath Ω Γ) :
    PathArguments (SourcePath.generic Q.first) Q (Q.first.endpoint Q.second Q.proof) where
  carrier := LeftConcatArguments.pathTypeAt Q.first Q.second Q.proof
  first := LeftConcatArguments.fixedAt Q.first Q.second Q.proof
  second := LeftConcatArguments.movingAt Q.first Q.second Q.proof
  proof := Q.first.pathFamily.variablePair Q.second.section
    (Q.proof.convert (Q.first.pathFamilySection Q.second).symmetric)
end PathArguments
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation

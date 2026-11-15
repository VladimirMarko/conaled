import SquareKit.Internal.DependentJudgments.PresentedPath

/-! Typed source paths and their reflexive-root evidence through dependent
binders. All conversions are generated source derivations. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)} {Γ Δ : Expression V}
structure SourcePath (Ω : List (Judgment V)) (Γ : Expression V) where
  A : Expression V
  x : Expression V
  y : Expression V
  p : Expression V
  first : Tm (Ω := Ω) Γ A x
  second : Tm (Ω := Ω) Γ A y
  proof : Tm (Ω := Ω) Γ (Contextual.identity A x y) p
namespace SourcePath
variable (P : SourcePath Ω Γ)
def substitute {σ : Expression V} (hs : Sub (Ω := Ω) Δ Γ σ) : SourcePath Ω Δ where
  A := subTy P.A σ
  x := subTm P.x σ
  y := subTm P.y σ
  p := subTm P.p σ
  first := P.first.substitute hs
  second := P.second.substitute hs
  proof := (P.proof.substitute hs).convert (P.first.identitySub P.second hs)
def generic {A x : Expression V} (hx : Tm (Ω := Ω) Γ A x) : SourcePath Ω (path A x) where
  A := LeftConcatFrame.pathType Γ A x
  x := LeftConcatFrame.fixed Γ A x
  y := LeftConcatFrame.moving Γ A x
  p := PresentedPath.pathProof Γ A x
  first := LeftConcatFrame.fixedTyped hx
  second := LeftConcatFrame.movingTyped hx
  proof := PresentedPath.pathProofTyped hx
end SourcePath
structure ReflexiveRoot (P : SourcePath Ω Γ) {σ : Expression V} (hs : Sub (Ω := Ω) Δ Γ σ) where
  endpoint : Equal (Ω := Ω) (subTm P.y σ) (subTm P.x σ)
  path : Equal (Ω := Ω) (subTm P.p σ) (Contextual.reflexivity (subTy P.A σ) (subTm P.x σ))
namespace ReflexiveRoot
variable {P : SourcePath Ω Γ} {σ B : Expression V} {hs : Sub (Ω := Ω) Δ Γ σ}
def under (R : ReflexiveRoot P hs) (hB : Ty (Ω := Ω) Γ B) :
    ReflexiveRoot (P.substitute hB.weaken) (hs.lift hB) where
  endpoint := P.second.weakenLiftEqual P.first hB hs R.endpoint
  path := (P.proof.weakenLift hB hs).transitive
    ((Equal.subTm R.path (.reflexive _)).transitive
      (((P.first.substitute hs).reflSub (hB.substitute hs).weaken).transitive
        (Equal.reflexivity (P.first.family.weakenLift hB hs).symmetric
          (P.first.weakenLift hB hs).symmetric)))
def generic {A x : Expression V} (hx : Tm (Ω := Ω) Γ A x) :
    ReflexiveRoot (SourcePath.generic hx) hx.root where
  endpoint := (LeftConcatFrame.movingRoot hx).transitive (LeftConcatFrame.fixedRoot hx).symmetric
  path := (PresentedPath.pathProofRoot hx).transitive
    (Equal.reflexivity (PresentedPath.pathTypeRoot hx).symmetric (LeftConcatFrame.fixedRoot hx).symmetric)
end ReflexiveRoot
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation

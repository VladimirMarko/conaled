import SquareKit.Internal.DependentJudgments.LeftAssociativity

/-! Public callers of generated source substitution and congruence. These
retain arbitrary typed paths and contexts rather than a reflexive test only. -/
noncomputable section
namespace Examples.GuardedLeftAuthoring
open SquareKit.GuardedTheory SquareKit.Internal.DependentJudgments
open Contextual TelescopePresentation
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Contextual.Judgment V)}
  {Γ Δ Θ A x y z p q q' σ τ : Contextual.Expression V}
variable (hx : TelescopePresentation.Tm (Ω := Ω) Γ A x)
  (hy : TelescopePresentation.Tm (Ω := Ω) Γ A y) (hz : TelescopePresentation.Tm (Ω := Ω) Γ A z)
  (hp : TelescopePresentation.Tm (Ω := Ω) Γ (Contextual.identity A x y) p)
  (hq : TelescopePresentation.Tm (Ω := Ω) Γ (Contextual.identity A y z) q)
  (hs : TelescopePresentation.Sub (Ω := Ω) Δ Γ σ) (ht : TelescopePresentation.Sub (Ω := Ω) Θ Δ τ)

example : TelescopePresentation.Equal (Ω := Ω) (subTm (leftConcat Γ A x y z p q) σ)
    (leftConcat Δ (subTy A σ) (subTm x σ) (subTm y σ) (subTm z σ) (subTm p σ) (subTm q σ)) :=
  hx.leftConcatSub hy hz hp hq hs

/-- Repeated fresh authoring reuses the same theorem; no composite
presentation equality is supplied by this caller. -/
example : TelescopePresentation.Equal (Ω := Ω) (subTm (subTm (leftConcat Γ A x y z p q) σ) τ)
    (leftConcat Θ (subTy (subTy A σ) τ) (subTm (subTm x σ) τ) (subTm (subTm y σ) τ)
      (subTm (subTm z σ) τ) (subTm (subTm p σ) τ) (subTm (subTm q σ) τ)) :=
  (TelescopePresentation.Equal.subTm (hx.leftConcatSub hy hz hp hq hs) (.reflexive _)).transitive
    ((hx.substitute hs).leftConcatSub (hy.substitute hs) (hz.substitute hs)
      ((hp.substitute hs).convert (hx.identitySub hy hs))
      ((hq.substitute hs).convert (hy.identitySub hz hs)) ht)

/-- A generated argument conversion composes with a fresh construction. -/
example (he : TelescopePresentation.Equal (Ω := Ω) q q') :
    TelescopePresentation.Equal (Ω := Ω) (leftConcat Γ A x y z p q) (leftConcat Γ A x y z p q') :=
  TelescopePresentation.Equal.leftConcat (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _)
    (.reflexive _) (.reflexive _) he
end Examples.GuardedLeftAuthoring

import SquareKit.Internal.DependentJudgments.LeftTransportCompositionSemantics

/-! An ordinary caller of the guarded first-path transport-composition proof.
The family, both paths, and the input element are independent syntax variables. -/
noncomputable section
namespace Examples.GuardedLeftTransportComposition
open SquareKit.Internal SquareKit.GuardedTheory
open DependentJudgments DependentJudgments.Contextual
open DependentJudgments.Contextual.TelescopePresentation
open TelescopePresentation.LeftTransportComposition
set_option backward.isDefEq.respectTransparency false

abbrev assumptions : List (Contextual.Judgment (Fin 9)) :=
  [family (Contextual.extend (.var 0) (.var 1)) (.var 2),
    term (.var 0) (.var 1) (.var 3), term (.var 0) (.var 1) (.var 4),
    term (.var 0) (.var 1) (.var 5),
    term (.var 0) (Contextual.identity (.var 1) (.var 3) (.var 4)) (.var 6),
    term (.var 0) (Contextual.identity (.var 1) (.var 4) (.var 5)) (.var 7),
    term (.var 0) (subTy (.var 2) (sectionSub (.var 0) (.var 1) (.var 3))) (.var 8)]

def inputs : LeftTransportComposition.Inputs assumptions (.var 0) where
  first := ⟨.var 1, .var 3, .var 4, .var 6,
    .hypothesis (by simp [assumptions]), .hypothesis (by simp [assumptions]),
    .hypothesis (by simp [assumptions])⟩
  B := .var 2
  z := .var 5
  q := .var 7
  u := .var 8
  family := .hypothesis (by simp [assumptions])
  third := .hypothesis (by simp [assumptions])
  secondPath := .hypothesis (by simp [assumptions])
  element := .hypothesis (by simp [assumptions])

/-- No presentation codes or conversion equalities are supplied by the caller. -/
def source : TelescopePresentation.Tm (Ω := assumptions) (.var 0)
    (Contextual.identity (subTy (.var 2) (sectionSub (.var 0) (.var 1) (.var 5)))
      (Contextual.transport (.var 0) (.var 1) (.var 2) (.var 3) (.var 5)
        (leftConcat (.var 0) (.var 1) (.var 3) (.var 4) (.var 5) (.var 6) (.var 7)) (.var 8))
      (Contextual.transport (.var 0) (.var 1) (.var 2) (.var 4) (.var 5) (.var 7)
        (Contextual.transport (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 6) (.var 8))))
    inputs.certificate := inputs.composition

/-- Fresh typed source substitution uses the same construction with reindexed
family, endpoints, paths, and element. -/
example {V : Type} {Ω : List (Contextual.Judgment V)} {Γ Δ σ : Contextual.Expression V}
    (C : LeftTransportComposition.Inputs Ω Γ) (hs : TelescopePresentation.Sub (Ω := Ω) Δ Γ σ) :
    TelescopePresentation.Tm (Ω := Ω) Δ (C.substitute hs).motive (C.substitute hs).certificate :=
  (C.substitute hs).composition

/-- The original certificate also transports to the fresh mathematical motive. -/
example {V : Type} {Ω : List (Contextual.Judgment V)} {Γ Δ σ : Contextual.Expression V}
    (C : LeftTransportComposition.Inputs Ω Γ) (hs : TelescopePresentation.Sub (Ω := Ω) Δ Γ σ) :
    TelescopePresentation.Tm (Ω := Ω) Δ (C.substitute hs).motive (subTm C.certificate σ) :=
  (C.composition.substitute hs).convert (C.motiveSub hs)

end Examples.GuardedLeftTransportComposition

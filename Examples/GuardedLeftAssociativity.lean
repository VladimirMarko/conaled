import SquareKit.Internal.DependentJudgments.LeftAssociativitySemantics
import Examples.GuardedLeftConcatenation

/-! Arbitrary source paths and labeled faithful/ineffective C4 consumers of
one guarded associativity derivation. This known theorem is not a fresh-author test. -/
noncomputable section
namespace Examples.GuardedLeftAssociativity
open CategoryTheory SquareKit.Internal SquareKit.GuardedTheory
open DependentJudgments DependentJudgments.Contextual
open DependentJudgments.Contextual.TelescopePresentation
open PathTransport.GroupoidModel Examples.GroupoidTransport Examples.GuardedLeftConcatenation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev assumptions : List (Contextual.Judgment (Fin 9)) :=
  [term (.var 0) (.var 1) (.var 2), term (.var 0) (.var 1) (.var 3),
    term (.var 0) (.var 1) (.var 4), term (.var 0) (.var 1) (.var 5),
    term (.var 0) (Contextual.identity (.var 1) (.var 2) (.var 3)) (.var 6),
    term (.var 0) (Contextual.identity (.var 1) (.var 3) (.var 4)) (.var 7),
    term (.var 0) (Contextual.identity (.var 1) (.var 4) (.var 5)) (.var 8)]

def inputs : ThreePaths assumptions (.var 0) where
  first := ⟨.var 1, .var 2, .var 3, .var 6,
    .hypothesis (by simp [assumptions]), .hypothesis (by simp [assumptions]),
    .hypothesis (by simp [assumptions])⟩
  z := .var 4
  w := .var 5
  q := .var 7
  r := .var 8
  third := .hypothesis (by simp [assumptions])
  fourth := .hypothesis (by simp [assumptions])
  middle := .hypothesis (by simp [assumptions])
  last := .hypothesis (by simp [assumptions])

/-- The source statement retains independently supplied p,q,r. -/
def source : TelescopePresentation.Tm (Ω := assumptions) (.var 0)
    (Contextual.identity (Contextual.identity (.var 1) (.var 2) (.var 5))
      (leftConcat (.var 0) (.var 1) (.var 2) (.var 4) (.var 5)
        (leftConcat (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 6) (.var 7)) (.var 8))
      (leftConcat (.var 0) (.var 1) (.var 2) (.var 3) (.var 5) (.var 6)
        (leftConcat (.var 0) (.var 1) (.var 3) (.var 4) (.var 5) (.var 7) (.var 8)))) inputs.associator :=
  inputs.associativity

def environment (B : C4 ⥤ Type) (m n k : ZMod 4) : Fin 9 → Value (Instance.fullModel C4 B).toStructuralModel :=
  ![.context G, .family G (constant C4), .term G (constant C4) ⟨base⟩,
    .term G (constant C4) ⟨base⟩, .term G (constant C4) ⟨base⟩, .term G (constant C4) ⟨base⟩,
    .term G (identityFamily (constant C4) base base) ⟨labeled m⟩,
    .term G (identityFamily (constant C4) base base) ⟨labeled n⟩,
    .term G (identityFamily (constant C4) base base) ⟨labeled k⟩]

theorem assumptions_valid (B : C4 ⥤ Type) (m n k : ZMod 4) :
    ∀ a ∈ assumptions, a.eval (TelescopePresentation.model (Instance.fullModel C4 B)).toAlgebra (environment B m n k) := by
  intro a ha
  simp only [assumptions, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    change ∃ Γ A t, _ = Value.context Γ ∧ _ = Value.family Γ A ∧ _ = Value.term Γ A t
    first
    | exact ⟨G, constant C4, ⟨base⟩, rfl, rfl, rfl⟩
    | refine ⟨G, identityFamily (constant C4) base base, ⟨labeled m⟩, rfl, ?_, rfl⟩
    | refine ⟨G, identityFamily (constant C4) base base, ⟨labeled n⟩, rfl, ?_, rfl⟩
    | refine ⟨G, identityFamily (constant C4) base base, ⟨labeled k⟩, rfl, ?_, rfl⟩
  all_goals
    simp [Term.eval, TelescopePresentation.model, Contextual.algebra, Contextual.operation, environment]
    rfl

abbrev higherFamily (m n k : ZMod 4) := identityFamily (identityFamily (constant C4) base base)
  (LeftSemantics.Groupoid.leftComposite (Grpd.of C4) G base base base base (labeled m) (labeled n) (labeled k))
  (LeftSemantics.Groupoid.rightComposite (Grpd.of C4) G base base base base (labeled m) (labeled n) (labeled k))

/-- The selected higher witness is the value of the source term itself. In
particular, the proof does not replace it with a direct groupoid associator. -/
theorem interpreted (B : C4 ⥤ Type) (m n k : ZMod 4) :
    ∃ selected : (Instance.fullModel C4 B).Section G (higherFamily m n k),
      inputs.associator.eval (algebra (Instance.fullModel C4 B)) (environment B m n k) = .term G _ selected :=
  LeftSemantics.Groupoid.associator_evaluates (Grpd.of C4) B inputs (environment B m n k) G
    base base base base (labeled m) (labeled n) (labeled k)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl (assumptions_valid B m n k)

example : ∃ selected : (Instance.fullModel C4 faithful).Section G (higherFamily 1 2 3),
    inputs.associator.eval (algebra (Instance.fullModel C4 faithful)) (environment faithful 1 2 3) = .term G _ selected :=
  interpreted faithful 1 2 3
example : ∃ selected : (Instance.fullModel C4 ineffective).Section G (higherFamily 1 2 3),
    inputs.associator.eval (algebra (Instance.fullModel C4 ineffective)) (environment ineffective 1 2 3) = .term G _ selected :=
  interpreted ineffective 1 2 3

/-- Both sides retain the path labels even for the ineffective action model. -/
example : ((LeftSemantics.Groupoid.leftComposite (Grpd.of C4) G base base base base (labeled 1) (labeled 2) (labeled 3)).obj ⟨PUnit.unit⟩).as = label 2 := rfl
example : ((LeftSemantics.Groupoid.rightComposite (Grpd.of C4) G base base base base (labeled 1) (labeled 2) (labeled 3)).obj ⟨PUnit.unit⟩).as = label 2 := rfl
end Examples.GuardedLeftAssociativity

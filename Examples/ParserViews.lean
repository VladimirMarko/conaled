import Applications.Languages.Transposition

/-! Exact selected results for every added top-level parser row. All examples
recover the symbolic result through the common transposition contract. -/
namespace Examples.ParserViews
open SquareKit.EquationTranspose LanguageWitnesses LanguageWitnesses.Transposition

/-- Zero refutes every claimed parse; no success witness is fabricated. -/
example : (methods.construct (meaning (α := Bool)) .zero PUnit.unit (.snapshot 0)
    PUnit.unit).lookup [] (by decide) = Decision.no (fun x => nomatch x) :=
  recovered_snapshot _ _ _ _ _

example : (methods.construct (meaning (α := Bool)) .universal PUnit.unit (.snapshot 2)
    PUnit.unit).lookup [true,false] (by decide) = Decision.yes PUnit.unit :=
  recovered_snapshot _ _ _ _ _

example : (methods.construct (meaning (α := Bool)) .epsilon PUnit.unit .nullable
    PUnit.unit).down = Decision.yes (Evidence.mk rfl) := recovered_nullable _ _

example : (methods.construct meaning (.atom true) PUnit.unit (.snapshot 1)
    PUnit.unit).lookup [true] (by decide) = Decision.yes (Evidence.mk rfl) :=
  recovered_snapshot _ _ _ _ _

/-- Rejection is checked at the same atom row on a different word. -/
example : ((methods.construct meaning (.atom true) PUnit.unit (.snapshot 1)
    PUnit.unit).lookup [false] (by decide)).test = false := by
  exact (congrArg Decision.test (recovered_snapshot (.atom true) PUnit.unit 1 [false] (by decide))).trans rfl

example : (methods.construct (meaning (α := Bool)) (.intersection epsilon epsilon)
    (Parser.epsilon,Parser.epsilon) .nullable PUnit.unit).down =
      Decision.yes (Evidence.mk rfl, Evidence.mk rfl) := recovered_nullable _ _

/-- Scale preserves the selected payload as well as epsilon evidence. -/
example : (methods.construct (meaning (α := Bool)) (.scale Bool epsilon)
    (⟨Decision.yes true⟩,Parser.epsilon) (.snapshot 0) PUnit.unit).lookup [] (by decide) =
      Decision.yes (true, Evidence.mk rfl) := recovered_snapshot _ _ _ _ _

abbrev Ambiguous : Language Bool := fun w => epsilon w ⊕ epsilon w

def swap (w : List Bool) : Iso (Ambiguous w) (Ambiguous w) where
  forward := Sum.swap
  backward := Sum.swap
  backward_forward := by intro x; cases x <;> rfl
  forward_backward := by intro x; cases x <;> rfl

/-- Arbitrary transport can change the selected alternative, and the view retains it. -/
example : (methods.construct meaning (.transport Ambiguous Ambiguous swap)
    (Parser.union Parser.epsilon Parser.epsilon) (.snapshot 0) PUnit.unit).lookup [] (by decide) =
      Decision.yes (Sum.inr (Evidence.mk rfl)) := recovered_snapshot _ _ _ _ _

/-- The transported derivative retains the reindexed isomorphism, not just acceptance. -/
example {P Q : Language Bool} (e : ∀ w, Iso (P w) (Q w)) (p : Parser P) (a : Bool) :
    methods.construct meaning (.transport P Q e) p (.derive a) PUnit.unit =
      Parser.transport (fun w => e (a :: w)) (p.derive a) := recovered_derive _ _ _

/-- Structural derivative recovery retains both intersection operands. -/
example (p : Parser (α := Bool) P) (q : Parser Q) (a : Bool) :
    methods.construct meaning (.intersection P Q) (p,q) (.derive a) PUnit.unit =
      Parser.intersection (p.derive a) (q.derive a) := recovered_derive _ _ _

example (p : Parser (α := Bool) P) (d : Decision Bool) (a : Bool) :
    methods.construct meaning (.scale Bool P) (⟨d⟩,p) (.derive a) PUnit.unit =
      Parser.scale d (p.derive a) := recovered_derive _ _ _

/-- All added rows retain both syntax round trips, with no semantic quotient. -/
example : untranspose (transpose (equations (α := Bool))) = equations :=
  untranspose_transpose _
example : transpose (untranspose (methods (α := Bool))) = methods :=
  transpose_untranspose _

end Examples.ParserViews

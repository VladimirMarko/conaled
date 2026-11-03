import SquareKit.Internal.Graph
import SquareKit.Internal.ConditionedComposition

/-! Preserved #50 authoring experiment. Only `Rules.existsHere` is recommended
for reuse; the helpers in this module are comparison artifacts, not a supported
frontend. No notation, instances, or elaborators are installed.
See `docs/research/internal-proof-authoring.md` for obligations and run commands. -/
namespace Examples.InternalAuthoring
open SquareKit.Internal
universe u
variable {S : Type u} {F P : S → S → Type u} {Γ : List S} {s a b c d : S}

namespace Direct
-- The baseline uses the existing named rules and explicit substitution equality.
theorem frobenius_forward (h : Formula F Γ P) (p : Formula F (s :: Γ) P) :
    Derives (.conj h (.ex p)) (.ex (.conj h.shift p)) := by
  apply Rules.existsElimWith
  change Derives (.conj h.shift p)
    (.ex ((FormulaCore.conj h.shift p).subst (Sub.lift (fun i => .var (.succ i)))))
  have witness := Rules.existsIntro
    ((FormulaCore.conj h.shift p).subst (Sub.lift (fun i => .var (.succ i)))) (.var .zero)
  rw [FormulaCore.lift_shift_instantiate] at witness
  exact witness

theorem frobenius_backward (h : Formula F Γ P) (p : Formula F (s :: Γ) P) :
    Derives (.ex (.conj h.shift p)) (.conj h (.ex p)) := by
  apply Rules.existsElim
  apply Rules.andIntro Rules.andLeft
  apply Rules.cut Rules.andRight
  change Derives p (.ex (p.subst (Sub.lift (fun i => .var (.succ i)))))
  have witness := Rules.existsIntro (p.subst (Sub.lift (fun i => .var (.succ i)))) (.var .zero)
  rw [FormulaCore.lift_shift_instantiate] at witness
  exact witness
theorem nested_forward (h : Formula F [a, d] P) (r : P a b) (s : P b c) (t : P c d) :
    Derives (.conj h (Associativity.left r s t))
      (.ex (.conj h.shift (ConditionedComposition.body r s t))) :=
  Rules.cut (Rules.andIntro Rules.andLeft
    (Rules.cut Rules.andRight (Associativity.forward r s t)))
    (frobenius_forward h (ConditionedComposition.body r s t))

theorem nested_backward (h : Formula F [a, d] P) (r : P a b) (s : P b c) (t : P c d) :
    Derives (.ex (.conj h.shift (ConditionedComposition.body r s t)))
      (.conj h (Associativity.left r s t)) :=
  Rules.cut (frobenius_backward h (ConditionedComposition.body r s t))
    (Rules.andIntro Rules.andLeft (Rules.cut Rules.andRight (Associativity.backward r s t)))
end Direct

namespace Helpers
/-- Frame a derivation with an untouched left assumption. -/
theorem frame (proof : Derives p q) : Derives (.conj h p) (.conj h q) :=
  Rules.andIntro Rules.andLeft (Rules.cut Rules.andRight proof)

/-- Retain the right assumption when the existential is on the left. -/
theorem eliminateLeft (proof : Derives (.conj h.shift p) q.shift) :
    Derives (.conj (.ex p) h) q :=
  Rules.cut (Rules.andIntro Rules.andRight Rules.andLeft) (Rules.existsElimWith proof)

-- Same graph sequents, with no wrapper conversion of the formulas.
theorem graph_forward (f : F a b) (g : F b c) :
    Derives (Graph.composite f g) (Graph.result f g) :=
  Rules.existsElim (Rules.eqTrans Rules.andRight (Rules.eqCongr g Rules.andLeft))

theorem graph_backward (f : F a b) (g : F b c) :
    Derives (Graph.result f g) (Graph.composite f g) :=
  Rules.existsWitness (.app f (.var .zero)) (Rules.andIntro Rules.eqRefl Rules.hypothesis)

-- Same associativity sequents. The forward proof uses right retention.
theorem associativity_forward (r : P a b) (s : P b c) (t : P c d) :
    Derives (Associativity.left (F := F) r s t) (Associativity.right r s t) := by
  apply Rules.existsElim
  apply eliminateLeft
  apply Rules.existsWitness (.var .zero)
  apply Rules.andIntro
  · exact Rules.cut Rules.andRight Rules.andLeft
  · apply Rules.existsWitness (.var (.succ .zero))
    exact Rules.andIntro (Rules.cut Rules.andRight Rules.andRight) Rules.andLeft

theorem associativity_backward (r : P a b) (s : P b c) (t : P c d) :
    Derives (Associativity.right (F := F) r s t) (Associativity.left r s t) := by
  apply Rules.existsElim
  apply Rules.existsElimWith
  apply Rules.existsWitness (.var .zero)
  apply Rules.andIntro
  · apply Rules.existsWitness (.var (.succ .zero))
    exact Rules.andIntro Rules.andLeft (Rules.cut Rules.andRight Rules.andLeft)
  · exact Rules.cut Rules.andRight Rules.andRight

theorem frobenius_forward (h : Formula F Γ P) (p : Formula F (s :: Γ) P) :
    Derives (.conj h (.ex p)) (.ex (.conj h.shift p)) :=
  Rules.existsElimWith (Rules.existsHere (.conj h.shift p))

theorem frobenius_backward (h : Formula F Γ P) (p : Formula F (s :: Γ) P) :
    Derives (.ex (.conj h.shift p)) (.conj h (.ex p)) :=
  Rules.existsElim (Rules.andIntro Rules.andLeft (Rules.cut Rules.andRight (Rules.existsHere p)))

theorem nested_forward (h : Formula F [a, d] P) (r : P a b) (s : P b c) (t : P c d) :
    Derives (.conj h (Associativity.left r s t))
      (.ex (.conj h.shift (ConditionedComposition.body r s t))) :=
  Rules.cut (frame (associativity_forward r s t))
    (frobenius_forward h (ConditionedComposition.body r s t))

theorem nested_backward (h : Formula F [a, d] P) (r : P a b) (s : P b c) (t : P c d) :
    Derives (.ex (.conj h.shift (ConditionedComposition.body r s t)))
      (.conj h (Associativity.left r s t)) :=
  Rules.cut (frobenius_backward h (ConditionedComposition.body r s t))
    (frame (associativity_backward r s t))
end Helpers
end Examples.InternalAuthoring

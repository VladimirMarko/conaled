import Applications.Languages.Compositional
import Examples.LanguageCoalgebra

namespace CompositionalCoalgebraExamples
open SquareKit.WordCoalgebra SquareKit.CompositionalCoalgebra
open LanguageCoalgebra.Compositional

namespace Weights
open LanguageCoalgebraExamples.Weights

/-- These reuse the generic constructor-law proof, not the old induction proof. -/
example (w : List Unit) :
    run (LanguageCoalgebra.Weighted.coalgebra pairMachine) expression w =
      (semantics false * semantics true) w :=
  recovered pairMachine semantics interpretation expression w

example : (run ((rule false).lift pairMachine) (embed expression) [()]) 0 0 = 2 := by
  rw [correct pairMachine semantics interpretation, embed_meaning]
  decide

example : (right * left) 0 0 = 0 := by decide

example (w : List Unit) :
    run ((rule true).lift pairMachine)
      (concat (pointwise (.leaf false) (.leaf true)) (embedExtended (.old expression))) w =
      (Convolution.Series.mk (fun w => semantics false w * semantics true w) *
        (semantics false * semantics true)) w := by
  rw [correct pairMachine semantics interpretation]
  rfl

example (w : List Unit) :
    run ((rule true).lift pairMachine) (embedExtended (.old expression)) w =
      (semantics false * semantics true) w :=
  old_in_extended pairMachine semantics interpretation expression w
end Weights

namespace Substitution

def seed (n : Nat) : Coalgebra Unit Nat Unit := fun _ => (n, fun _ => ())
def twice (_ : Unit) : Syntax Nat false Unit := add (.leaf ()) (.leaf ())

theorem twice_morphism : Morphism (seed 2) ((rule false).lift (seed 1)) twice := by
  refine ⟨fun _ => rfl, ?_⟩
  intro x a
  cases x; cases a
  change (rule false).next (seed 1) (add _ _) () = _
  rw [next_add]; rfl

/-- A compound replacement preserves observations in every compound context. -/
example (t : Syntax Nat false Unit) (w : List Unit) :
    run ((rule false).lift (seed 1)) (Term.bind twice t) w =
      run ((rule false).lift (seed 2)) t w :=
  run_transport _ _ _ ((rule false).bind_morphism _ _ _ twice_morphism) t w

example : run ((rule false).lift (seed 1))
    (Term.bind twice (concat (.leaf ()) (.leaf ()))) [()] = 8 := by
  rw [run_transport _ _ _ ((rule false).bind_morphism _ _ _ twice_morphism)]
  decide

example (t : Term (Op Nat false) arity (Syntax Nat false Unit)) (w : List Unit) :
    run ((rule false).lift (seed 1)) (Term.bind id t) w =
      run ((rule false).lift ((rule false).lift (seed 1))) t w :=
  run_transport _ _ _ ((rule false).join_morphism _) t w
end Substitution

namespace RejectedRule
/-- An incorrect concat equation differentiates the right operand twice.
It still has syntactic naturality, but fails semantic compatibility. -/
def bad : Rule (Op Nat false) arity Unit Nat :=
  { rule (A := Unit) false with step := fun op xs a => match op with
    | .concat => add (scale (xs 0) (.leaf (.inr 1)))
        (concat (.leaf (.inr 0)) (.leaf (.inr 1)))
    | .add => (rule false).step .add xs a
    | .scale r => (rule false).step (.scale r) xs a }

def letter : Convolution.Series Unit Nat := ⟨fun w => match w with
  | [_] => 1
  | _ => 0⟩
def empty : Convolution.Series Unit Nat := ⟨fun w => match w with
  | [] => 1
  | _ => 0⟩

theorem incompatible : ¬ bad.Compatible algebra observe := by
  intro h
  have he := congrArg (fun s : Convolution.Series Unit Nat => s [])
    (h.next .concat ![letter,empty] ())
  change 1 = 0 at he
  exact Nat.one_ne_zero he

example {X Y : Type} (f : X → Y) (xs : Fin 2 → X × B Unit Nat X) :
    bad.layer .concat (fun i => (f (xs i).1, (xs i).2.1, fun a => f ((xs i).2.2 a))) =
      ((bad.layer .concat xs).1, fun a => Term.map f ((bad.layer .concat xs).2 a)) :=
  bad.layer_natural f .concat xs
end RejectedRule

namespace IndexedVectors
/-- The size index is retained. This instance stays within one fiber at a time. -/
abbrev Vec (n : Nat) := Fin (n+1) → Nat

def observe (n : Nat) : Coalgebra Unit Nat (Vec n) :=
  fun xs => (xs 0, fun _ i => xs i.rev)

def doubling : Rule Unit (fun _ => 1) Unit Nat where
  out _ xs := 2 * xs 0
  step _ _ _ := .node () ![.leaf (.inr 0)]

def algebra (n : Nat) (_ : Unit) (xs : Fin 1 → Vec n) : Vec n := fun i => 2 * xs 0 i

theorem compatible (n : Nat) : doubling.Compatible (algebra n) (observe n) where
  output _ _ := rfl
  next _ _ _ := rfl

/-- All finite expressions of indexed vectors inherit the local doubling equation. -/
theorem composite (n : Nat) (t : Term Unit (fun _ => 1) (Vec n)) (w : List Unit) :
    run (doubling.lift (observe n)) t w =
      run (observe n) (Term.fold (algebra n) id t) w := by
  exact (run_transport _ _ _
    (doubling.fold_morphism (algebra n) (observe n) (compatible n) (observe n) id
      ⟨fun _ => rfl, fun _ _ => rfl⟩) t w).symm

def sample : Term Unit (fun _ => 1) (Vec 1) :=
  .node () ![.node () ![.leaf ![3,7]]]

example : run (doubling.lift (observe 1)) sample [] = 12 := by
  rw [composite]; rfl
example : run (doubling.lift (observe 1)) sample [()] = 28 := by
  rw [composite]; rfl
example : run (doubling.lift (observe 1)) sample [(),()] = 12 := by
  rw [composite]; rfl
end IndexedVectors
end CompositionalCoalgebraExamples

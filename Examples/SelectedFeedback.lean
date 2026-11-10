import SquareKit.SelectedFeedbackTransport

namespace Examples.SelectedFeedback
open SquareKit SquareKit.FunctionFeedback

def body (p : Unit × Bool) : Bool × Bool := (p.2, p.2)
def choice (s : Bool) : Witness body := fun _ => ⟨s, s, rfl⟩

theorem choices_differ : trace body (choice false) ≠ trace body (choice true) := by
  intro h
  exact Bool.false_ne_true (congrFun h ())

def inputSetoid : Setoid Bool := ⟨fun _ _ => True, ⟨fun _ => trivial,
  fun _ => trivial, fun _ _ => trivial⟩⟩
def setoidBody (p : Bool × Bool) : Bool × Bool := (p.2, p.2)
def inputChoice : Witness setoidBody := fun x => ⟨x, x, rfl⟩

theorem body_congruent (x x' s s' : Bool)
    (_hx : inputSetoid.r x x') (hs : s = s') :
    setoidBody (x,s) = setoidBody (x',s') := by cases hs; rfl

theorem selection_not_congruent :
    ¬ OutputCongruent inputSetoid.r Eq inputChoice := by
  intro h
  exact Bool.false_ne_true (h false true trivial)

def constantChoice : Witness setoidBody := fun _ => ⟨false, false, rfl⟩

theorem corrected_selection :
    ∀ x x', inputSetoid.r x x' →
      trace setoidBody constantChoice x = trace setoidBody constantChoice x' :=
  trace_congruent constantChoice (fun _ _ _ => rfl)

open SquareKit.GuardedStreams

def delayed (x : Nat) : Stream Nat → Stream Nat := cons x

def delayedWitness (seed : Nat) :
    Witness (fun p : Nat × Stream Nat => (p.2 3, delayed p.1 p.2)) :=
  guardedWitness delayed (fun _ s => s 3) cons_guarded seed

theorem delayed_output (seed x : Nat) : trace _ (delayedWitness seed) x = x := by
  change solve (cons x) seed 3 = x
  rw [seed_independent (cons_guarded x) seed x]
  exact congrFun (constantStream_eq x) 3

theorem every_delayed_choice
    (w : Witness (fun p : Nat × Stream Nat => (p.2 3, delayed p.1 p.2))) :
    trace _ w = id := by
  rw [guarded_trace_unique delayed (fun _ s => s 3) cons_guarded 0 w]
  funext x
  exact delayed_output 0 x

def paired := SquareKit.SelectedFeedback.product
  FunctionFeedback.selected FunctionFeedback.selected

theorem product_keeps_choices :
    (paired.trace (a := (Unit, Unit)) (b := (Bool, Bool)) (s := (Bool, Bool))
      (body, body) (choice false, choice true)).1 () = false ∧
    (paired.trace (a := (Unit, Unit)) (b := (Bool, Bool)) (s := (Bool, Bool))
      (body, body) (choice false, choice true)).2 () = true := ⟨rfl, rfl⟩

/-- A noninjective object function with a comparison that is not an iso. -/
def collapseComparison (_a _b : Bool) :
    Comparison FunctionCategory.ops Bool (Bool × Bool) :=
  ⟨fun x => (x,x), Prod.fst⟩

def collapsed := SquareKit.SelectedFeedback.reindex FunctionFeedback.selected
  (fun _ : Bool => Bool) (fun a b => a && b) collapseComparison

def collapsedWitness : collapsed.WF (a := false) (b := true) (s := false)
    (id : Bool → Bool) := fun x => ⟨x, x, rfl⟩

theorem reindex_output :
    collapsed.trace (a := false) (b := true) (s := false) id collapsedWitness = id := rfl

theorem comparison_not_inverse :
    ¬ ∀ p : Bool × Bool,
      (collapseComparison false false).hom ((collapseComparison false false).inv p) = p := by
  intro h
  have bad := congrArg Prod.snd (h (false,true))
  exact Bool.false_ne_true bad

end Examples.SelectedFeedback

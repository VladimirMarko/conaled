import Applications.FRP.Feedback
import Examples.TemporalFRP

namespace Examples.InitializedFeedback
open Progress Progress.Feedback

def p (a y x : Nat) := a+y+x
def q (_ x y : Nat) := x+y
def coupled := joint p q 0 0

def inputs : Stream Nat
  | 0 => 1
  | 1 => 2
  | _ => 1

/-- Independent arithmetic: (1,1), then (2+1+1,4+1), then (1+5+4,10+5). -/
example : wired p q 0 0 [1,2,1] = ([(1,1),(4,5),(10,15)],(10,15)) := by decide
example : prefixOf (output coupled inputs) 3 = [(1,1),(4,5),(10,15)] := by
  rw [show coupled = joint p q 0 0 from rfl, coupled_prefix]; decide
example (as : List Nat) : run coupled.mealy (0,0) as = wired p q 0 0 as :=
  factorization p q 0 0 as
example : CoupledSolution p q 0 0 inputs
    (fun n => (state coupled inputs n).1) (fun n => (state coupled inputs n).2) :=
  joint_solves p q 0 0 inputs
example (x y : Stream Nat) (h : CoupledSolution p q 0 0 inputs x y) :
    (fun n => (x n,y n)) = state coupled inputs := coupled_unique h
example : (fun n => (state coupled inputs (n+1)).1) =
    runStream (leftStage p) 0 (fun n => (inputs n,(state coupled inputs n).2)) :=
  left_stream (joint_solves p q 0 0 inputs)
example : (fun n => (state coupled inputs (n+1)).2) =
    runStream (rightStage q) 0 (fun n => (inputs n,(state coupled inputs (n+1)).1)) :=
  right_stream (joint_solves p q 0 0 inputs)
example : Temporal.Synchronous (output coupled) := causal coupled
example : DeliversWithin (mealyProcessor coupled.mealy (0,0)) (fun n => n+1) :=
  mealy_delivery _ _

/-- The same source state relates to two different target states. -/
def tagged (s : Nat × Nat) (t : (Nat × Nat) × Bool) : Prop := s = t.1
def decorated (tag : Bool) : Initialized Nat (Nat × Nat) ((Nat × Nat) × Bool) where
  initial := ((0,0),tag)
  step := fun (a,t) => let next := coupled.step (a,t.1); (next.1,(next.2,!t.2))

theorem decorated_step (tag : Bool) (a a' : Nat) (s : Nat × Nat) (t : (Nat × Nat) × Bool)
    (ha : a = a') (hs : tagged s t) :
    (coupled.step (a,s)).1 = ((decorated tag).step (a',t)).1 ∧
      tagged (coupled.step (a,s)).2 ((decorated tag).step (a',t)).2 := by
  subst a'; cases t with | mk t flag => cases hs; exact ⟨rfl,rfl⟩
example : tagged (0,0) ((0,0),false) ∧ tagged (0,0) ((0,0),true) ∧
    ((0,0),false) ≠ ((0,0),true) := by unfold tagged; decide

theorem decorated_prefix (tag : Bool) (a : Stream Nat) (n : Nat) :
    List.Forall₂ Eq (prefixOf (output coupled a) n) (prefixOf (output (decorated tag) a) n) :=
  prefix_related _ _ _ (transport coupled (decorated tag) Eq tagged Eq rfl
    (decorated_step tag) a a (fun _ => rfl)).2 n

def totals : Relational.RelSquare (streamRep (Eq : Nat × Nat → Nat × Nat → Prop))
    (streamRep (Eq : Nat → Nat → Prop)) where
  impl b n := (b n).1 + (b n).2
  spec b n := (b n).1 + (b n).2
  preserves h n := congrArg (fun z : Nat × Nat => z.1+z.2) (h n)

/-- A downstream observer composes through existing square laws. -/
example (tag : Bool) (a : Stream Nat) :
    ∀ n, (output coupled a n).1 + (output coupled a n).2 =
      (output (decorated tag) a n).1 + (output (decorated tag) a n).2 :=
  (Relational.compose totals (solutionSquare coupled (decorated tag) Eq tagged Eq rfl
    (decorated_step tag))).preserves (fun _ => rfl)

/-- The functional specialization also consumes the existing coalgebra law. -/
example (input : Progress.Coalgebra Nat Nat) (s : (Nat × Nat) × Bool) (seed n : Nat) :
    unfold (mealyCoalgebra coupled.mealy input) (s.1,seed) n =
      (unfold (mealyCoalgebra (decorated false).mealy input) (s,seed) n).map id :=
  producer_transport (decorated false).mealy coupled.mealy Prod.fst id
    (fun _ _ => rfl) input s seed n

example : ¬ ∃ b : Bool, b = !b := by rintro ⟨b,h⟩; cases b <;> cases h
example : (fun _ : Nat => false) ≠ (fun _ : Nat => true) ∧
    (∀ n, (fun _ : Nat => false) (n+1) = (fun _ => false) n) ∧
    (∀ n, (fun _ : Nat => true) (n+1) = (fun _ => true) n) := by
  refine ⟨?_,fun _ => rfl,fun _ => rfl⟩
  intro h; have := congrFun h 0; cases this
example : ¬ tagged (0,0) ((1,0),false) := by unfold tagged; decide
example : output (joint p q 0 0) inputs 0 ≠ output (joint p q 1 0) inputs 0 := by decide
example : ¬ (∀ a s t, tagged s t →
    tagged (coupled.step (a,s)).2 ((t.1.1+1,t.1.2),t.2)) := by
  intro h
  have bad := h 1 (0,0) ((0,0),false) rfl
  change (1,1) = (1,0) at bad
  cases bad

/-- Batch history keeps order/duplicates; empty deliveries still increment ticks. -/
def batches : Initialized (List Nat) (Nat × List Nat) (Nat × List Nat) where
  initial := (0,[])
  step := fun (xs,n,history) => ((n+1,history++xs),(n+1,history++xs))

open FRPSpec.Feedback
example : consume batches (0,[]) [none] = ([],(0,[])) := rfl
example : consume batches (0,[]) [some []] = ([(1,[])],(1,[])) := rfl
example : consume batches (0,[]) [none] ≠ consume batches (0,[]) [some []] := by decide
example : consume batches (0,[]) [some [3,3],none,some [],some [7]] =
    ([(1,[3,3]),(2,[3,3]),(3,[3,3,7])],(3,[3,3,7])) := by decide
example (xs ys : List (Option (List Nat))) :
    consume batches batches.initial (xs++ys) =
      let first := consume batches batches.initial xs
      let second := consume batches first.2 ys
      (first.1++second.1,second.2) := chunk _ _ _ _
example : (consume batches (0,[]) [none,some [],some [3,3]]).1 =
    prefixOf (output batches (fun n => if n=0 then [] else [3,3])) 2 :=
  stream_agreement _ _ _ 2 rfl

open FRPSpec.Frontier FRPSpec.Frontier.Trace FRPSpec.Frontier.Demand
open FRPSpec.Frontier.Demand.Temporal
open Examples.FRPTrace Examples.FRPDemand Examples.TemporalFRP

example : feedbackInputs start packets early 2 7 =
    [none,none,none,none,none,some [3,4,3],none] := by decide
example : consume batches batches.initial (feedbackInputs start packets early 2 7) =
    ([(1,[3,4,3])],(1,[3,4,3])) := by decide
example : (consume batches batches.initial (feedbackInputs start packets early 2 5)).1 = [] := by decide
example : (frame start packets early 2 6).observed = some [3,4,3] ∧
    frameBatch (frame start packets early 2 6) = none := by decide
example : consume batches batches.initial (feedbackInputs start packets emptyQuery 1 3) =
    ([(1,[])],(1,[])) := by decide

/-- Truth enters only through the existing honest response square. -/
example : consume batches batches.initial [frameBatch (frame start packets early 2 5)] =
    ([(1,truth .left 2 ++ truth .right 2)],(1,truth .left 2 ++ truth .right 2)) :=
  feedback_response start packets early 2 truth honest batches batches.initial 5 [3,4,3] (by decide)
example : consume batches batches.initial [frameBatch (frame start packets emptyQuery 1 1)] =
    ([(1,truth .left 1 ++ truth .right 1)],(1,truth .left 1 ++ truth .right 1)) :=
  feedback_response start packets emptyQuery 1 truth honest batches batches.initial 1 [] (by decide)

#eval consume batches batches.initial (feedbackInputs start packets early 2 7)
#eval consume batches batches.initial (feedbackInputs start packets emptyQuery 1 3)
end Examples.InitializedFeedback

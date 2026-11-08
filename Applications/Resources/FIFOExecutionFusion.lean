import Applications.Resources.FIFOContracts

/-! Native FIFO execution recovered through the existing finite-fold fusion
law. Cost comparisons remain separate from state preservation. -/
namespace Resources.FIFOContracts
open Sequences.AbstractFIFO
universe u
variable {α Q R : Type u}

theorem native_run_fold (ops : Ops α Q) (cs : List (Command α)) (q : Q) :
    Sequences.AbstractFIFO.run ops cs q = cs.foldl (fun q c => step ops c q) q := by
  induction cs generalizing q with
  | nil => rfl
  | cons c cs ih => exact ih _

theorem run_erases_via_fusion {ops : Ops α Q} (m : Instrumentation ops)
    (cs : List (Command α)) (q : Q) :
    (Resources.run m.measured cs q).1 = Sequences.AbstractFIFO.run ops cs q := by
  rw [native_run_fold]
  exact Resources.run_value_fusion m.measured (step ops) id (fun _ => True)
    (fun _ _ _ => trivial) (fun c q _ => m.erases c q) cs q trivial

/-- A changing representation exercises the decoder of generic fusion. -/
theorem run_decodes_via_fusion {ops : Ops α Q} {spec : Ops α R}
    (m : Instrumentation ops) (decode : Q → R)
    (h : Simulation ops spec (fun q r => decode q = r))
    (cs : List (Command α)) (q : Q) :
    decode (Resources.run m.measured cs q).1 = Sequences.AbstractFIFO.run spec cs (decode q) := by
  rw [native_run_fold]
  apply Resources.run_value_fusion m.measured (step spec) decode (fun _ => True)
    (fun _ _ _ => trivial) _ cs q trivial
  intro c q _
  rw [m.erases]
  cases c with
  | enqueue x => exact h.snoc x q (decode q) rfl
  | delete => exact h.tail q (decode q) rfl

abbrev redundant (α : Type u) : Ops α (List α × Nat) where
  empty := ([],0)
  snoc x q := (q.1 ++ [x],q.2+1)
  tail q := (q.1.tail,q.2+1)
  head q := q.1.head?

def redundantInstrumentation : Instrumentation (redundant α) where
  measured c q := (step (redundant α) c q,1)
  erases _ _ := rfl

theorem redundant_simulation : Simulation (redundant α) (lists α) (fun q r => q.1 = r) where
  empty := rfl
  snoc _ _ _ h := by cases h; rfl
  tail _ _ h := by cases h; rfl
  head _ _ h := by cases h; rfl

theorem redundant_run (cs : List (Command α)) (xs : List α) (flag : Nat) :
    (Resources.run redundantInstrumentation.measured cs (xs,flag)).1.1 =
      Sequences.AbstractFIFO.run (lists α) cs xs :=
  run_decodes_via_fusion redundantInstrumentation Prod.fst redundant_simulation cs (xs,flag)

/-- Equal values alone cannot transfer a cost-zero bound. -/
theorem value_equality_does_not_preserve_budget :
    (((),0) : Measured Unit Nat).1 = (((),1) : Measured Unit Nat).1 ∧
    (((),0) : Measured Unit Nat).2 ≤ 0 ∧ ¬ (((),1) : Measured Unit Nat).2 ≤ 0 := by
  decide

end Resources.FIFOContracts

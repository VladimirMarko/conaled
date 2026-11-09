import Applications.Orbifold.WiredMotionComparison
import Examples.NumericalMotion
import Examples.OpenSystemWiring

/-! A finite admitted motion comparison retaining native execution contracts. -/
namespace Examples.WiredNumericalMotion
open CategoryTheory
open Orbifold Orbifold.DiskTransport Orbifold.DiskTransport.Numerical
open Orbifold.DiskTransport.Numerical.Wired
open SquareKit.DiscreteApproximation
open NumericalMotion

abbrev coarsePacket (n : ℕ) := orbit (advance moveTick) initial n
abbrev finePacket (n : ℕ) := orbit (advance halfTick) initial n

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1000000 in
theorem coarse_admitted : ∀ n : Fin 3, Admissible moveTick (coarsePacket n) := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1000000 in
theorem fine_admitted : ∀ n : Fin 5, Admissible halfTick (finePacket n) := by decide +kernel

theorem coarse_domain (n : ℕ) (hn : n ≤ 2) : Domain (coarsePacket n).state.decode :=
  (admissible_domain (coarse_admitted ⟨n, by omega⟩)).1

theorem fine_domain (n : ℕ) (hn : n ≤ 4) : Domain (finePacket n).state.decode :=
  (admissible_domain (fine_admitted ⟨n, by omega⟩)).1

theorem coarse_bridge (n : ℕ) : (coarsePacket n).state.decode =
    orbit (euler (1/1024)) initial.state.decode n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (step (.move (1,0)) (1/1024) (coarsePacket n).state).decode = _
    rw [step_eq, ih]
    norm_num [orbit]

theorem fine_bridge (n : ℕ) : (finePacket n).state.decode =
    orbit (euler (1/2048)) initial.state.decode n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (step (.move (1,0)) (1/2048) (finePacket n).state).decode = _
    rw [step_eq, ih]
    norm_num [orbit]

theorem orbit_twice {S : Type*} (f : S → S) (s : S) (n : ℕ) :
    orbit (fun x => f (f x)) s n = orbit f s (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [orbit, ih, Nat.mul_succ, Nat.add_succ, Nat.add_zero]

theorem fine_sample_bridge (n : ℕ) :
    orbit (halfTwice (1/1024)) initial.state.decode n = (finePacket (2*n)).state.decode := by
  rw [fine_bridge]
  have h : (1/1024 : ℝ)/2 = 1/2048 := by norm_num
  change orbit (fun x => euler ((1/1024 : ℝ)/2) (euler ((1/1024 : ℝ)/2) x))
    initial.state.decode n = _
  rw [h]
  exact orbit_twice _ _ _

theorem safe_fixture : Safe (1/1024) initial.state.decode initial.state.decode 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    rw [fine_sample_bridge]
    exact fine_domain _ (by omega)
  · intro n hn
    rw [← coarse_bridge]
    exact coarse_domain n hn
  · intro n hn
    rw [fine_sample_bridge]
    have h : (1/1024 : ℝ)/2 = 1/2048 := by norm_num
    rw [h, fine_bridge]
    change Domain (orbit (euler (1/2048)) initial.state.decode (2*n+1))
    rw [← fine_bridge]
    exact fine_domain _ (by omega)

/-- Derived component error at each common sample, over duration 2/1024. -/
theorem sampled_comparison (n : ℕ) (hn : n ≤ 2) :
    dist (finePacket (2*n)).state.decode (coarsePacket n).state.decode ≤
      SquareKit.DiscreteApproximation.budget (1+12*(1/1024)) (6*(1/1024)^2) 0 n := by
  rw [coarse_bridge, ← fine_sample_bridge]
  exact comparison (by norm_num) safe_fixture (by simp) n hn

set_option maxRecDepth 30000 in
/-- A genuine defect, even though both routes are exact rational arithmetic. -/
theorem nonzero_defect : (finePacket 2).state ≠ (coarsePacket 1).state := by decide +kernel

set_option maxRecDepth 30000 in
theorem coarse_success : (run (List.replicate 2 moveTick) initial).isSome = true := by decide +kernel
set_option maxRecDepth 30000 in
theorem fine_success : (run (List.replicate 4 halfTick) initial).isSome = true := by decide +kernel

def coarseResult := (run (List.replicate 2 moveTick) initial).get coarse_success
def fineResult := (run (List.replicate 4 halfTick) initial).get fine_success

theorem coarse_run : run (List.replicate 2 moveTick) initial = some coarseResult :=
  (Option.some_get coarse_success).symm
theorem fine_run : run (List.replicate 4 halfTick) initial = some fineResult :=
  (Option.some_get fine_success).symm

/-- The existing continuous endpoint guarantee remains separate from refinement error. -/
theorem coarse_continuous : Approx coarseResult.final
    (moveTick.control.decode.trajectory initialPose (2/1024)) := by
  have h := run_interval_correct moveTick 2 coarse_run initial_approx
  norm_num [moveTick] at h ⊢
  exact h

theorem fine_continuous : Approx fineResult.final
    (moveTick.control.decode.trajectory initialPose (2/1024)) := by
  have h := run_interval_correct halfTick 4 fine_run initial_approx
  norm_num [halfTick, moveTick] at h ⊢
  exact h

theorem samples_and_domains :
    List.Forall₂ Approx fineResult.samples (endpoints initialPose (List.replicate 4 halfTick)) ∧
    List.Forall (fun q => Domain q.state.decode) fineResult.samples :=
  (run_correct fine_run initial_approx).2

/-- The native Option and action-category map retain failure and the selected C4 label. -/
theorem symmetry (g : Orbifolds.QuarterTurn.C4) :
    run (List.replicate 4 halfTick) (g • initial) = g • run (List.replicate 4 halfTick) initial :=
  run_equivariant _ _ _

theorem selected_label {p q : CategoryTheory.ActionCategory Orbifolds.QuarterTurn.C4 Packet}
    (a : p ⟶ q) : ((executionFunctor (List.replicate 4 halfTick)).map a).hom = a.hom :=
  execution_label _ a

theorem outside_domain : checkedStep moveTick ⟨⟨(3/4,0),(1/2,0)⟩,0⟩ = none :=
  outside_rejected

set_option maxRecDepth 30000 in
theorem returned_states : coarseResult.final = coarsePacket 2 ∧ fineResult.final = finePacket 4 := by
  decide +kernel

theorem returned_comparison :
    dist fineResult.final.state.decode coarseResult.final.state.decode ≤
      SquareKit.DiscreteApproximation.budget (1+12*(1/1024)) (6*(1/1024)^2) 0 2 := by
  rw [returned_states.1, returned_states.2]
  exact sampled_comparison 2 le_rfl

theorem decoded_defect : (finePacket 2).state.decode ≠ (coarsePacket 1).state.decode :=
  fun h => nonzero_defect (State.decode_injective h)

theorem equal_clock : coarseResult.elapsed = 2/1024 ∧ fineResult.elapsed = 2/1024 := by
  rw [run_clock coarse_run, run_clock fine_run]
  norm_num [clock, moveTick, halfTick]

/-- State-only wiring does not solve an instantaneous equation with no solution. -/
theorem invalid_feedthrough : ¬ ∃ i : ℝ, i = i+1 :=
  OpenSystemWiring.feedthrough_feedback_unsolvable

end Examples.WiredNumericalMotion

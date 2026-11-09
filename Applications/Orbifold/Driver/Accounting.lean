import Applications.Orbifold.Driver.Soundness

namespace Orbifold.DiskTransport.Numerical.Driver

theorem drive_elapsed (limits : Limits) (tolerance : ℚ) (es : List Event)
    (q : Packet) (fuel index : Nat) :
    (drive limits tolerance es q fuel index).elapsed =
      ((drive limits tolerance es q fuel index).observations.map Observation.elapsed).sum := by
  induction es generalizing q fuel index with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | relabel k =>
      simp only [drive]
      split
      · rfl
      · simpa [prepend] using congrArg ((Observation.relabel k q).elapsed + ·) (ih _ _ _)
    | command c =>
      simp only [drive]
      split
      · rfl
      · split
        · rfl
        · rename_i s hs
          simpa [prepend] using congrArg ((Observation.command c s.predecessor q s.execution).elapsed + ·) (ih _ _ _)

theorem success_clock (limits : Limits) (tolerance : ℚ) (es : List Event)
    (q : Packet) (fuel index : Nat)
    (h : (drive limits tolerance es q fuel index).failure = none) :
    (drive limits tolerance es q fuel index).elapsed = eventClock es := by
  rw [drive_elapsed,chain_clock (drive_chain limits tolerance es q fuel index)]
  have HP := drive_partition limits tolerance es q fuel index
  rw [(drive_success limits tolerance es q fuel index h).1,List.append_nil] at HP
  rw [HP]

theorem drive_work (limits : Limits) (tolerance : ℚ) (es : List Event)
    (q : Packet) (fuel index : Nat) :
    (drive limits tolerance es q fuel index).counts.1 ≤
      (drive limits tolerance es q fuel index).charged ∧
    (drive limits tolerance es q fuel index).charged ≤ fuel := by
  induction es generalizing q fuel index with
  | nil => simp [drive]
  | cons e es ih =>
    cases e with
    | relabel k =>
      simp only [drive]
      split
      · simp [stopped]
      · have H := ih (q.rotate k.val) (fuel-1) (index+1)
        simp only [prepend]
        omega
    | command c =>
      have HA := search_work_bound limits tolerance fuel c q
      simp only [drive]
      split
      · simp [stopped]
      · split
        · exact HA
        · rename_i s hs
          have HB := ih s.execution.final (fuel-(searchInterval limits tolerance fuel c q).charged) (index+1)
          simp only [Prod.fst_add]
          omega

end Orbifold.DiskTransport.Numerical.Driver

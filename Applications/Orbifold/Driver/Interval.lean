import Applications.Orbifold.Driver.Guarded

namespace Orbifold.DiskTransport.Numerical.Driver
open Resources

structure Limits where
  rounds : Nat
  packetBitLimit : Nat
  deriving Repr

/-- Evidence is acquired from the actual guarded executor, not requested from the caller. -/
structure Selected (c : Tick) (q : Packet) (tolerance : ℚ) where
  predecessor : Nat
  execution : Result
  ran : Numerical.run (schedule c predecessor) q = some execution
  within : execution.final.error ≤ tolerance

def Selected.subdivisions {c q tolerance} (s : Selected c q tolerance) := s.predecessor+1

structure AttemptLog where
  subdivisions : Nat
  counts : AttemptCounts
  finalError : Option ℚ
  reason : Failure
  deriving Repr

structure SearchReport (c : Tick) (q : Packet) (tolerance : ℚ) where
  accepted : Option (Selected c q tolerance)
  counts : AttemptCounts
  charged : Nat
  attempts : List AttemptLog
  failure : Failure

/-- Reserve each planned tick and one search decision. Actual measured attempts are
reported separately, including work abandoned by rejection or failed accuracy. -/
def searchCandidates (cap : Nat) (tolerance : ℚ) (c : Tick) (q : Packet) :
    List Nat → Nat → Failure → SearchReport c q tolerance
  | [], _, last => ⟨none,0,0,[],last⟩
  | n::ns, fuel, _ =>
    if n+2 > fuel then ⟨none,0,0,[],.work⟩ else
    let a := guarded cap (schedule c n) q
    match ha : a.accepted with
    | some r =>
      if ht : r.final.error ≤ tolerance then
        ⟨some ⟨n,r,guarded_sound cap (schedule c n) q ha,ht⟩,
          a.counts,n+2,[⟨n+1,a.counts,some r.final.error,.accuracy⟩],.accuracy⟩
      else
        let rest := searchCandidates cap tolerance c q ns (fuel-(n+2)) .accuracy
        ⟨rest.accepted,a.counts+rest.counts,n+2+rest.charged,
          ⟨n+1,a.counts,some r.final.error,.accuracy⟩::rest.attempts,rest.failure⟩
    | none =>
      if a.failure == .packetBits then
        ⟨none,a.counts,n+2,[⟨n+1,a.counts,none,.packetBits⟩],.packetBits⟩
      else
        let rest := searchCandidates cap tolerance c q ns (fuel-(n+2)) a.failure
        ⟨rest.accepted,a.counts+rest.counts,n+2+rest.charged,
          ⟨n+1,a.counts,none,a.failure⟩::rest.attempts,rest.failure⟩

def searchInterval (limits : Limits) (tolerance : ℚ) (fuel : Nat) (c : Tick) (q : Packet) :
    SearchReport c q tolerance :=
  searchCandidates limits.packetBitLimit tolerance c q
    ((List.range limits.rounds).map (fun k => 2^k-1)) fuel .accuracy

theorem selected_sound {c : Tick} {q : Packet} {tolerance : ℚ} (s : Selected c q tolerance)
    {p : Pose} (hp : Approx q p) :
    Approx s.execution.final (c.decode.finish p) ∧
    List.Forall₂ Approx s.execution.samples (endpoints p (schedule c s.predecessor)) ∧
    List.Forall (fun v => Domain v.state.decode) s.execution.samples ∧
    s.execution.elapsed = c.duration ∧ s.execution.final.error ≤ tolerance := by
  have H := Numerical.run_correct s.ran hp
  rw [schedule_execute] at H
  exact ⟨H.1,H.2.1,H.2.2,(Numerical.run_clock s.ran).trans (schedule_clock _ _),s.within⟩

theorem selected_error {c : Tick} {q : Packet} {tolerance : ℚ} (s : Selected c q tolerance) :
    s.execution.final.error = errorAfter (schedule c s.predecessor) q.error :=
  Numerical.run_error s.ran

theorem searchCandidates_bounds (cap : Nat) (tolerance : ℚ) (c : Tick) (q : Packet)
    (ns : List Nat) (fuel : Nat) (last : Failure) :
    (searchCandidates cap tolerance c q ns fuel last).charged ≤ fuel ∧
    (searchCandidates cap tolerance c q ns fuel last).counts.1 ≤
      (searchCandidates cap tolerance c q ns fuel last).charged := by
  induction ns generalizing fuel last with
  | nil => simp [searchCandidates]
  | cons n ns ih =>
    have hg := guarded_counts cap (schedule c n) q
    rw [schedule_length] at hg
    simp only [searchCandidates]
    split
    · simp
    · have H := ih (fuel-(n+2)) .accuracy
      have H' := ih (fuel-(n+2)) (guarded cap (schedule c n) q).failure
      split
      · split
        · simp only
          omega
        · simp only [Prod.fst_add]
          omega
      · split
        · simp only
          omega
        · simp only [Prod.fst_add]
          omega

theorem search_work_bound (limits : Limits) (tolerance : ℚ) (fuel : Nat) (c : Tick) (q : Packet) :
    (searchInterval limits tolerance fuel c q).counts.1 ≤
      (searchInterval limits tolerance fuel c q).charged ∧
    (searchInterval limits tolerance fuel c q).charged ≤ fuel := by
  have H := searchCandidates_bounds limits.packetBitLimit tolerance c q
    ((List.range limits.rounds).map (fun k => 2^k-1)) fuel .accuracy
  exact ⟨H.2,H.1⟩

end Orbifold.DiskTransport.Numerical.Driver

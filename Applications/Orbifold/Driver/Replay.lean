import Applications.Orbifold.Driver.Accounting

namespace Orbifold.DiskTransport.Numerical.Driver
open Orbifold.QuarterTurn

@[simp] theorem ratBits_neg (q : ℚ) : ratBits (-q) = ratBits q := by
  simp [ratBits]

@[simp] theorem packetBits_turn (q : Packet) : packetBits q.turn = packetBits q := by
  simp only [packetBits,Packet.turn,State.turn,QComplex.turn,List.foldl_cons,List.foldl_nil,
    ratBits_neg]
  ac_rfl

@[simp] theorem packetBits_rotate (k : Nat) (q : Packet) : packetBits (q.rotate k) = packetBits q := by
  induction k generalizing q with
  | zero => rfl
  | succ k ih =>
    have he : q.rotate (k+1) = (q.rotate k).turn := by
      simp [Packet.rotate,State.rotate,Packet.turn,Function.iterate_succ_apply']
    rw [he,packetBits_turn,ih]

@[simp] theorem packetBits_action (g : C4) (q : Packet) : packetBits (g • q) = packetBits q :=
  packetBits_rotate (Orbifolds.QuarterTurn.scalar_eq_pow g).choose q

@[simp] theorem result_action_final (g : C4) (r : Result) : (g • r).final = g • r.final := rfl
@[simp] theorem result_action_samples (g : C4) (r : Result) : (g • r).samples = r.samples.map (g • ·) := rfl
@[simp] theorem result_action_elapsed (g : C4) (r : Result) : (g • r).elapsed = r.elapsed := rfl
@[simp] theorem result_action_mk (g : C4) (q : Packet) (qs : List Packet) (t : ℚ) :
    g • Result.mk q qs t = Result.mk (g • q) (qs.map (g • ·)) t := rfl

theorem measured_action (g : C4) (cs : List Tick) (q : Packet) :
    Measured.run cs (g • q) = ((Measured.run cs q).1.map (g • ·),(Measured.run cs q).2) := by
  induction cs generalizing q with
  | nil => rfl
  | cons c cs ih =>
    simp only [Measured.run,checkedStep_equivariant]
    cases hs : checkedStep c q with
    | none => rfl
    | some s =>
      simp only [Option.map_some]
      rw [ih]
      cases hr : Measured.run cs s with
      | mk a cost =>
        cases a <;> simp [Measured.prepend,List.map_cons,Option.map_map,Function.comp_def]

noncomputable def Attempt.act (g : C4) (a : Attempt) : Attempt :=
  ⟨a.accepted.map (g • ·),a.counts,a.failure⟩

theorem guarded_action (g : C4) (cap : Nat) (cs : List Tick) (q : Packet) :
    guarded cap cs (g • q) = (guarded cap cs q).act g := by
  induction cs generalizing q with
  | nil => rfl
  | cons c cs ih =>
    simp only [guarded,packetBits_action,measured_action]
    split
    · rfl
    · cases ha : (Measured.run [c] q).1 with
      | none => simp [ha,Attempt.act]
      | some a =>
        simp only [ha,Option.map_some]
        change (if packetBits (g • a.final) > cap then _ else _) = _
        rw [packetBits_action]
        split
        · rfl
        · simp only [result_action_final]
          rw [ih]
          cases hb : (guarded cap cs a.final).accepted <;>
            simp [hb,Attempt.act,Measured.combine,Option.map_map,Function.comp_def]

@[simp] theorem packet_action_error (g : C4) (q : Packet) : (g • q).error = q.error := rfl

noncomputable def Selected.act (g : C4) {c : Tick} {q : Packet} {tolerance : ℚ}
    (s : Selected c q tolerance) : Selected c (g • q) tolerance where
  predecessor := s.predecessor
  execution := g • s.execution
  ran := by rw [run_equivariant,s.ran]; rfl
  within := s.within

noncomputable def SearchReport.act (g : C4) {c : Tick} {q : Packet} {tolerance : ℚ}
    (r : SearchReport c q tolerance) : SearchReport c (g • q) tolerance :=
  ⟨r.accepted.map (Selected.act g),r.counts,r.charged,r.attempts,r.failure⟩

theorem searchCandidates_action (g : C4) (cap : Nat) (tolerance : ℚ) (c : Tick) (q : Packet)
    (ns : List Nat) (fuel : Nat) (last : Failure) :
    searchCandidates cap tolerance c (g • q) ns fuel last =
      (searchCandidates cap tolerance c q ns fuel last).act g := by
  induction ns generalizing fuel last with
  | nil => rfl
  | cons n ns ih =>
    by_cases hf : n+2 > fuel
    · simp [searchCandidates,hf,SearchReport.act]
    · cases ha : (guarded cap (schedule c n) q).accepted with
      | none =>
        have hr : (guarded cap (schedule c n) (g • q)).accepted = none := by
          rw [guarded_action]
          simp [Attempt.act,ha]
        by_cases hb : (guarded cap (schedule c n) q).failure == .packetBits
        all_goals simp [searchCandidates,hf,ha,hb,guarded_action,Attempt.act,SearchReport.act,ih]
      | some r =>
        have hr : (guarded cap (schedule c n) (g • q)).accepted = some (g • r) := by
          rw [guarded_action]
          simp [Attempt.act,ha]
        by_cases ht : r.final.error ≤ tolerance
        · simp [searchCandidates,hf,ha,ht,guarded_action,Attempt.act,SearchReport.act,Selected.act]
        · simp [searchCandidates,hf,ha,ht,guarded_action,Attempt.act,SearchReport.act,ih]

theorem searchInterval_action (g : C4) (limits : Limits) (tolerance : ℚ) (fuel : Nat)
    (c : Tick) (q : Packet) :
    searchInterval limits tolerance fuel c (g • q) =
      (searchInterval limits tolerance fuel c q).act g :=
  searchCandidates_action g _ _ _ _ _ _ _

end Orbifold.DiskTransport.Numerical.Driver

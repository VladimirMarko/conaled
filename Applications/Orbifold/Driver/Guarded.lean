import Applications.Orbifold.Driver.Schedule

namespace Orbifold.DiskTransport.Numerical.Driver
open Resources

inductive Failure where
  | domain | accuracy | work | packetBits | unsupported
  deriving DecidableEq, Repr, BEq

def ratBits (q : ℚ) : Nat := max (q.num.natAbs.log2+1) (q.den.log2+1)
def packetBits (q : Packet) : Nat :=
  [q.state.position.1,q.state.position.2,q.state.frame.1,q.state.frame.2,q.error].foldl
    (fun n r => max n (ratBits r)) 0

structure Attempt where
  accepted : Option Result
  counts : AttemptCounts
  failure : Failure
  deriving Repr

/-- One measured backend invocation at a time; the bit guard is not a bit-operation price. -/
def guarded (cap : Nat) : List Tick → Packet → Attempt
  | [], q => ⟨some ⟨q,[],0⟩,0,.accuracy⟩
  | c::cs, q =>
    if packetBits q > cap then ⟨none,0,.packetBits⟩ else
    let a := Measured.run [c] q
    match a.1 with
    | none => ⟨none,a.2,.domain⟩
    | some s =>
      if packetBits s.final > cap then ⟨none,a.2,.packetBits⟩ else
      let b := guarded cap cs s.final
      ⟨b.accepted.map (Measured.combine s),a.2+b.counts,b.failure⟩

theorem guarded_sound (cap : Nat) (cs : List Tick) (q : Packet) {r : Result}
    (h : (guarded cap cs q).accepted = some r) : Numerical.run cs q = some r := by
  induction cs generalizing q r with
  | nil => simpa [guarded,Numerical.run] using h
  | cons c cs ih =>
    simp only [guarded] at h
    split at h
    · simp at h
    · cases ha : (Measured.run [c] q).1 with
      | none => simp [ha] at h
      | some a =>
        simp only [ha] at h
        split at h
        · simp at h
        · obtain ⟨b,hb,hr⟩ := Option.map_eq_some_iff.mp h
          have HB := ih _ hb
          have HA : Numerical.run [c] q = some a := (Measured.run_erases _ _).symm.trans ha
          have H := Numerical.run_append [c] cs q
          simp only [List.singleton_append] at H
          rw [H]
          simp [HA,HB,←hr,Measured.combine]

theorem guarded_counts (cap : Nat) (cs : List Tick) (q : Packet) :
    (guarded cap cs q).counts.1 ≤ cs.length := by
  induction cs generalizing q with
  | nil => simp [guarded]
  | cons c cs ih =>
    simp only [guarded]
    split
    · simp
    · have ha := (Measured.run_counts [c] q).2.2
      cases he : (Measured.run [c] q).1 with
      | none => simp only [he]; exact ha.trans (by simp)
      | some a =>
        simp only [he]
        split
        · simpa using ha.trans (by simp)
        · have hb := ih a.final
          simp only [Prod.fst_add,List.length_cons]
          change (Measured.run [c] q).2.1 + (guarded cap cs a.final).counts.1 ≤ cs.length+1
          simp only [List.length_singleton] at ha
          omega

end Orbifold.DiskTransport.Numerical.Driver

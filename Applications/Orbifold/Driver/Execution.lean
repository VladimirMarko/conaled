import Applications.Orbifold.Driver.Events

namespace Orbifold.DiskTransport.Numerical.Driver
open Resources

structure Report where
  final : Packet
  observations : List Observation
  pending : List Event
  elapsed : ℚ
  failure : Option Failure
  counts : AttemptCounts
  charged : Nat
  searches : List (Nat × List AttemptLog)
  deriving Repr

def stopped (q : Packet) (es : List Event) (why : Failure) : Report :=
  ⟨q,[],es,0,some why,0,0,[]⟩

def prepend (o : Observation) (r : Report) : Report :=
  { r with observations := o::r.observations, elapsed := o.elapsed+r.elapsed }

def supported (c : Tick) : Prop := c.control.velocity.normSq ≤ 1 ∧ |c.control.angular| ≤ 1
instance (c : Tick) : Decidable (supported c) := by unfold supported; infer_instance

/-- Committed observations come only from accepted intervals; retries receive the same q. -/
def drive (limits : Limits) (tolerance : ℚ) : List Event → Packet → Nat → Nat → Report
  | [], q, _, _ =>
    ⟨q,[],[],0,if q.error ≤ tolerance then none else some .accuracy,0,0,[]⟩
  | .relabel k::es, q, fuel, index =>
    if fuel = 0 then stopped q (.relabel k::es) .work else
    let rest := drive limits tolerance es (q.rotate k.val) (fuel-1) (index+1)
    { prepend (.relabel k q) rest with charged := 1+rest.charged }
  | .command c::es, q, fuel, index =>
    if ¬ supported c then stopped q (.command c::es) .unsupported else
    let a := searchInterval limits tolerance fuel c q
    match a.accepted with
    | none => { stopped q (.command c::es) a.failure with
        counts := a.counts,charged := a.charged,searches := [(index,a.attempts)] }
    | some s =>
      let rest := drive limits tolerance es s.execution.final (fuel-a.charged) (index+1)
      { prepend (.command c s.predecessor q s.execution) rest with
        counts := a.counts+rest.counts,charged := a.charged+rest.charged,
        searches := (index,a.attempts)::rest.searches }

def Chain : Packet → List Observation → Packet → Prop
  | q, [], final => final = q
  | q, o::os, final => o.incoming = q ∧ o.Valid ∧ Chain o.outgoing os final

theorem drive_chain (limits : Limits) (tolerance : ℚ) (es : List Event)
    (q : Packet) (fuel index : Nat) :
    Chain q (drive limits tolerance es q fuel index).observations
      (drive limits tolerance es q fuel index).final := by
  induction es generalizing q fuel index with
  | nil => simp [drive,Chain]
  | cons e es ih =>
    cases e with
    | relabel k =>
      simp only [drive]
      split
      · rfl
      · exact ⟨rfl,trivial,ih _ _ _⟩
    | command c =>
      simp only [drive]
      split
      · rfl
      · split
        · rfl
        · rename_i s hs
          exact ⟨rfl,s.ran,ih _ _ _⟩

theorem drive_partition (limits : Limits) (tolerance : ℚ) (es : List Event)
    (q : Packet) (fuel index : Nat) :
    (drive limits tolerance es q fuel index).observations.map Observation.event ++
      (drive limits tolerance es q fuel index).pending = es := by
  induction es generalizing q fuel index with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | relabel k =>
      simp only [drive]
      split
      · rfl
      · simpa [prepend,Observation.event] using congrArg (Event.relabel k :: ·) (ih _ _ _)
    | command c =>
      simp only [drive]
      split
      · rfl
      · split
        · rfl
        · rename_i s hs
          simpa [prepend,Observation.event] using congrArg (Event.command c :: ·) (ih _ _ _)

theorem drive_success (limits : Limits) (tolerance : ℚ) (es : List Event)
    (q : Packet) (fuel index : Nat)
    (h : (drive limits tolerance es q fuel index).failure = none) :
    (drive limits tolerance es q fuel index).pending = [] ∧
    (drive limits tolerance es q fuel index).final.error ≤ tolerance := by
  induction es generalizing q fuel index with
  | nil => simpa [drive] using h
  | cons e es ih =>
    cases e with
    | relabel k =>
      by_cases hf : fuel = 0
      · simp [drive,hf,stopped] at h
      · simp only [drive,if_neg hf] at h ⊢
        exact ih _ _ _ h
    | command c =>
      by_cases hc : supported c
      · simp only [drive,hc,not_true_eq_false,if_false] at h ⊢
        cases ha : (searchInterval limits tolerance fuel c q).accepted with
        | none => simp [ha,stopped] at h
        | some s =>
          simp only [ha] at h ⊢
          exact ih _ _ _ h
      · simp [drive,hc,stopped] at h

end Orbifold.DiskTransport.Numerical.Driver

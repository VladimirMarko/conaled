import Applications.Orbifold.BoundedMotion.Execution
import Applications.Orbifold.Driver.Execution

namespace Orbifold.DiskTransport.Numerical.Bounded.Driver
open Numerical.Driver (Event Label schedule schedule_clock schedule_execute executeEvents eventClock)

structure Limits where
  rounds : Nat
  deriving Repr

/-- This witness names the bounded executor; the rational driver's witness remains unchanged. -/
structure Selected (c : Tick) (q : Packet) (tolerance : ℚ) where
  predecessor : Nat
  execution : Result
  ran : Bounded.run (schedule c predecessor) q = .ok execution
  within : rational execution.final.error ≤ tolerance

structure AttemptLog where
  subdivisions : Nat
  attemptedTicks : Nat
  finalError : Option ℚ
  outcome : Option Failure
  deriving Repr

structure SearchReport (c : Tick) (q : Packet) (tolerance : ℚ) where
  accepted : Option (Selected c q tolerance)
  charged : Nat
  attempts : List AttemptLog
  failure : Failure

/-- Each retry starts at q, even after a partially executed rejected schedule. -/
def searchCandidates (tolerance : ℚ) (c : Tick) (q : Packet) :
    List Nat → Nat → Failure → SearchReport c q tolerance
  | [], _, last => ⟨none, 0, [], last⟩
  | n :: ns, fuel, _ =>
    if n + 2 > fuel then ⟨none, 0, [], .work⟩ else
    let a := runMeasured (schedule c n) q
    match ha : a.1 with
    | .ok r =>
      if ht : rational r.final.error ≤ tolerance then
        ⟨some ⟨n, r, (runMeasured_erases _ _).symm.trans ha, ht⟩,
          n + 2, [⟨n+1, a.2, some (rational r.final.error), none⟩], .accuracy⟩
      else
        let rest := searchCandidates tolerance c q ns (fuel-(n+2)) .accuracy
        ⟨rest.accepted, n+2+rest.charged,
          ⟨n+1, a.2, some (rational r.final.error), some .accuracy⟩ :: rest.attempts, rest.failure⟩
    | .error reason =>
      let rest := searchCandidates tolerance c q ns (fuel-(n+2)) reason
      ⟨rest.accepted, n+2+rest.charged,
        ⟨n+1, a.2, none, some reason⟩ :: rest.attempts, rest.failure⟩

def searchInterval (limits : Limits) (tolerance : ℚ) (fuel : Nat) (c : Tick) (q : Packet) :
    SearchReport c q tolerance :=
  searchCandidates tolerance c q ((List.range limits.rounds).map (fun k => 2^k-1)) fuel .accuracy

theorem search_singleton_isSome (tolerance : ℚ) (c : Tick) (q : Packet)
    (n fuel : Nat) (hf : n+2 ≤ fuel) (r : Result)
    (hr : (runMeasured (schedule c n) q).1 = .ok r) :
    (searchCandidates tolerance c q [n] fuel .accuracy).accepted.isSome =
      decide (rational r.final.error ≤ tolerance) := by
  unfold searchCandidates
  split
  · omega
  · dsimp only
    split
    · rename_i out hout
      have he : out = r := Except.ok.inj (hout.symm.trans hr)
      subst out
      split <;> simp_all [searchCandidates]
    · rename_i err herr
      rw [herr] at hr
      cases hr

theorem selected_sound {c : Tick} {q : Packet} {tolerance : ℚ} (s : Selected c q tolerance)
    {p : Pose} (hp : Approx q.rational p) :
    Approx s.execution.final.rational (c.decode.finish p) ∧
    List.Forall₂ (fun q p => Approx q.rational p) s.execution.samples (endpoints p (schedule c s.predecessor)) ∧
    List.Forall (fun v => Domain v.state.rational.decode) s.execution.samples ∧
    s.execution.elapsed = c.duration ∧ rational s.execution.final.error ≤ tolerance := by
  have h := Bounded.run_correct s.ran hp
  rw [schedule_execute] at h
  exact ⟨h.1, h.2.1, h.2.2, (Bounded.run_clock s.ran).trans (schedule_clock _ _), s.within⟩

inductive Observation where
  | command (c : Tick) (predecessor : Nat) (incoming : Packet) (execution : Result)
  | relabel (k : Label) (incoming : Packet)
  deriving Repr

def Observation.event : Observation → Event
  | .command c _ _ _ => .command c
  | .relabel k _ => .relabel k

def Observation.incoming : Observation → Packet
  | .command _ _ q _ => q
  | .relabel _ q => q

def Observation.outgoing : Observation → Packet
  | .command _ _ _ r => r.final
  | .relabel k q => q.rotate k.val

def Observation.elapsed : Observation → ℚ
  | .command _ _ _ r => r.elapsed
  | .relabel _ _ => 0

def Observation.Valid : Observation → Prop
  | .command c n q r => Bounded.run (schedule c n) q = .ok r
  | .relabel _ _ => True

theorem observation_correct (o : Observation) (ho : o.Valid) {p : Pose}
    (hp : Approx o.incoming.rational p) : Approx o.outgoing.rational (o.event.finish p) := by
  cases o with
  | command c n q r => simpa [Observation.outgoing, Observation.event, Numerical.Driver.Event.finish, schedule_execute]
      using (Bounded.run_correct ho hp).1
  | relabel k q => exact (Bounded.rotate_approx k q p).mpr hp

theorem observation_clock (o : Observation) (ho : o.Valid) : o.elapsed = o.event.duration := by
  cases o with
  | command c n q r => exact (Bounded.run_clock ho).trans (schedule_clock c n)
  | relabel k q => rfl

structure Report where
  final : Packet
  observations : List Observation
  pending : List Event
  elapsed : ℚ
  failure : Option Failure
  charged : Nat
  searches : List (Nat × List AttemptLog)
  deriving Repr

def stopped (q : Packet) (es : List Event) (why : Failure) : Report :=
  ⟨q, [], es, 0, some why, 0, []⟩

def prepend (o : Observation) (r : Report) : Report :=
  { r with observations := o :: r.observations, elapsed := o.elapsed + r.elapsed }

/-- Only a whole certified interval is committed; relabel events retain their exact label. -/
def drive (limits : Limits) (tolerance : ℚ) : List Event → Packet → Nat → Nat → Report
  | [], q, _, _ =>
    ⟨q, [], [], 0, if rational q.error ≤ tolerance then none else some .accuracy, 0, []⟩
  | .relabel k :: es, q, fuel, index =>
    if fuel = 0 then stopped q (.relabel k :: es) .work else
    let rest := drive limits tolerance es (q.rotate k.val) (fuel-1) (index+1)
    { prepend (.relabel k q) rest with charged := 1+rest.charged }
  | .command c :: es, q, fuel, index =>
    if ¬ Numerical.Driver.supported c then stopped q (.command c :: es) .unsupported else
    let a := searchInterval limits tolerance fuel c q
    match a.accepted with
    | none => { stopped q (.command c :: es) a.failure with
        charged := a.charged, searches := [(index, a.attempts)] }
    | some s =>
      let rest := drive limits tolerance es s.execution.final (fuel-a.charged) (index+1)
      { prepend (.command c s.predecessor q s.execution) rest with
        charged := a.charged+rest.charged, searches := (index, a.attempts) :: rest.searches }

def Chain : Packet → List Observation → Packet → Prop
  | q, [], final => final = q
  | q, o :: os, final => o.incoming = q ∧ o.Valid ∧ Chain o.outgoing os final

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
    rational (drive limits tolerance es q fuel index).final.error ≤ tolerance := by
  induction es generalizing q fuel index with
  | nil => simpa [drive] using h
  | cons e es ih =>
    cases e with
    | relabel k =>
      by_cases hf : fuel = 0
      · simp [drive,hf,stopped] at h
      · simp only [drive,ite_eq_right hf] at h ⊢
        exact ih _ _ _ h
    | command c =>
      by_cases hc : Numerical.Driver.supported c
      · simp only [drive,hc,not_true_eq_false,ite_false] at h ⊢
        cases ha : (searchInterval limits tolerance fuel c q).accepted with
        | none => simp [ha,stopped] at h
        | some s =>
          simp only [ha] at h ⊢
          exact ih _ _ _ h
      · simp [drive,hc,stopped] at h

def SampleSound (p : Pose) : Observation → Prop
  | .relabel _ _ => True
  | .command c n _ r =>
    List.Forall₂ (fun q p => Approx q.rational p) r.samples (endpoints p (schedule c n)) ∧
    List.Forall (fun s => Domain s.state.rational.decode) r.samples

def TraceSound : Pose → List Observation → Prop
  | _, [] => True
  | p, o::os => SampleSound p o ∧ TraceSound (o.event.finish p) os

theorem chain_correct {q final : Packet} {os : List Observation} (hc : Chain q os final)
    {p : Pose} (hp : Approx q.rational p) :
    Approx final.rational (executeEvents (os.map Observation.event) p) ∧ TraceSound p os := by
  induction os generalizing q p with
  | nil => cases hc; exact ⟨hp,trivial⟩
  | cons o os ih =>
    obtain ⟨hs,ho,ht⟩ := hc
    have hp' : Approx o.incoming.rational p := by rwa [hs]
    have H := ih ht (observation_correct o ho hp')
    refine ⟨H.1,?_,H.2⟩
    cases o with
    | relabel k q => trivial
    | command c n q r =>
      have hc' := Bounded.run_correct ho hp'
      exact ⟨hc'.2.1,hc'.2.2⟩

theorem chain_clock {q final : Packet} {os : List Observation} (hc : Chain q os final) :
    (os.map Observation.elapsed).sum = eventClock (os.map Observation.event) := by
  induction os generalizing q with
  | nil => rfl
  | cons o os ih =>
    obtain ⟨_,ho,ht⟩ := hc
    simp only [List.map_cons,List.sum_cons,eventClock]
    rw [observation_clock o ho]
    exact congrArg (o.event.duration + ·) (ih ht)

theorem success_sound (limits : Limits) (tolerance : ℚ) (es : List Event)
    (q : Packet) (fuel index : Nat) {p : Pose} (hp : Approx q.rational p)
    (hs : (drive limits tolerance es q fuel index).failure = none) :
    Approx (drive limits tolerance es q fuel index).final.rational (executeEvents es p) ∧
    TraceSound p (drive limits tolerance es q fuel index).observations ∧
    rational (drive limits tolerance es q fuel index).final.error ≤ tolerance := by
  have H := chain_correct (drive_chain limits tolerance es q fuel index) hp
  have HP := drive_partition limits tolerance es q fuel index
  have HC := drive_success limits tolerance es q fuel index hs
  rw [HC.1,List.append_nil] at HP
  rw [HP] at H
  exact ⟨H.1,H.2,HC.2⟩


/-- Import is an exact boundary, including explicit domain and representation admission. -/
def packetWithinRange (q : Numerical.Packet) : Prop :=
  |q.state.position.1| ≤ 256 ∧ |q.state.position.2| ≤ 256 ∧
  |q.state.frame.1| ≤ 256 ∧ |q.state.frame.2| ≤ 256 ∧ |q.error| ≤ 256
instance (q : Numerical.Packet) : Decidable (packetWithinRange q) := by
  unfold packetWithinRange
  infer_instance

def start (limits : Limits) (tolerance : ℚ) (events : List Event)
    (q : Numerical.Packet) (fuel : Nat) : Except Failure Report :=
  match importPacket q with
  | none => .error (if packetWithinRange q then .precision else .range)
  | some input =>
    if input.state.admitted ∧ 0 ≤ input.error.ticks then
      .ok (drive limits tolerance events input fuel 0)
    else .error .domain

theorem start_correct (limits : Limits) (tolerance : ℚ) (events : List Event)
    (q : Numerical.Packet) (fuel : Nat) {r : Report} {p : Pose}
    (hr : start limits tolerance events q fuel = .ok r) (hp : Approx q p) :
    Approx r.final.rational (executeEvents (r.observations.map Observation.event) p) ∧
    TraceSound p r.observations ∧
    r.observations.map Observation.event ++ r.pending = events := by
  unfold start at hr
  cases hi : importPacket q with
  | none => simp [hi] at hr
  | some input =>
    simp only [hi] at hr
    split at hr
    · cases hr
      have hp' : Approx input.rational p := by rwa [importPacket_sound hi]
      have hc := chain_correct (drive_chain limits tolerance events input fuel 0) hp'
      exact ⟨hc.1, hc.2, drive_partition limits tolerance events input fuel 0⟩
    · cases hr


end Orbifold.DiskTransport.Numerical.Bounded.Driver

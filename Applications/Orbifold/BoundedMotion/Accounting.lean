import Applications.Orbifold.BoundedMotion.Driver
import Applications.Orbifold.Driver.Accounting

namespace Orbifold.DiskTransport.Numerical.Bounded
open BoundedArithmetic

/-- Nodes entered by the expression evaluator, including a failing node and excluding
unvisited right subtrees. One boxed arithmetic operation is one model unit. -/
def expressionVisits (env : ι → Box) : Expr ι → Nat
  | .input _ | .literal _ => 1
  | .neg a | .absolute a => 1 + expressionVisits env a
  | .add a b | .sub a b | .mul a b | .divide a b =>
    1 + expressionVisits env a + if (a.run env).isSome then expressionVisits env b else 0

def expressionNodes : Expr ι → Nat
  | .input _ | .literal _ => 1
  | .neg a | .absolute a => 1 + expressionNodes a
  | .add a b | .sub a b | .mul a b | .divide a b => 1 + expressionNodes a + expressionNodes b

theorem expressionVisits_le (env : ι → Box) (e : Expr ι) :
    expressionVisits env e ≤ expressionNodes e := by
  induction e <;> simp only [expressionVisits, expressionNodes]
  all_goals first | omega | split <;> omega

/-- All output and guard trees are charged, even when execution stops early. -/
def stepTrees : List Motion.E :=
  [Motion.positionStep.1, Motion.positionStep.2, Motion.frameStep.1, Motion.frameStep.2,
   Motion.budget, Motion.normSq Motion.control, .absolute (.input .angular),
   .neg (.input .error), Motion.positionMargin, Motion.normSq Motion.frame,
   Motion.normSq Motion.positionStep, Motion.normSq Motion.frameStep]

def stepNodeEnvelope : Nat := (stepTrees.map expressionNodes).sum

theorem step_visits_bound (env : Motion.Variable → Box) :
    (stepTrees.map (expressionVisits env)).sum ≤ stepNodeEnvelope := by
  apply List.sum_le_sum
  intro x hx
  exact expressionVisits_le env x

/-- Distinct model categories: conversions and guards are not boxed arithmetic nodes.
Reservations include complete trees for failed attempts; no bit-operation or time claim. -/
structure WorkEnvelope where
  expressionNodes : Nat
  inputScalarConversions : Nat
  outputScalarConversions : Nat
  integerGuardUnits : Nat
  scheduleAndSearchUnits : Nat
  retainedPacketWrites : Nat
  setupAdmissionChecks : Nat
  relabelScalarNegations : Nat
  deriving Repr

namespace Driver
open Numerical.Driver (Event Label schedule schedule_length eventClock)

def attemptedTicks (logs : List AttemptLog) : Nat := (logs.map AttemptLog.attemptedTicks).sum

theorem searchCandidates_bounds (tolerance : ℚ) (c : Tick) (q : Packet)
    (ns : List Nat) (fuel : Nat) (last : Failure) :
    attemptedTicks (searchCandidates tolerance c q ns fuel last).attempts ≤
      (searchCandidates tolerance c q ns fuel last).charged ∧
    (searchCandidates tolerance c q ns fuel last).charged ≤ fuel := by
  induction ns generalizing fuel last with
  | nil => simp [searchCandidates, attemptedTicks]
  | cons n ns ih =>
    have hm := runMeasured_bound (schedule c n) q
    rw [schedule_length] at hm
    have H := ih (fuel-(n+2)) .accuracy
    have H' (why : Failure) := ih (fuel-(n+2)) why
    simp only [searchCandidates]
    split
    · simp [attemptedTicks]
    · split
      · split
        · simp only [attemptedTicks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
          omega
        · simp only [attemptedTicks, List.map_cons, List.sum_cons] at H ⊢
          omega
      · rename_i why hwhy
        have hf := H' why
        simp only [attemptedTicks, List.map_cons, List.sum_cons] at hf ⊢
        omega

theorem search_work_bound (limits : Limits) (tolerance : ℚ) (fuel : Nat) (c : Tick) (q : Packet) :
    attemptedTicks (searchInterval limits tolerance fuel c q).attempts ≤
      (searchInterval limits tolerance fuel c q).charged ∧
    (searchInterval limits tolerance fuel c q).charged ≤ fuel :=
  searchCandidates_bounds _ _ _ _ _ _

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


def Report.attemptedTicks (r : Report) : Nat :=
  (r.searches.map (fun s => Driver.attemptedTicks s.2)).sum

theorem drive_work (limits : Limits) (tolerance : ℚ) (es : List Event)
    (q : Packet) (fuel index : Nat) :
    (drive limits tolerance es q fuel index).attemptedTicks ≤
      (drive limits tolerance es q fuel index).charged ∧
    (drive limits tolerance es q fuel index).charged ≤ fuel := by
  induction es generalizing q fuel index with
  | nil => simp [drive, Report.attemptedTicks]
  | cons e es ih =>
    cases e with
    | relabel k =>
      simp only [drive]
      split
      · simp [stopped, Report.attemptedTicks]
      · have h := ih (q.rotate k.val) (fuel-1) (index+1)
        simp only [prepend, Report.attemptedTicks] at h ⊢
        omega
    | command c =>
      have ha := search_work_bound limits tolerance fuel c q
      simp only [drive]
      split
      · simp [stopped, Report.attemptedTicks]
      · split
        · simpa [stopped, Report.attemptedTicks] using ha
        · rename_i s hs
          have hb := ih s.execution.final (fuel-(searchInterval limits tolerance fuel c q).charged) (index+1)
          simp only [Report.attemptedTicks, List.map_cons, List.sum_cons] at hb ⊢
          omega


def Observation.packets : Observation → List Packet
  | .relabel _ q => [q]
  | .command _ _ q r => q :: r.final :: r.samples

def Report.packets (r : Report) : List Packet :=
  r.final :: r.observations.flatMap Observation.packets

/-- Logical scalar slots, counting duplicate occurrences without an assumed sharing allocator. -/
def Report.scalarSlots (r : Report) : Nat := 5 * r.packets.length

def Report.envelope (r : Report) : WorkEnvelope :=
  ⟨stepNodeEnvelope * r.attemptedTicks,
    5 + 4 * r.attemptedTicks,
    r.scalarSlots + (r.searches.map (fun s => s.2.length)).sum,
    (7 + 8 + 12 + 4 + 4 + 7) * r.attemptedTicks,
    r.charged + r.observations.length + r.pending.length,
    r.packets.length, 1,
    (r.observations.map (fun o => match o with
      | .relabel k _ => 2 * k.val | .command _ _ _ _ => 0)).sum⟩

end Driver

/-- An injective finite code for every stored coordinate packet; this does not specify Int layout. -/
def Packet.code (q : Packet) : Fin 131073 × Fin 131073 × Fin 131073 × Fin 131073 × Fin 131073 :=
  (q.state.px.code, q.state.py.code, q.state.fx.code, q.state.fy.code, q.error.code)

theorem Packet.code_injective : Function.Injective Packet.code := by
  rintro ⟨⟨a,b,c,d⟩,e⟩ ⟨⟨a',b',c',d'⟩,e'⟩ h
  simp only [Packet.code, Prod.mk.injEq] at h
  obtain ⟨ha,hb,hc,hd,he⟩ := h
  cases BoundedArithmetic.code_injective ha
  cases BoundedArithmetic.code_injective hb
  cases BoundedArithmetic.code_injective hc
  cases BoundedArithmetic.code_injective hd
  cases BoundedArithmetic.code_injective he
  rfl

example : 131073 ≤ 2^18 := by decide

/-- Rational boundary/control storage is reported separately from bounded scalar codes. -/
def rationalBits (q : ℚ) : Nat := 1 + (q.num.natAbs.log2+1) + (q.den.log2+1)
def packetRationals (q : Numerical.Packet) : List ℚ :=
  [q.state.position.1, q.state.position.2, q.state.frame.1, q.state.frame.2, q.error]

def rationalObservationPackets : Numerical.Driver.Observation → List Numerical.Packet
  | .relabel _ q => [q]
  | .command _ _ q r => q :: r.final :: r.samples

def rationalScalarStorage (r : Numerical.Driver.Report) : Nat :=
  ((r.final :: r.observations.flatMap rationalObservationPackets).flatMap packetRationals).foldl
    (fun n x => n + rationalBits x) 0


def eventRationals : Numerical.Driver.Event → List ℚ
  | .relabel _ => []
  | .command c => [c.control.velocity.1, c.control.velocity.2, c.control.angular, c.duration]

def Driver.Report.metadataRationals (r : Driver.Report) : List ℚ :=
  r.elapsed ::
    (r.observations.flatMap fun o => eventRationals o.event ++
      match o with | .relabel _ _ => [] | .command _ _ _ result => [result.elapsed]) ++
    r.pending.flatMap eventRationals ++
    r.searches.flatMap (fun s => s.2.flatMap (fun a => a.finalError.toList))

def Driver.Report.metadataNaturals (r : Driver.Report) : List Nat :=
  r.charged :: (r.observations.flatMap fun o =>
    match o with | .relabel k _ => [k.val] | .command _ n _ _ => [n]) ++
    (r.pending.flatMap fun e => match e with | .relabel k => [k.val] | .command _ => []) ++
    r.searches.flatMap (fun s => s.1 :: s.2.flatMap (fun a => [a.subdivisions, a.attemptedTicks]))

def Driver.Report.metadataBits (r : Driver.Report) : Nat :=
  (r.metadataRationals.map rationalBits).sum + (r.metadataNaturals.map (fun n => n.log2+1)).sum

def Driver.Report.listCells (r : Driver.Report) : Nat :=
  r.observations.length + r.pending.length + r.searches.length +
    (r.searches.map (fun s => s.2.length)).sum +
    (r.observations.map fun o => match o with | .relabel _ _ => 0 | .command _ _ _ result => result.samples.length).sum

/-- The error accumulator is exact integer arithmetic and is range-checked before storage. -/
theorem Outputs.accumulator_range (o : Outputs) :
    0 ≤ o.roundoff ∧ o.roundoff ≤ 524288 ∧ -65536 ≤ o.errorTicks ∧ o.errorTicks ≤ 589824 := by
  have h1 := radius_range o.px
  have h2 := radius_range o.py
  have h3 := radius_range o.fx
  have h4 := radius_range o.fy
  have hlo := o.budget.hi.lower
  have hhi := o.budget.hi.upper
  simp only [Outputs.errorTicks, Outputs.roundoff]
  omega



/-- A rational arithmetic node includes its exact normalization as one model operation.
These units are not the bounded executor's integer operations or bit costs. -/
structure RationalWorkEnvelope where
  formulaNodes : Nat
  packetScalarBitScans : Nat
  setupRationalCopies : Nat
  outputRationalObservations : Nat
  scheduleAndSearchUnits : Nat
  retainedPacketWrites : Nat
  setupAdmissionChecks : Nat
  relabelScalarNegations : Nat
  deriving Repr

def rationalWorkEnvelope (r : Numerical.Driver.Report) : RationalWorkEnvelope :=
  let packets := r.final :: r.observations.flatMap rationalObservationPackets
  ⟨stepNodeEnvelope * r.counts.1,
   10 * r.counts.1, 5,
   5 * packets.length + (r.searches.map (fun s => s.2.length)).sum,
   r.charged + r.observations.length + r.pending.length, packets.length, 0,
   (r.observations.map (fun o => match o with
     | .relabel k _ => 2 * k.val | .command _ _ _ _ => 0)).sum⟩

def rationalMetadataBits (r : Numerical.Driver.Report) : Nat :=
  let rationals := r.elapsed ::
    (r.observations.flatMap fun o => eventRationals o.event ++
      match o with | .relabel _ _ => [] | .command _ _ _ result => [result.elapsed]) ++
    r.pending.flatMap eventRationals ++
    r.searches.flatMap (fun s => s.2.flatMap (fun a => a.finalError.toList))
  let naturals := r.charged :: [r.counts.1, r.counts.2.1, r.counts.2.2] ++
    (r.observations.flatMap fun o => match o with | .relabel k _ => [k.val] | .command _ n _ _ => [n]) ++
    (r.pending.flatMap fun e => match e with | .relabel k => [k.val] | .command _ => []) ++
    r.searches.flatMap (fun s => s.1 :: s.2.flatMap
      (fun a => [a.subdivisions, a.counts.1, a.counts.2.1, a.counts.2.2]))
  (rationals.map rationalBits).sum + (naturals.map (fun n => n.log2+1)).sum

def rationalListCells (r : Numerical.Driver.Report) : Nat :=
  r.observations.length + r.pending.length + r.searches.length +
    (r.searches.map (fun s => s.2.length)).sum +
    (r.observations.map fun o => match o with | .relabel _ _ => 0 | .command _ _ _ result => result.samples.length).sum


end Orbifold.DiskTransport.Numerical.Bounded

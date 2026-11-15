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


/-- Source-level compound tariffs. A candidate cell includes range/map allocation,
`2^k-1`, and storing that candidate. A schedule slot includes constructing its
subtick (including exact duration division), allocation, and traversal. A step
slot includes input conversions, all AST evaluation and guards, packet-bit tests
where applicable, result construction, and sample/error logging. These tariffs
are whole source operations, not uniform integer or machine operations. -/
structure RequestEnvelope where
  initialScalarSlots : Nat
  initialPredicates : Nat
  eventSlots : Nat
  candidateCells : Nat
  candidateChecks : Nat
  scheduleSlots : Nat
  stepSlots : Nat
  relabelQuarterTurns : Nat
  outputScalarSlots : Nat
  outputListCells : Nat
  deriving Repr, DecidableEq

/-- Reserve all request events and configured candidates, including unreached
ones; fuel bounds schedules actually allocated after the reservation check.
Output traversal charges the complete retained result when one exists. -/
def requestEnvelope (rounds eventCount fuel scalarSlots listCells : Nat) : RequestEnvelope :=
  ⟨5, 2, eventCount + 1, rounds * eventCount, (rounds + 1) * eventCount,
    fuel, fuel, 3 * eventCount, scalarSlots, listCells⟩

namespace Driver

theorem drive_searches_le (limits : Limits) (tolerance : ℚ) (es : List Numerical.Driver.Event)
    (q : Packet) (fuel index : Nat) :
    (drive limits tolerance es q fuel index).searches.length ≤ es.length := by
  induction es generalizing q fuel index with
  | nil => simp [drive]
  | cons e es ih =>
    cases e with
    | relabel k =>
      simp only [drive]
      split
      · simp [stopped]
      · have h := ih (q.rotate k.val) (fuel-1) (index+1)
        simpa only [prepend, List.length_cons] using Nat.le_succ_of_le h
    | command c =>
      simp only [drive]
      split
      · simp [stopped]
      · split
        · simp
        · rename_i s hs
          simpa only [List.length_cons] using Nat.succ_le_succ
            (ih s.execution.final (fuel-(searchInterval limits tolerance fuel c q).charged) (index+1))

/-- The cost-bearing result survives initial conversion or admission failure. -/
def startAccounted (limits : Limits) (tolerance : ℚ) (events : List Numerical.Driver.Event)
    (q : Numerical.Packet) (fuel : Nat) : Except Failure Report × RequestEnvelope :=
  let result := start limits tolerance events q fuel
  let slots := match result with | .error _ => 0 | .ok r => r.scalarSlots
  let cells := match result with | .error _ => 0 | .ok r => r.listCells
  (result, requestEnvelope limits.rounds events.length fuel slots cells)

theorem startAccounted_erases (limits : Limits) (tolerance : ℚ)
    (events : List Numerical.Driver.Event) (q : Numerical.Packet) (fuel : Nat) :
    (startAccounted limits tolerance events q fuel).1 = start limits tolerance events q fuel := rfl

/-- Coverage of all actual search calls, allocated schedules, attempted ticks,
and complete retained-output traversal. A refused candidate allocates no schedule;
its setup and decision remain charged by candidateCells/candidateChecks. -/
theorem startAccounted_coverage (limits : Limits) (tolerance : ℚ)
    (events : List Numerical.Driver.Event) (q : Numerical.Packet) (fuel : Nat)
    {r : Report} (hr : (startAccounted limits tolerance events q fuel).1 = .ok r) :
    limits.rounds * r.searches.length ≤ (startAccounted limits tolerance events q fuel).2.candidateCells ∧
    r.attemptedTicks ≤ (startAccounted limits tolerance events q fuel).2.stepSlots ∧
    r.charged ≤ (startAccounted limits tolerance events q fuel).2.scheduleSlots ∧
    (startAccounted limits tolerance events q fuel).2.outputScalarSlots = r.scalarSlots ∧
    (startAccounted limits tolerance events q fuel).2.outputListCells = r.listCells := by
  have hr' : start limits tolerance events q fuel = .ok r := hr
  have bounds : r.searches.length ≤ events.length ∧ r.attemptedTicks ≤ fuel ∧ r.charged ≤ fuel := by
    unfold start at hr'
    cases hi : importPacket q with
    | none => simp [hi] at hr'
    | some input =>
      simp only [hi] at hr'
      split at hr'
      · cases hr'
        exact ⟨drive_searches_le _ _ _ _ _ _, (drive_work _ _ _ _ _ _).1.trans
          (drive_work _ _ _ _ _ _).2, (drive_work _ _ _ _ _ _).2⟩
      · cases hr'
  simp only [startAccounted, hr', requestEnvelope]
  exact ⟨Nat.mul_le_mul_left _ bounds.1, bounds.2.1, bounds.2.2, trivial, trivial⟩

/-- Initial rejection still reserves every initial scalar conversion and both
compound admission/classification predicates, even when conversion short circuits. -/
theorem startAccounted_initial (limits : Limits) (tolerance : ℚ)
    (events : List Numerical.Driver.Event) (q : Numerical.Packet) (fuel : Nat) :
    (startAccounted limits tolerance events q fuel).2.initialScalarSlots = 5 ∧
    (startAccounted limits tolerance events q fuel).2.initialPredicates = 2 := ⟨rfl, rfl⟩

end Driver

theorem rational_drive_searches_le (limits : Numerical.Driver.Limits) (tolerance : ℚ)
    (es : List Numerical.Driver.Event) (q : Numerical.Packet) (fuel index : Nat) :
    (Numerical.Driver.drive limits tolerance es q fuel index).searches.length ≤ es.length := by
  induction es generalizing q fuel index with
  | nil => simp [Numerical.Driver.drive]
  | cons e es ih =>
    cases e with
    | relabel k =>
      simp only [Numerical.Driver.drive]
      split
      · simp [Numerical.Driver.stopped]
      · have h := ih (q.rotate k.val) (fuel-1) (index+1)
        simpa only [Numerical.Driver.prepend, List.length_cons] using Nat.le_succ_of_le h
    | command c =>
      simp only [Numerical.Driver.drive]
      split
      · simp [Numerical.Driver.stopped]
      · split
        · simp
        · rename_i s hs
          simpa only [List.length_cons] using Nat.succ_le_succ
            (ih s.execution.final (fuel-(Numerical.Driver.searchInterval limits tolerance fuel c q).charged) (index+1))

def rationalAccounted (limits : Numerical.Driver.Limits) (tolerance : ℚ)
    (events : List Numerical.Driver.Event) (q : Numerical.Packet) (fuel : Nat) :
    Numerical.Driver.Report × RequestEnvelope :=
  let r := Numerical.Driver.drive limits tolerance events q fuel 0
  (r, requestEnvelope limits.rounds events.length fuel
    (5 * (r.final :: r.observations.flatMap rationalObservationPackets).length) (rationalListCells r))

theorem rationalAccounted_erases (limits : Numerical.Driver.Limits) (tolerance : ℚ)
    (events : List Numerical.Driver.Event) (q : Numerical.Packet) (fuel : Nat) :
    (rationalAccounted limits tolerance events q fuel).1 =
      Numerical.Driver.drive limits tolerance events q fuel 0 := rfl

theorem rationalAccounted_coverage (limits : Numerical.Driver.Limits) (tolerance : ℚ)
    (events : List Numerical.Driver.Event) (q : Numerical.Packet) (fuel : Nat) :
    let a := rationalAccounted limits tolerance events q fuel
    limits.rounds * a.1.searches.length ≤ a.2.candidateCells ∧
    a.1.counts.1 ≤ a.2.stepSlots ∧ a.1.charged ≤ a.2.scheduleSlots := by
  exact ⟨Nat.mul_le_mul_left _ (rational_drive_searches_le _ _ _ _ _ _),
    (Numerical.Driver.drive_work _ _ _ _ _ _).1.trans (Numerical.Driver.drive_work _ _ _ _ _ _).2,
    (Numerical.Driver.drive_work _ _ _ _ _ _).2⟩

/-- Actual eager candidate construction has exactly this many cells. Exponentiation
and subtraction are included in each compound candidate-cell tariff. -/
theorem candidate_cells (rounds : Nat) :
    ((List.range rounds).map (fun k => 2^k-1)).length = rounds := by simp

/-- Search visits at most the prepared candidate list. The extra one in the
request tariff covers either list exhaustion or refusal before execution. -/
theorem Driver.search_attempts_le (tolerance : ℚ) (c : Tick) (q : Packet)
    (ns : List Nat) (fuel : Nat) (last : Failure) :
    (Driver.searchCandidates tolerance c q ns fuel last).attempts.length ≤ ns.length := by
  induction ns generalizing fuel last with
  | nil => simp [Driver.searchCandidates]
  | cons n ns ih =>
    have h := ih (fuel-(n+2)) .accuracy
    have h' why := ih (fuel-(n+2)) why
    simp only [Driver.searchCandidates]
    split
    · simp
    · split
      · split
        · simp
        · simpa only [List.length_cons] using Nat.succ_le_succ h
      · simpa only [List.length_cons] using Nat.succ_le_succ (h' _)

theorem rational_search_attempts_le (cap : Nat) (tolerance : ℚ) (c : Tick)
    (q : Numerical.Packet) (ns : List Nat) (fuel : Nat) (last : Numerical.Driver.Failure) :
    (Numerical.Driver.searchCandidates cap tolerance c q ns fuel last).attempts.length ≤ ns.length := by
  induction ns generalizing fuel last with
  | nil => simp [Numerical.Driver.searchCandidates]
  | cons n ns ih =>
    have h := ih (fuel-(n+2)) .accuracy
    have h' why := ih (fuel-(n+2)) why
    simp only [Numerical.Driver.searchCandidates]
    split
    · simp
    · split
      · split
        · simp
        · simpa only [List.length_cons] using Nat.succ_le_succ h
      · split
        · simp
        · simpa only [List.length_cons] using Nat.succ_le_succ (h' _)

/-- Both drivers commit a prefix, so event dispatch and signed-permutation work
are bounded by the original request even when a failure leaves a suffix. -/
theorem Driver.observations_le (limits : Driver.Limits) (tolerance : ℚ)
    (es : List Numerical.Driver.Event) (q : Packet) (fuel index : Nat) :
    (Driver.drive limits tolerance es q fuel index).observations.length ≤ es.length := by
  have h := congrArg List.length (Driver.drive_partition limits tolerance es q fuel index)
  simp only [List.length_append, List.length_map] at h
  omega

theorem rational_observations_le (limits : Numerical.Driver.Limits) (tolerance : ℚ)
    (es : List Numerical.Driver.Event) (q : Numerical.Packet) (fuel index : Nat) :
    (Numerical.Driver.drive limits tolerance es q fuel index).observations.length ≤ es.length := by
  have h := congrArg List.length (Numerical.Driver.drive_partition limits tolerance es q fuel index)
  simp only [List.length_append, List.length_map] at h
  omega

def Driver.plannedTicks (logs : List Driver.AttemptLog) : Nat :=
  (logs.map Driver.AttemptLog.subdivisions).sum

theorem Driver.search_planned_le (tolerance : ℚ) (c : Tick) (q : Packet)
    (ns : List Nat) (fuel : Nat) (last : Failure) :
    Driver.plannedTicks (Driver.searchCandidates tolerance c q ns fuel last).attempts ≤
      (Driver.searchCandidates tolerance c q ns fuel last).charged := by
  induction ns generalizing fuel last with
  | nil => simp [Driver.searchCandidates, Driver.plannedTicks]
  | cons n ns ih =>
    have h := ih (fuel-(n+2)) .accuracy
    have h' why := ih (fuel-(n+2)) why
    simp only [Driver.searchCandidates]
    split
    · simp [Driver.plannedTicks]
    · split
      · split
        · simp [Driver.plannedTicks]
        · simp only [Driver.plannedTicks, List.map_cons, List.sum_cons] at h ⊢; omega
      · rename_i why hw
        have H := h' why
        simp only [Driver.plannedTicks, List.map_cons, List.sum_cons] at H ⊢; omega

def rationalPlannedTicks (logs : List Numerical.Driver.AttemptLog) : Nat :=
  (logs.map Numerical.Driver.AttemptLog.subdivisions).sum

theorem rational_search_planned_le (cap : Nat) (tolerance : ℚ) (c : Tick)
    (q : Numerical.Packet) (ns : List Nat) (fuel : Nat) (last : Numerical.Driver.Failure) :
    rationalPlannedTicks (Numerical.Driver.searchCandidates cap tolerance c q ns fuel last).attempts ≤
      (Numerical.Driver.searchCandidates cap tolerance c q ns fuel last).charged := by
  induction ns generalizing fuel last with
  | nil => simp [Numerical.Driver.searchCandidates, rationalPlannedTicks]
  | cons n ns ih =>
    have h := ih (fuel-(n+2)) .accuracy
    have h' why := ih (fuel-(n+2)) why
    simp only [Numerical.Driver.searchCandidates]
    split
    · simp [rationalPlannedTicks]
    · split
      · split
        · simp [rationalPlannedTicks]
        · simp only [rationalPlannedTicks, List.map_cons, List.sum_cons] at h ⊢; omega
      · split
        · simp [rationalPlannedTicks]
        · have H := h' (Numerical.Driver.guarded cap (Numerical.Driver.schedule c n) q).failure
          simp only [rationalPlannedTicks, List.map_cons, List.sum_cons] at H ⊢; omega

/-- Each label is a C4 element; the tariff reserves three quarter turns per event. -/
def relabelTurns (es : List Numerical.Driver.Event) : Nat :=
  (es.map (fun e => match e with | .relabel k => k.val | .command _ => 0)).sum

theorem relabelTurns_le (es : List Numerical.Driver.Event) : relabelTurns es ≤ 3 * es.length := by
  induction es with
  | nil => simp [relabelTurns]
  | cons e es ih =>
    cases e with
    | command c => simp only [relabelTurns, List.map_cons, List.sum_cons, List.length_cons] at *; omega
    | relabel k =>
      have h := k.isLt
      simp only [relabelTurns, List.map_cons, List.sum_cons, List.length_cons] at *
      omega

theorem Driver.drive_planned_le (limits : Driver.Limits) (tolerance : ℚ)
    (es : List Numerical.Driver.Event) (q : Packet) (fuel index : Nat) :
    (((Driver.drive limits tolerance es q fuel index).searches.map
      (fun s => Driver.plannedTicks s.2)).sum) ≤
      (Driver.drive limits tolerance es q fuel index).charged := by
  induction es generalizing q fuel index with
  | nil => simp [Driver.drive]
  | cons e es ih =>
    cases e with
    | relabel k =>
      simp only [Driver.drive]
      split
      · simp [Driver.stopped]
      · have h := ih (q.rotate k.val) (fuel-1) (index+1)
        simp only [Driver.prepend] at h ⊢
        omega
    | command c =>
      have h := Driver.search_planned_le tolerance c q
        ((List.range limits.rounds).map (fun k => 2^k-1)) fuel .accuracy
      change Driver.plannedTicks (Driver.searchInterval limits tolerance fuel c q).attempts ≤
        (Driver.searchInterval limits tolerance fuel c q).charged at h
      simp only [Driver.drive]
      split
      · simp [Driver.stopped]
      · split
        · simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] using h
        · rename_i sel hs
          have h' := ih sel.execution.final (fuel-(Driver.searchInterval limits tolerance fuel c q).charged) (index+1)
          simp only [List.map_cons, List.sum_cons] at h' ⊢
          omega

theorem rational_drive_planned_le (limits : Numerical.Driver.Limits) (tolerance : ℚ)
    (es : List Numerical.Driver.Event) (q : Numerical.Packet) (fuel index : Nat) :
    (((Numerical.Driver.drive limits tolerance es q fuel index).searches.map
      (fun s => rationalPlannedTicks s.2)).sum) ≤
      (Numerical.Driver.drive limits tolerance es q fuel index).charged := by
  induction es generalizing q fuel index with
  | nil => simp [Numerical.Driver.drive]
  | cons e es ih =>
    cases e with
    | relabel k =>
      simp only [Numerical.Driver.drive]
      split
      · simp [Numerical.Driver.stopped]
      · have h := ih (q.rotate k.val) (fuel-1) (index+1)
        simp only [Numerical.Driver.prepend] at h ⊢
        omega
    | command c =>
      have h := rational_search_planned_le limits.packetBitLimit tolerance c q
        ((List.range limits.rounds).map (fun k => 2^k-1)) fuel .accuracy
      change rationalPlannedTicks (Numerical.Driver.searchInterval limits tolerance fuel c q).attempts ≤
        (Numerical.Driver.searchInterval limits tolerance fuel c q).charged at h
      simp only [Numerical.Driver.drive]
      split
      · simp [Numerical.Driver.stopped]
      · split
        · simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] using h
        · rename_i sel hs
          have h' := ih sel.execution.final (fuel-(Numerical.Driver.searchInterval limits tolerance fuel c q).charged) (index+1)
          simp only [List.map_cons, List.sum_cons] at h' ⊢
          omega

end Orbifold.DiskTransport.Numerical.Bounded

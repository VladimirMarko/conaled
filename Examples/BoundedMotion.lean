import Applications.Orbifold.BoundedMotion.Accounting

namespace BoundedMotionExamples
open Orbifold Orbifold.DiskTransport
open Orbifold.DiskTransport.Numerical
open BoundedArithmetic

def fixture : Bounded.Packet :=
  ⟨⟨Motion.fixtureScalar .px, Motion.fixtureScalar .py,
    Motion.fixtureScalar .fx, Motion.fixtureScalar .fy⟩, Motion.fixtureScalar .error⟩
def move : Tick := ⟨Motion.fixtureControl, 1/16, by norm_num⟩
def turn : Tick := ⟨.turn (1/2), 1/64, by norm_num⟩
def word : List Driver.Event := [.command move, .relabel ⟨1, by decide⟩, .command turn]
def moved : Bounded.Packet :=
  ⟨⟨Motion.fixturePX.value, Motion.fixturePY.value, Motion.fixtureFX.value, Motion.fixtureFY.value⟩,
    ⟨43, by norm_num, by norm_num⟩⟩

def moveInput : Bounded.Input :=
  ⟨Motion.fixtureScalar .vx, Motion.fixtureScalar .vy,
    Motion.fixtureScalar .angular, Motion.fixtureScalar .duration⟩
theorem import_move : Bounded.importInput move = some moveInput := by
  norm_num [Bounded.importInput, Bounded.encode, move, Motion.fixtureControl,
    Numerical.Input.velocity, Numerical.Input.angular, moveInput, Motion.fixtureScalar]

/-- Independent #538 fixture: upper budget 41 plus two coordinate-radius ticks. -/
theorem fixture_step : Bounded.checkedStep move fixture = .ok moved := by
  rw [Bounded.checkedStep, import_move]
  decide
example : Bounded.rational moved.error = 43/256 := by norm_num [moved, Bounded.rational]
example : (Bounded.Driver.searchInterval ⟨1⟩ (43/256) 128 move fixture).accepted.isSome = true := by
  have sub0 : Driver.subTick move 0 = move := by simp [Driver.subTick]
  have hr : Bounded.runMeasured (Driver.schedule move 0) fixture =
      (.ok ⟨moved, [moved], 1/16⟩, 1) := by
    simp only [Driver.schedule, Nat.zero_add, List.replicate_succ, List.replicate_zero, sub0,
      Bounded.runMeasured, fixture_step]
    simp [move]
  change (Bounded.Driver.searchCandidates _ move fixture [0] 128 .accuracy).accepted.isSome = _
  rw [Bounded.Driver.search_singleton_isSome _ _ _ _ _ (by decide) _ (congrArg Prod.fst hr)]
  norm_num [Bounded.rational, moved]
example : (Bounded.Driver.searchInterval ⟨1⟩ (42/256) 128 move fixture).accepted.isSome = false := by
  have sub0 : Driver.subTick move 0 = move := by simp [Driver.subTick]
  have hr : Bounded.runMeasured (Driver.schedule move 0) fixture =
      (.ok ⟨moved, [moved], 1/16⟩, 1) := by
    simp only [Driver.schedule, Nat.zero_add, List.replicate_succ, List.replicate_zero, sub0,
      Bounded.runMeasured, fixture_step]
    simp [move]
  change (Bounded.Driver.searchCandidates _ move fixture [0] 128 .accuracy).accepted.isSome = _
  rw [Bounded.Driver.search_singleton_isSome _ _ _ _ _ (by decide) _ (congrArg Prod.fst hr)]
  norm_num [Bounded.rational, moved]


def fixtureOutputs : Bounded.Outputs :=
  ⟨Motion.fixturePX, Motion.fixturePY, Motion.fixtureFX, Motion.fixtureFY, Motion.fixtureBudget⟩
theorem fixture_evaluate : Bounded.evaluate (Bounded.inputEnv moveInput fixture) = some fixtureOutputs := by decide

/-- Mesh roundoff is two ticks; the larger continuous bound includes truncation and input error. -/
theorem fixture_mesh :
    ‖moved.state.rational.decode - (Numerical.advance move fixture.rational).state.decode‖ ≤ (2/256 : ℝ) := by
  have hc : Admissible move fixture.rational :=
    Motion.admitted_sound move fixture.rational (Bounded.inputEnv_sound import_move fixture) (by decide)
  have hr : Numerical.checkedStep move fixture.rational = some (Numerical.advance move fixture.rational) := by
    simp only [Numerical.checkedStep, ite_eq_left hc]
  have h := Bounded.checkedStep_mesh fixture_step hr
  have he : Bounded.stepRoundoff move fixture = 2/256 := by
    simp only [Bounded.stepRoundoff, import_move, fixture_evaluate]
    norm_num [fixtureOutputs, Bounded.Outputs.roundoff, Box.radius,
      Motion.fixturePX, Motion.fixturePY, Motion.fixtureFX, Motion.fixtureFY]
  simpa only [Bounded.Packet.rational, sub_self, norm_zero, mul_zero, zero_add, he,
    Rat.cast_div, Rat.cast_ofNat] using h

/-- Signed permutation is exact, but floor-selected multiplication need not commute with it. -/
example : Bounded.checkedStep move (fixture.rotate 1) ≠ .ok (moved.rotate 1) := by
  rw [Bounded.checkedStep, import_move]
  decide


/-- An exact valid pose supplies a nonvacuous continuous-trajectory specialization. -/
noncomputable def originPose : Pose := ⟨0, 1, by norm_num [Complex.normSq_apply], by norm_num⟩
def zero : Scalar := ⟨0, by norm_num, by norm_num⟩
def half : Scalar := ⟨128, by norm_num, by norm_num⟩
def origin : Bounded.Packet := ⟨⟨zero, zero, half, zero⟩, zero⟩
def originMoved : Bounded.Packet :=
  ⟨⟨⟨-4, by norm_num, by norm_num⟩, ⟨2, by norm_num, by norm_num⟩, half, zero⟩,
    ⟨39, by norm_num, by norm_num⟩⟩

theorem origin_exact : Approx origin.rational originPose := by
  have h : origin.state.rational.decode = coordinates originPose := by
    apply Prod.ext <;> apply Complex.ext <;>
      norm_num [origin, originPose, Bounded.State.rational, Bounded.rational, zero, half,
        State.decode, QComplex.decode, coordinates, Pose.frame, Complex.normSq_apply,
        Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  unfold Approx Bounded.Packet.rational
  rw [h, sub_self, norm_zero]
  norm_num [origin, zero, Bounded.rational]

theorem origin_motion : Approx originMoved.rational (move.decode.finish originPose) ∧
    Domain originMoved.state.rational.decode :=
  Bounded.checkedStep_correct (by rw [Bounded.checkedStep, import_move]; decide : Bounded.checkedStep move origin = .ok originMoved) origin_exact

example : Bounded.checkedStep ⟨.hold, 1/512, by norm_num⟩ origin = .error .precision := by
  norm_num [Bounded.checkedStep, Bounded.importInput, Bounded.encode, Bounded.inputWithinRange, Input.velocity, Input.angular]
example : Bounded.checkedStep ⟨.turn 257, 0, by norm_num⟩ origin = .error .range := by
  norm_num [Bounded.checkedStep, Bounded.importInput, Bounded.encode, Bounded.inputWithinRange, Input.velocity, Input.angular]
example : Bounded.importPacket ⟨⟨(1/512,0),(1/2,0)⟩,0⟩ = none := by norm_num [Bounded.importPacket, Bounded.encode]
example : Bounded.importPacket ⟨⟨(257,0),(1/2,0)⟩,0⟩ = none := by norm_num [Bounded.importPacket, Bounded.encode]

def nearBoundary : Bounded.Packet := ⟨⟨⟨127, by norm_num, by norm_num⟩, zero, half, zero⟩, zero⟩
example : Bounded.checkedStep move nearBoundary = .error .domain := by
  rw [Bounded.checkedStep, import_move]
  decide

def boundedReport (tolerance : ℚ) (k : Nat := 0) : Bounded.Driver.Report :=
  match Bounded.Driver.start ⟨4⟩ tolerance word (fixture.rational.rotate k) 128 with
  | .ok r => r
  | .error err => Bounded.Driver.stopped (fixture.rotate k) word err

def rationalReport (tolerance : ℚ) (k : Nat := 0) : Driver.Report :=
  Driver.drive ⟨4, 4096⟩ tolerance word (fixture.rational.rotate k) 128 0


def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

def smoke : IO Unit := do
  let low := boundedReport (1/4)
  check "failed turn preserves two-event prefix" (low.failure == some .precision &&
    low.observations.length == 2 && low.pending.length == 1 && low.elapsed == 1/16 &&
    low.final == moved.rotate 1)
  let high := boundedReport (1/2)
  check "larger tolerance completes timed word" (high.failure == none && high.pending.isEmpty &&
    high.observations.length == 3 && high.elapsed == 5/64)
  let empty := Bounded.Driver.drive ⟨4⟩ (1/4) [] fixture 128 0
  check "empty prefix" (empty.failure == none && empty.elapsed == 0 && empty.final == fixture)
  let unsupported : Tick := ⟨.turn 2, 1/64, by norm_num⟩
  let rejected := Bounded.Driver.drive ⟨4⟩ (1/2) [.command move, .command unsupported] fixture 128 0
  check "unsupported command keeps incoming prefix" (rejected.failure == some .unsupported &&
    rejected.final == moved && rejected.observations.length == 1 && rejected.pending.length == 1)
  let tooFine : Tick := ⟨.hold, 1/512, by norm_num⟩
  let precision := Bounded.Driver.drive ⟨4⟩ (1/2) [.command move, .command tooFine] fixture 128 0
  check "precision failure keeps incoming prefix" (precision.failure == some .precision &&
    precision.final == moved && precision.elapsed == 1/16 && precision.pending.length == 1)
  let work := Bounded.Driver.drive ⟨4⟩ (1/2) [.command move] fixture 1 0
  check "work rejected before execution" (work.failure == some .work && work.final == fixture &&
    work.observations.isEmpty)
  for k in List.range 4 do
    let changed := boundedReport (1/2) k
    check s!"representative {k} completes at loose tolerance" (changed.failure == none &&
      changed.elapsed == 5/64 && changed.observations.length == 3)
    let rational := rationalReport (1/2) k
    check s!"rational representative {k}" (rational.failure == none && rational.elapsed == 5/64)
  let one := Bounded.Driver.startAccounted ⟨1⟩ (1/2) [.command move] fixture.rational 128
  let many := Bounded.Driver.startAccounted ⟨4⟩ (1/2) [.command move] fixture.rational 128
  check "early success still charges all configured candidates" (one.2.candidateCells == 1 &&
    many.2.candidateCells == 4 && match one.1, many.1 with
      | .ok a, .ok b => a.final == b.final && a.attemptedTicks == 1 && b.attemptedTicks == 1
      | _, _ => false)
  let refused := Bounded.Driver.startAccounted ⟨4⟩ (1/2) [.command move] fixture.rational 1
  check "work refusal retains eager setup" (refused.2.candidateCells == 4 &&
    match refused.1 with | .ok r => r.failure == some .work && r.attemptedTicks == 0 | _ => false)
  let nongrid := Bounded.Driver.startAccounted ⟨4⟩ (1/2) word ⟨⟨(1/512,0),(1/2,0)⟩,0⟩ 128
  check "initial rejection remains cost bearing" (nongrid.2.initialScalarSlots == 5 &&
    nongrid.2.initialPredicates == 2 && nongrid.2.outputScalarSlots == 0 &&
    match nongrid.1 with | .error .precision => true | _ => false)
  IO.println "bounded-motion smoke cases passed"

#eval smoke

/-- Runtime observations use the pinned Lean evaluator; they are separate from work charges. -/
def measurements : IO Unit := do
  for tolerance in ([1/4, 1/2] : List ℚ) do
    for k in List.range 4 do
      let before ← IO.monoNanosNow
      let boundedRun := Bounded.Driver.startAccounted ⟨4⟩ tolerance word (fixture.rational.rotate k) 128
      let bounded := match boundedRun.1 with
        | .ok r => r
        | .error err => Bounded.Driver.stopped (fixture.rotate k) word err
      let boundedSummary := (bounded.failure, bounded.elapsed, Bounded.rational bounded.final.error,
        bounded.attemptedTicks, bounded.charged, bounded.scalarSlots, bounded.metadataBits, bounded.listCells, bounded.envelope,
        boundedRun.2)
      IO.println s!"bounded tol={tolerance} representative={k}: {repr boundedSummary}"
      let after ← IO.monoNanosNow
      IO.println s!"bounded elapsed_ns_including_render={after-before}"
      let beforeR ← IO.monoNanosNow
      let rationalRun := Bounded.rationalAccounted ⟨4,4096⟩ tolerance word (fixture.rational.rotate k) 128
      let rational := rationalRun.1
      let rationalSummary := (rational.failure, rational.elapsed, rational.final.error,
        rational.counts.1, rational.charged, Bounded.rationalScalarStorage rational,
        Bounded.rationalMetadataBits rational, Bounded.rationalListCells rational,
        Bounded.rationalWorkEnvelope rational,
        rationalRun.2)
      IO.println s!"rational tol={tolerance} representative={k}: {repr rationalSummary}"
      let afterR ← IO.monoNanosNow
      IO.println s!"rational elapsed_ns_including_render={afterR-beforeR}"

#eval measurements

end BoundedMotionExamples

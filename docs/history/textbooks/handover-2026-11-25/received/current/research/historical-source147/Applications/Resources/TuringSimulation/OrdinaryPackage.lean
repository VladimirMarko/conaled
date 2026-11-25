import Applications.Resources.TuringSimulation.MarkedInput
import Applications.Resources.TuringSimulation.FiniteStackToTape
import Applications.Resources.TuringSimulation.SingletonOutput

set_option autoImplicit false
set_option warningAsError true

/-!
# Ordinary input and singleton output for finite stack packages

The wrapper fixes a native machine before the raw input is supplied. It uses
the package's work alphabet, its exact supported starting control, and an
injective nonblank letter map. Finiteness of the work alphabet requires finite
alphabets at every source stack index.

`runInTime` consumes an actual bounded encoded native run and a complete
`TM2to1.TrCfg` relation to `haltList tm [answer]`. It composes the paid input
prelude with the supplied run and one output write, reaching the whole singleton
output tape with blank tails. Its bound is `preludeSteps raw + B + 1`;
`nextNoneRun` pays one additional step to observe outer `none`. The native
evaluation theorem follows from this complete endpoint.
-/

namespace Resources.TuringSimulation.StackToTape.OrdinaryPackage

open Function Turing

abbrev Alphabet (tm : FinTM2) := Package.Alphabet tm

abbrev Control (tm : FinTM2) := MarkedInput.Control (Package.Control tm)

/-- The wrapper starts at its actual prelude, independently of the raw input. -/
@[instance_reducible] def controlInhabited (tm : FinTM2) : Inhabited (Control tm) :=
  ⟨.start⟩

/-- The entire primitive alphabet is finite when every source stack alphabet
is finite. FinTM2's input-only finite field does not replace this premise. -/
@[instance_reducible] def alphabetFintype (tm : FinTM2) [∀ k, Fintype (tm.Γ k)] :
    Fintype (Alphabet tm) :=
  Package.alphabetFintype tm

/-- The wrapper adds its four fixed phases to the already finite supported
native controls. No global finiteness of translated continuations is assumed. -/
@[instance_reducible] noncomputable def controlFintype (tm : FinTM2) :
    Fintype (Control tm) := by
  letI : Fintype (Package.Control tm) := Package.controlFintype tm
  infer_instance

/-- The exact supported native starting control supplied by the package. -/
def sourceDefault (tm : FinTM2) : Package.Control tm :=
  (Package.controlInhabited tm).default

theorem sourceDefault_val (tm : FinTM2) :
    (sourceDefault tm).val =
      (some ((TM2to1.tr tm.m) (.normal tm.main)), tm.initialState) := rfl

theorem sourceDefault_register (tm : FinTM2) :
    (sourceDefault tm).val.2 = tm.initialState := rfl

theorem wrapper_default (tm : FinTM2) :
    (controlInhabited tm).default = (MarkedInput.Control.start : Control tm) := rfl

/-- The ordinary alphabet injection is chosen once, before the input word. -/
def inputLetter (tm : FinTM2) : tm.Γ tm.k₀ ↪ Alphabet tm :=
  ⟨MarkedInput.symbol (Γ := tm.Γ) tm.k₀,
    MarkedInput.symbol_injective (Γ := tm.Γ) tm.k₀⟩

theorem inputLetter_ne_blank (tm : FinTM2) (a : tm.Γ tm.k₀) :
    inputLetter tm a ≠ (default : Alphabet tm) :=
  MarkedInput.symbol_ne_blank (Γ := tm.Γ) tm.k₀ a

theorem inputLetter_selected (tm : FinTM2) (a : tm.Γ tm.k₀) :
    (inputLetter tm a).2 tm.k₀ = some a :=
  MarkedInput.symbol_selected (Γ := tm.Γ) tm.k₀ a

theorem input_map_eq (tm : FinTM2) (raw : List (tm.Γ tm.k₀)) :
    raw.map (inputLetter tm) = MarkedInput.input (Γ := tm.Γ) tm.k₀ raw := rfl

theorem input_map_length (tm : FinTM2) (raw : List (tm.Γ tm.k₀)) :
    (raw.map (inputLetter tm)).length = raw.length := by
  simp only [List.length_map]

/-- One fixed output-cell function. The reached halt row contains some answer
at k₁; fallback only makes the transition function total on other cells. -/
def emitter (tm : FinTM2)
    (outputLetter : tm.Γ tm.k₁ → tm.Γ tm.k₀) (fallback : tm.Γ tm.k₁)
    (a : Alphabet tm) : Alphabet tm :=
  MarkedInput.symbol (Γ := tm.Γ) tm.k₀
    (outputLetter ((a.2 tm.k₁).getD fallback))

theorem haltRow_output (tm : FinTM2) (answer : tm.Γ tm.k₁) :
    SingletonOutput.haltRow tm answer tm.k₁ = some answer := by
  change Function.update (fun k : tm.K => (none : Option (tm.Γ k)))
    tm.k₁ (some answer) tm.k₁ = (some answer : Option (tm.Γ tm.k₁))
  exact Function.update_self tm.k₁ (some answer)
    (fun k : tm.K => (none : Option (tm.Γ k)))

/-- With distinct designated stores, the complete source halt has an empty
input track and a singleton output track. -/
theorem haltRow_input (tm : FinTM2) (answer : tm.Γ tm.k₁)
    (separate : tm.k₀ ≠ tm.k₁) :
    SingletonOutput.haltRow tm answer tm.k₀ = none := by
  change Function.update (fun k : tm.K => (none : Option (tm.Γ k)))
    tm.k₁ (some answer) tm.k₀ = (none : Option (tm.Γ tm.k₀))
  exact Function.update_of_ne separate (some answer)
    (fun k : tm.K => (none : Option (tm.Γ k)))

theorem emitter_halt_row (tm : FinTM2)
    (outputLetter : tm.Γ tm.k₁ → tm.Γ tm.k₀) (fallback answer : tm.Γ tm.k₁) :
    emitter tm outputLetter fallback (true, SingletonOutput.haltRow tm answer) =
      MarkedInput.symbol (Γ := tm.Γ) tm.k₀ (outputLetter answer) :=
  congrArg
    (fun observed : Option (tm.Γ tm.k₁) =>
      MarkedInput.symbol (Γ := tm.Γ) tm.k₀ (outputLetter (observed.getD fallback)))
    (haltRow_output tm answer)

theorem emitter_halt_readback (tm : FinTM2)
    (outputLetter : tm.Γ tm.k₁ → tm.Γ tm.k₀) (fallback answer : tm.Γ tm.k₁) :
    (emitter tm outputLetter fallback (true, SingletonOutput.haltRow tm answer)).2 tm.k₀ =
      some (outputLetter answer) :=
  (congrArg (fun a : Alphabet tm => a.2 tm.k₀)
    (emitter_halt_row tm outputLetter fallback answer)).trans
      (MarkedInput.symbol_selected (Γ := tm.Γ) tm.k₀ (outputLetter answer))

/-- The actual finite-control primitive machine. Its supplied wrapper start
is fixed, and its run phase inherits exactly Package.controlInhabited tm. -/
def machine (tm : FinTM2)
    (outputLetter : tm.Γ tm.k₁ → tm.Γ tm.k₀) (fallback : tm.Γ tm.k₁) :
    @TM0.Machine (Alphabet tm) (Control tm) (controlInhabited tm) := by
  letI : Inhabited (Package.Control tm) := Package.controlInhabited tm
  exact MarkedInput.machine (Γ := tm.Γ) tm.k₀ (Package.closedMachine tm)
    (emitter tm outputLetter fallback)

/-- Actual ordinary native initialization reaches the supplied source
default on the entire reflected encoded tape, with the exact prelude count. -/
theorem prelude_exact (tm : FinTM2)
    (outputLetter : tm.Γ tm.k₁ → tm.Γ tm.k₀) (fallback : tm.Γ tm.k₁)
    (raw : List (tm.Γ tm.k₀)) :
    (flip Bind.bind (TM0.step (machine tm outputLetter fallback)))^[MarkedInput.preludeSteps raw]
      (some (TM0.init (raw.map (MarkedInput.symbol (Γ := tm.Γ) tm.k₀)))) =
      some ⟨.run (sourceDefault tm),
        TapeReflection.tape (Tape.mk₁ (TM2to1.trInit (Γ := tm.Γ) tm.k₀ raw))⟩ := by
  let : Inhabited (Package.Control tm) := Package.controlInhabited tm
  exact MarkedInput.prelude_exact (Γ := tm.Γ) tm.k₀ (Package.closedMachine tm)
    (emitter tm outputLetter fallback) raw

/-- Done is a live control with a separate next transition to outer none. -/
theorem done_step (tm : FinTM2)
    (outputLetter : tm.Γ tm.k₁ → tm.Γ tm.k₀) (fallback : tm.Γ tm.k₁)
    (T : Tape (Alphabet tm)) :
    TM0.step (machine tm outputLetter fallback) ⟨.done, T⟩ = none := rfl

end Resources.TuringSimulation.StackToTape.OrdinaryPackage

namespace Resources.TuringSimulation.StackToTape.OrdinaryPackage

open Function Turing

abbrev NativeTarget (tm : FinTM2) :=
  TM1.Cfg (TM2to1.Γ' tm.K tm.Γ)
    (TM2to1.Λ' tm.K tm.Γ tm.Λ tm.σ) tm.σ

/-- The exact finite native image of the supplied full intermediate target. -/
noncomputable def mappedTarget (tm : FinTM2) (target : NativeTarget tm) :
    TM0.Cfg (Alphabet tm) (Package.Control tm) :=
  Package.mapCfg tm (TM1to0.trCfg (TM2to1.tr tm.m) target)

theorem mappedTarget_tape (tm : FinTM2) (target : NativeTarget tm) :
    (mappedTarget tm target).Tape = target.Tape :=
  (Package.mapCfg_tape tm (TM1to0.trCfg (TM2to1.tr tm.m) target)).trans rfl

/-- This is an actual native bounded run, with the exact supplied finite
default and full mapped endpoint. The alias introduces no timing assumption. -/
abbrev EncodedRun (tm : FinTM2) (raw : List (tm.Γ tm.k₀))
    (target : NativeTarget tm) (B : Nat) :=
  letI : Inhabited (Package.Control tm) := Package.controlInhabited tm
  StateTransition.EvalsToInTime (TM0.step (Package.closedMachine tm))
    (TM0.init (TM2to1.trInit (Γ := tm.Γ) tm.k₀ raw))
    (some (mappedTarget tm target)) B

/-- The complete ordinary stopped output, including both blank tails. -/
def outputCfg (tm : FinTM2)
    (outputLetter : tm.Γ tm.k₁ → tm.Γ tm.k₀) (answer : tm.Γ tm.k₁) :
    TM0.Cfg (Alphabet tm) (Control tm) :=
  ⟨.done, Tape.mk₁ [MarkedInput.symbol (Γ := tm.Γ) tm.k₀ (outputLetter answer)]⟩

theorem outputCfg_tape (tm : FinTM2)
    (outputLetter : tm.Γ tm.k₁ → tm.Γ tm.k₀) (answer : tm.Γ tm.k₁) :
    (outputCfg tm outputLetter answer).Tape =
      Tape.mk₁ [MarkedInput.symbol (Γ := tm.Γ) tm.k₀ (outputLetter answer)] := rfl

theorem outputCfg_stopped (tm : FinTM2)
    (outputLetter : tm.Γ tm.k₁ → tm.Γ tm.k₀) (fallback answer : tm.Γ tm.k₁) :
    TM0.step (machine tm outputLetter fallback) (outputCfg tm outputLetter answer) = none := rfl

/-- The entire mapped target is singleton, derived from every track in TrCfg. -/
theorem related_target_singleton (tm : FinTM2) (answer : tm.Γ tm.k₁)
    (target : NativeTarget tm)
    (related : TM2to1.TrCfg (Turing.haltList tm [answer]) target) :
    (mappedTarget tm target).Tape = Tape.mk₁ [(true, SingletonOutput.haltRow tm answer)] :=
  (mappedTarget_tape tm target).trans
    (SingletonOutput.haltList_singleton_tape tm answer target related)

theorem related_target_stopped (tm : FinTM2) (answer : tm.Γ tm.k₁)
    (target : NativeTarget tm)
    (related : TM2to1.TrCfg (Turing.haltList tm [answer]) target)
    (a : Alphabet tm) :
    Package.closedMachine tm (mappedTarget tm target).q a = none :=
  SingletonOutput.related_package_halt_stopped tm [answer] target related a

/-- Endpoint presentation only: both the actual primitive steps and its
upper-bound proof are reused without alteration. -/
def singletonRun (tm : FinTM2) (raw : List (tm.Γ tm.k₀))
    (answer : tm.Γ tm.k₁) (target : NativeTarget tm)
    (related : TM2to1.TrCfg (Turing.haltList tm [answer]) target)
    (B : Nat) (before : EncodedRun tm raw target B) :
    letI : Inhabited (Package.Control tm) := Package.controlInhabited tm
    StateTransition.EvalsToInTime (TM0.step (Package.closedMachine tm))
      (TM0.init (TM2to1.trInit (Γ := tm.Γ) tm.k₀ raw))
      (some ⟨(mappedTarget tm target).q,
        Tape.mk₁ [(true, SingletonOutput.haltRow tm answer)]⟩) B := by
  let : Inhabited (Package.Control tm) := Package.controlInhabited tm
  have endpoint : mappedTarget tm target =
      (⟨(mappedTarget tm target).q, Tape.mk₁ [(true, SingletonOutput.haltRow tm answer)]⟩ :
        TM0.Cfg (Alphabet tm) (Package.Control tm)) :=
    congrArg
      (fun T : Tape (Alphabet tm) =>
        (⟨(mappedTarget tm target).q, T⟩ : TM0.Cfg (Alphabet tm) (Package.Control tm)))
      (related_target_singleton tm answer target related)
  exact
    { steps := before.steps
      evals_in_steps := before.evals_in_steps.trans (congrArg some endpoint)
      steps_le_m := before.steps_le_m }

theorem singletonRun_steps (tm : FinTM2) (raw : List (tm.Γ tm.k₀))
    (answer : tm.Γ tm.k₁) (target : NativeTarget tm)
    (related : TM2to1.TrCfg (Turing.haltList tm [answer]) target)
    (B : Nat) (before : EncodedRun tm raw target B) :
    (singletonRun tm raw answer target related B before).steps = before.steps := rfl

private theorem emitted_endpoint (tm : FinTM2)
    (outputLetter : tm.Γ tm.k₁ → tm.Γ tm.k₀) (fallback answer : tm.Γ tm.k₁) :
    (some ⟨MarkedInput.Control.done,
      Tape.mk₁ [emitter tm outputLetter fallback (true, SingletonOutput.haltRow tm answer)]⟩ :
        Option (TM0.Cfg (Alphabet tm) (Control tm))) =
      some (outputCfg tm outputLetter answer) :=
  congrArg
    (fun a : Alphabet tm =>
      (some ⟨MarkedInput.Control.done, Tape.mk₁ [a]⟩ :
        Option (TM0.Cfg (Alphabet tm) (Control tm))))
    (emitter_halt_row tm outputLetter fallback answer)

/-- At the actual reflected related halt, one native transition writes the
complete ordinary singleton. A head observation alone is insufficient here. -/
theorem emit_related_halt_step (tm : FinTM2)
    (outputLetter : tm.Γ tm.k₁ → tm.Γ tm.k₀) (fallback answer : tm.Γ tm.k₁)
    (target : NativeTarget tm)
    (related : TM2to1.TrCfg (Turing.haltList tm [answer]) target) :
    TM0.step (machine tm outputLetter fallback)
      (MarkedInput.runConfiguration (mappedTarget tm target)) =
      some (outputCfg tm outputLetter answer) := by
  let : Inhabited (Package.Control tm) := Package.controlInhabited tm
  let marked : Alphabet tm := (true, SingletonOutput.haltRow tm answer)
  have reflected : TapeReflection.tape (mappedTarget tm target).Tape = Tape.mk₁ [marked] :=
    (congrArg TapeReflection.tape (related_target_singleton tm answer target related)).trans
      (SingletonOutput.reflection_singleton marked)
  have initial : MarkedInput.runConfiguration (mappedTarget tm target) =
      (⟨.run (mappedTarget tm target).q, Tape.mk₁ [marked]⟩ :
        TM0.Cfg (Alphabet tm) (Control tm)) :=
    congrArg
      (fun T : Tape (Alphabet tm) =>
        (⟨.run (mappedTarget tm target).q, T⟩ : TM0.Cfg (Alphabet tm) (Control tm)))
      reflected
  have output := MarkedInput.emit_singleton_step (Γ := tm.Γ)
    tm.k₀ (Package.closedMachine tm) (emitter tm outputLetter fallback)
    (mappedTarget tm target).q marked
    (related_target_stopped tm answer target related marked)
  exact (congrArg (TM0.step (machine tm outputLetter fallback)) initial).trans
    (output.trans (emitted_endpoint tm outputLetter fallback answer))

/-- Actual prelude, identical-count reflected primitive run, and one actual
output write. The raw input is a length-preserving per-letter map. -/
noncomputable def runInTime (tm : FinTM2)
    (outputLetter : tm.Γ tm.k₁ → tm.Γ tm.k₀) (fallback : tm.Γ tm.k₁)
    (raw : List (tm.Γ tm.k₀)) (answer : tm.Γ tm.k₁) (target : NativeTarget tm)
    (related : TM2to1.TrCfg (Turing.haltList tm [answer]) target)
    (B : Nat) (before : EncodedRun tm raw target B) :
    StateTransition.EvalsToInTime (TM0.step (machine tm outputLetter fallback))
      (TM0.init (raw.map (MarkedInput.symbol (Γ := tm.Γ) tm.k₀)))
      (some (outputCfg tm outputLetter answer)) (MarkedInput.preludeSteps raw + B + 1) := by
  let : Inhabited (Package.Control tm) := Package.controlInhabited tm
  let marked : Alphabet tm := (true, SingletonOutput.haltRow tm answer)
  let prepared := singletonRun tm raw answer target related B before
  let live := MarkedInput.normalizedRunInTime (Γ := tm.Γ)
    tm.k₀ (Package.closedMachine tm) (emitter tm outputLetter fallback)
    raw (mappedTarget tm target).q marked B prepared
    (related_target_stopped tm answer target related marked)
  exact
    { steps := live.steps
      evals_in_steps := live.evals_in_steps.trans
        (emitted_endpoint tm outputLetter fallback answer)
      steps_le_m := live.steps_le_m }

/-- The stored count is the original count plus the literal prelude and one
write. It is not replaced by the upper bound B. -/
theorem runInTime_steps (tm : FinTM2)
    (outputLetter : tm.Γ tm.k₁ → tm.Γ tm.k₀) (fallback : tm.Γ tm.k₁)
    (raw : List (tm.Γ tm.k₀)) (answer : tm.Γ tm.k₁) (target : NativeTarget tm)
    (related : TM2to1.TrCfg (Turing.haltList tm [answer]) target)
    (B : Nat) (before : EncodedRun tm raw target B) :
    (runInTime tm outputLetter fallback raw answer target related B before).steps =
      1 + (before.steps + MarkedInput.preludeSteps raw) := rfl

/-- The native evaluator returns the same complete ordinary output singleton. -/
theorem eval_of_run (tm : FinTM2)
    (outputLetter : tm.Γ tm.k₁ → tm.Γ tm.k₀) (fallback : tm.Γ tm.k₁)
    (raw : List (tm.Γ tm.k₀)) (answer : tm.Γ tm.k₁) (target : NativeTarget tm)
    (related : TM2to1.TrCfg (Turing.haltList tm [answer]) target)
    (B : Nat) (before : EncodedRun tm raw target B) :
    TM0.eval (machine tm outputLetter fallback)
        (raw.map (MarkedInput.symbol (Γ := tm.Γ) tm.k₀)) =
      Part.some (ListBlank.mk [MarkedInput.symbol (Γ := tm.Γ) tm.k₀ (outputLetter answer)]) := by
  let : Inhabited (Package.Control tm) := Package.controlInhabited tm
  let marked : Alphabet tm := (true, SingletonOutput.haltRow tm answer)
  let prepared := singletonRun tm raw answer target related B before
  have evaluated := MarkedInput.normalized_eval (Γ := tm.Γ)
    tm.k₀ (Package.closedMachine tm) (emitter tm outputLetter fallback)
    raw (mappedTarget tm target).q marked prepared.toEvalsTo
    (related_target_stopped tm answer target related marked)
  exact evaluated.trans
    (congrArg (fun a : Alphabet tm => Part.some (ListBlank.mk [a]))
      (emitter_halt_row tm outputLetter fallback answer))

/-- The distinct transition after the live output is charged separately. -/
noncomputable def nextNoneRun (tm : FinTM2)
    (outputLetter : tm.Γ tm.k₁ → tm.Γ tm.k₀) (fallback : tm.Γ tm.k₁)
    (raw : List (tm.Γ tm.k₀)) (answer : tm.Γ tm.k₁) (target : NativeTarget tm)
    (related : TM2to1.TrCfg (Turing.haltList tm [answer]) target)
    (B : Nat) (before : EncodedRun tm raw target B) :
    StateTransition.EvalsToInTime (TM0.step (machine tm outputLetter fallback))
      (TM0.init (raw.map (MarkedInput.symbol (Γ := tm.Γ) tm.k₀))) none
      (MarkedInput.preludeSteps raw + B + 2) := by
  let live := runInTime tm outputLetter fallback raw answer target related B before
  let terminal : StateTransition.EvalsTo (TM0.step (machine tm outputLetter fallback))
      (outputCfg tm outputLetter answer) none :=
    { steps := 1
      evals_in_steps := rfl }
  exact
    { toEvalsTo := StateTransition.EvalsTo.trans
        (TM0.step (machine tm outputLetter fallback))
        (TM0.init (raw.map (MarkedInput.symbol (Γ := tm.Γ) tm.k₀)))
        (outputCfg tm outputLetter answer) none live.toEvalsTo terminal
      steps_le_m := by
        change 1 + live.steps ≤ MarkedInput.preludeSteps raw + B + 2
        have bounded := Nat.add_le_add_left live.steps_le_m 1
        simpa only [Nat.add_comm 1 (MarkedInput.preludeSteps raw + B + 1)] using bounded }

theorem nextNoneRun_steps (tm : FinTM2)
    (outputLetter : tm.Γ tm.k₁ → tm.Γ tm.k₀) (fallback : tm.Γ tm.k₁)
    (raw : List (tm.Γ tm.k₀)) (answer : tm.Γ tm.k₁) (target : NativeTarget tm)
    (related : TM2to1.TrCfg (Turing.haltList tm [answer]) target)
    (B : Nat) (before : EncodedRun tm raw target B) :
    (nextNoneRun tm outputLetter fallback raw answer target related B before).steps =
      1 + (runInTime tm outputLetter fallback raw answer target related B before).steps := rfl

/-- Convenient proposition form retains both live and outer-none native
witnesses, the stopped live output, and the native evaluation result. -/
theorem run_and_eval (tm : FinTM2)
    (outputLetter : tm.Γ tm.k₁ → tm.Γ tm.k₀) (fallback : tm.Γ tm.k₁)
    (raw : List (tm.Γ tm.k₀)) (answer : tm.Γ tm.k₁) (target : NativeTarget tm)
    (related : TM2to1.TrCfg (Turing.haltList tm [answer]) target)
    (B : Nat) (before : EncodedRun tm raw target B) :
    Nonempty (StateTransition.EvalsToInTime (TM0.step (machine tm outputLetter fallback))
      (TM0.init (raw.map (MarkedInput.symbol (Γ := tm.Γ) tm.k₀)))
      (some (outputCfg tm outputLetter answer)) (MarkedInput.preludeSteps raw + B + 1)) ∧
      TM0.step (machine tm outputLetter fallback) (outputCfg tm outputLetter answer) = none ∧
      TM0.eval (machine tm outputLetter fallback)
          (raw.map (MarkedInput.symbol (Γ := tm.Γ) tm.k₀)) =
        Part.some (ListBlank.mk [MarkedInput.symbol (Γ := tm.Γ) tm.k₀ (outputLetter answer)]) ∧
      Nonempty (StateTransition.EvalsToInTime (TM0.step (machine tm outputLetter fallback))
        (TM0.init (raw.map (MarkedInput.symbol (Γ := tm.Γ) tm.k₀))) none
        (MarkedInput.preludeSteps raw + B + 2)) :=
  ⟨⟨runInTime tm outputLetter fallback raw answer target related B before⟩,
    outputCfg_stopped tm outputLetter fallback answer,
    eval_of_run tm outputLetter fallback raw answer target related B before,
    ⟨nextNoneRun tm outputLetter fallback raw answer target related B before⟩⟩

end Resources.TuringSimulation.StackToTape.OrdinaryPackage

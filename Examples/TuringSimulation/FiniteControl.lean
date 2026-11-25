import Applications.Resources.TuringSimulation.FiniteControl
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option warningAsError true

namespace Examples.TuringSimulation.FiniteControl

open Resources.TuringSimulation.FiniteControl

open Function Turing

def ambient : TM0.Machine Bool ℕ
  | 0, a => some (1, .write a)
  | 1, _ => none
  | n + 2, _ => some (n + 3, .move .right)

def support : Finset ℕ := {0, 1}

theorem supported : TM0.Supports ambient (↑support) := by
  constructor
  · change 0 ∈ support
    simp [support]
  · intro q a q' act hstep hq
    have choices : q = 0 ∨ q = 1 := by
      simpa only [Finset.mem_coe, support, Finset.mem_insert,
        Finset.mem_singleton] using hq
    rcases choices with rfl | rfl
    · change some (1, TM0.Stmt.write a) = some (q', act) at hstep
      cases hstep
      simp [support]
    · change (none : Option (ℕ × TM0.Stmt Bool)) = some (q', act) at hstep
      cases hstep

theorem source_zero_step (T : Tape Bool) :
    TM0.step ambient ⟨0, T⟩ = some ⟨1, T⟩ := by
  change some (TM0.Cfg.mk 1 (T.write T.head)) = some (TM0.Cfg.mk 1 T)
  rw [Tape.write_self]

theorem source_one_halts (T : Tape Bool) :
    TM0.step ambient ⟨1, T⟩ = none := rfl

def sourceLiveRun (l : List Bool) :
    StateTransition.EvalsToInTime (TM0.step ambient)
      (TM0.init l) (some ⟨1, Tape.mk₁ l⟩) 1 where
  toEvalsTo := {
    steps := 1
    evals_in_steps := by
      change TM0.step ambient (⟨0, Tape.mk₁ l⟩ : TM0.Cfg Bool ℕ) =
        some ⟨1, Tape.mk₁ l⟩
      exact source_zero_step (Tape.mk₁ l) }
  steps_le_m := Nat.le_refl 1

def sourceNoneRun (l : List Bool) :
    StateTransition.EvalsToInTime (TM0.step ambient) (TM0.init l) none 2 where
  toEvalsTo := {
    steps := 2
    evals_in_steps := by
      rw [Function.iterate_succ_apply']
      simp only [Function.iterate_one, Function.flip_def, bind, Option.bind_some]
      rw [show TM0.step ambient (TM0.init l) = some ⟨1, Tape.mk₁ l⟩ from
        source_zero_step (Tape.mk₁ l)]
      rfl }
  steps_le_m := Nat.le_refl 2

local instance : Inhabited {q : ℕ // q ∈ support} :=
  restrictedInhabited support supported.1

example : Infinite ℕ := inferInstance
example : Fintype {q : ℕ // q ∈ support} := inferInstance

noncomputable def finiteMachine : TM0.Machine Bool {q : ℕ // q ∈ support} :=
  restrictMachine ambient support supported.1

def finiteHalt (l : List Bool) : TM0.Cfg Bool {q : ℕ // q ∈ support} :=
  ⟨⟨1, by simp [support]⟩, Tape.mk₁ l⟩

/-- The actual subtype machine starts at native init on the original tape
and returns outer none with precisely the source witness's two transitions. -/
noncomputable def finiteNoneRun (l : List Bool) :
    StateTransition.EvalsToInTime (TM0.step finiteMachine)
      (TM0.init l) none 2 :=
  restrictInitialEvalsToInTime ambient support supported l none 2 (sourceNoneRun l)

theorem finiteNoneRun_steps (l : List Bool) : (finiteNoneRun l).steps = 2 := rfl

/-- The preceding live halt is represented separately and retains the full
initial tape, including the original Boolean input list. -/
noncomputable def finiteLiveRun (l : List Bool) :
    StateTransition.EvalsToInTime (TM0.step finiteMachine)
      (TM0.init l) (some (finiteHalt l)) 1 := by
  refine {
    toEvalsTo := { steps := 1, evals_in_steps := ?_ }
    steps_le_m := Nat.le_refl 1 }
  have e := (restrictInitialEvalsToInTime ambient support supported
    l (some ⟨1, Tape.mk₁ l⟩) 1 (sourceLiveRun l)).evals_in_steps
  change (flip bind (TM0.step finiteMachine))^[1] (some (TM0.init l)) =
    some (restrictCfg support supported.1 (⟨1, Tape.mk₁ l⟩ : TM0.Cfg Bool ℕ)) at e
  rw [restrictCfg_supported support supported.1
    (⟨1, Tape.mk₁ l⟩ : TM0.Cfg Bool ℕ) (by simp [support])] at e
  exact e

theorem finiteLiveRun_steps (l : List Bool) : (finiteLiveRun l).steps = 1 := rfl

theorem finiteHalt_halts (l : List Bool) :
    TM0.step finiteMachine (finiteHalt l) = none := by
  have e := restrict_step ambient support supported
    (⟨1, Tape.mk₁ l⟩ : TM0.Cfg Bool ℕ) (by simp [support])
  rw [source_one_halts, Option.map_none,
    restrictCfg_supported support supported.1
      (⟨1, Tape.mk₁ l⟩ : TM0.Cfg Bool ℕ) (by simp [support])] at e
  exact e.symm

end Examples.TuringSimulation.FiniteControl


namespace Examples.TuringSimulation.FiniteControl

open Resources.TuringSimulation.FiniteControl

open Turing

local instance : Inhabited {q : ℕ // q ∈ support} :=
  restrictedInhabited support supported.1

def closedFiniteMachine : TM0.Machine Bool {q : ℕ // q ∈ support} :=
  closedRestrictMachine ambient support supported

theorem closedFiniteMachine_eq : closedFiniteMachine = finiteMachine :=
  closedRestrictMachine_eq ambient support supported

def closedFiniteLiveRun (l : List Bool) :
    StateTransition.EvalsToInTime (TM0.step closedFiniteMachine)
      (TM0.init l) (some (finiteHalt l)) 1 where
  toEvalsTo := {
    steps := 1
    evals_in_steps := by
      rw [closedFiniteMachine_eq]
      exact (finiteLiveRun l).evals_in_steps }
  steps_le_m := Nat.le_refl 1

def closedFiniteNoneRun (l : List Bool) :
    StateTransition.EvalsToInTime (TM0.step closedFiniteMachine)
      (TM0.init l) none 2 where
  toEvalsTo := {
    steps := 2
    evals_in_steps := by
      rw [closedFiniteMachine_eq]
      exact (finiteNoneRun l).evals_in_steps }
  steps_le_m := Nat.le_refl 2

theorem closedFiniteLiveRun_steps (l : List Bool) :
    (closedFiniteLiveRun l).steps = 1 := rfl

theorem closedFiniteNoneRun_steps (l : List Bool) :
    (closedFiniteNoneRun l).steps = 2 := rfl

end Examples.TuringSimulation.FiniteControl

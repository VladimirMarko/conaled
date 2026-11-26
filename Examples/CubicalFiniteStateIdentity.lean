import Examples.CubicalStructuredState
import Examples.NativeModelCombination
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Group.Action.End

/-! A finite machine, its distinct presentation, and a bijection rejected by
transition preservation. The even-to-odd package is a second specialization. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalFiniteStateIdentity
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open CubicalStateTransport CubicalStatePackageFamily CubicalStatePackageUa
open CubicalStructuredState CubicalUnivalenceTransport CubicalGlue

inductive Phase where
  | idle | ready | failed
  deriving DecidableEq

def presentation : Fin 3 ≃ Phase where
  toFun n := if n = 0 then .idle else if n = 1 then .ready else .failed
  invFun p := match p with | .idle => 0 | .ready => 1 | .failed => 2
  left_inv n := by fin_cases n <;> rfl
  right_inv p := by cases p <;> rfl

def machine : StatePackage (Fin 3) where
  initial := 0
  step n := if n = 0 then 1 else n
  Invariant n := n ≠ 2
  initial_valid := by decide
  preserves n h := by split <;> simp_all

def presentedMachine : StatePackage Phase := machine.conjugate presentation

def observer : Phase → Nat
  | .idle => 0
  | .ready => 1
  | .failed => 2

theorem machine_preserved : Preserves presentation machine presentedMachine := Preserves.of_eq rfl

/-- A direct operation transport used for the same client as the package path. -/
def transportOperation {S T : Type} (e : S ≃ T) (step : S → S) : T → T :=
  e ∘ step ∘ e.symm

theorem operation_recovery {S T : Type} (e : S ≃ T) (step : S → S) (s : S) :
    e.symm (transportOperation e step (e s)) = step s := by
  simp [transportOperation]

theorem machine_operation_comparison : presentedMachine.step = transportOperation presentation machine.step := rfl

theorem direct_observation : observer (presentedMachine.step presentedMachine.initial) = 1 := rfl

noncomputable def nativeEquivalence := HomotopyEquivalence.ofIso (codeIso presentation)

/-- Forward maps agree exactly; inverse agreement follows from injectivity.
The native contraction record is not claimed equal to another chosen record. -/
theorem admittedCarrier_of_iso {S T : Type} (e : S ≃ T) :
    admittedCarrier (codeIso e).hom (HomotopyEquivalence.ofIso (codeIso e)) = e := by
  apply Equiv.ext
  intro s
  change (constantLocal _ T).decodeCodeIso.hom.app point
    ((codeIso e).hom.app point ((constantLocal _ S).decodeCodeIso.inv.app point s)) = e s
  exact congrArg (fun t => t.val point) (codeIso_action e s)

noncomputable def machinePath :=
  (uaStructureIdentity (codeIso presentation).hom nativeEquivalence machine presentedMachine).symm
    (by
      rw [nativeEquivalence, admittedCarrier_of_iso]
      exact machine_preserved)

noncomputable def machineTransported := targetPackage (codeIso presentation).hom nativeEquivalence machine

theorem machineTransported_eq : machineTransported = presentedMachine := by
  rw [machineTransported, targetPackage_eq, nativeEquivalence, admittedCarrier_of_iso]
  rfl

theorem transported_observation : observer (machineTransported.step machineTransported.initial) = 1 := by
  rw [machineTransported_eq]
  exact direct_observation

theorem transported_invariant : machineTransported.Invariant .ready ∧ ¬ machineTransported.Invariant .failed := by
  rw [machineTransported_eq]
  change (1 : Fin 3) ≠ 2 ∧ ¬ ((2 : Fin 3) ≠ 2)
  decide

/-- Swapping the two noninitial states preserves the initial point but fails
at the first transition. A carrier equivalence alone cannot supply this law. -/
def wrongPresentation : Fin 3 ≃ Phase := (Equiv.swap 1 2).trans presentation

theorem wrong_initial : wrongPresentation machine.initial = presentedMachine.initial := by decide

theorem wrong_transition :
    wrongPresentation (machine.step 0) ≠ presentedMachine.step (wrongPresentation 0) := by decide

theorem wrong_rejected : ¬ Preserves wrongPresentation machine presentedMachine := by
  intro h
  have hs := congrFun h.step (wrongPresentation 0)
  change wrongPresentation (machine.step (wrongPresentation.symm (wrongPresentation 0))) =
    presentedMachine.step (wrongPresentation 0) at hs
  rw [Equiv.symm_apply_apply] at hs
  exact wrong_transition hs

/-- The rejected carrier bijection cannot admit a complete structured path
with these endpoints over its selected ua line. -/
theorem wrong_path_rejected : IsEmpty
    (StructuredPath
      (admittedLine (codeIso wrongPresentation).hom (HomotopyEquivalence.ofIso (codeIso wrongPresentation)))
      (admittedPresentation (codeIso wrongPresentation).hom (HomotopyEquivalence.ofIso (codeIso wrongPresentation)))
      (admittedCarrier (codeIso wrongPresentation).hom (HomotopyEquivalence.ofIso (codeIso wrongPresentation)))
      machine presentedMachine) := by
  refine ⟨fun r => ?_⟩
  have h := (uaStructureIdentity (codeIso wrongPresentation).hom
    (HomotopyEquivalence.ofIso (codeIso wrongPresentation)) machine presentedMachine) r
  rw [admittedCarrier_of_iso] at h
  exact wrong_rejected h

noncomputable def evenOddPath :=
  (uaStructureIdentity (codeIso successor).hom (HomotopyEquivalence.ofIso (codeIso successor))
    evenPackage oddPackage).symm (by
      rw [admittedCarrier_of_iso]
      exact Preserves.of_eq rfl)

theorem evenOdd_recovery :
    targetPackage (codeIso successor).hom (HomotopyEquivalence.ofIso (codeIso successor)) evenPackage = oddPackage := by
  rw [targetPackage_eq, admittedCarrier_of_iso]
  rfl

/-- #437's operation/observer combination on the identical machine and observer.
The native action is evaluation of endomorphisms; its unit is identity, not the
selected machine state. -/
def combined := NativeModelCombination.combine (M := Function.End (Fin 3))
  machine.initial presentedMachine.initial 0 observer presentation rfl

theorem combined_step_observation : combined.out (machine.step machine.initial) = 1 := by
  calc
    _ = observer (presentation (machine.step machine.initial)) :=
      combined.action_output presentation rfl machine.step machine.initial
    _ = 1 := rfl

theorem combined_native_agreement : combined.out (machine.step machine.initial) =
    observer (machineTransported.step machineTransported.initial) :=
  combined_step_observation.trans transported_observation.symm

end Examples.CubicalFiniteStateIdentity

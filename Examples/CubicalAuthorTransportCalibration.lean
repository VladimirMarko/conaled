import Examples.CubicalAuthorTransport

/-! Public calibration for the bounded interface. These solved cases are
excluded from the independent author trial. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalAuthorTransportCalibration
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open CubicalAuthorTransport CubicalStateTransport CubicalStructuredState
open CubicalFiniteStateIdentity

noncomputable def machineChange := Change.ofEquiv presentation

noncomputable def machinePath : machineChange.PackagePath machine presentedMachine :=
  machineChange.path (by
    rw [machineChange, Change.carrier_ofEquiv]
    exact machine_preserved)

theorem machine_transport : machineChange.transport machine = presentedMachine := by
  exact Change.transport_ofEquiv presentation machine

theorem machine_observation :
    observer ((machineChange.transport machine).step (machineChange.transport machine).initial) = 1 := by
  rw [machine_transport]
  exact direct_observation

theorem machine_invariant : (machineChange.transport machine).invariant Phase.ready ∧
    ¬ (machineChange.transport machine).invariant Phase.failed := by
  rw [machine_transport]
  change (1 : Fin 3) ≠ 2 ∧ ¬ ((2 : Fin 3) ≠ 2)
  decide

/-- The native body is recovered, not merely the output record. -/
theorem machine_native_recovery : machineChange.nativeSection machine =
    CubicalStatePackageFamily.pullPackage machineChange.line
      (admittedPresentation machineChange.map machineChange.equivalence)
      (machine.conjugate machineChange.carrier) := machineChange.native_recovery machine

theorem wrong_path_rejected : IsEmpty
    ((Change.ofEquiv wrongPresentation).PackagePath machine presentedMachine) := by
  refine ⟨fun r => ?_⟩
  have h := (Change.ofEquiv wrongPresentation).packageIdentity machine presentedMachine r
  rw [Change.carrier_ofEquiv] at h
  exact wrong_rejected h

noncomputable def shift := Change.ofEquiv successor
noncomputable def twice := shift.trans shift

theorem repeated_transport : twice.transport evenPackage =
    shift.transport (shift.transport evenPackage) := shift.transport_trans shift evenPackage

theorem twice_package : twice.transport evenPackage =
    evenPackage.conjugate (successor.trans successor) := by
  rw [twice, Change.transport_eq, Change.carrier_trans, shift, Change.carrier_ofEquiv]

theorem twice_initial : (twice.transport evenPackage).initial = 2 := by
  rw [twice_package]
  rfl

theorem twice_step : (twice.transport evenPackage).step 4 = 6 := by
  rw [twice_package]
  rfl

theorem twice_invariant : (twice.transport evenPackage).invariant 2 ∧
    ¬ (twice.transport evenPackage).invariant 3 := by
  rw [twice_package]
  change (0 : Int) % 2 = 0 ∧ ¬ (1 : Int) % 2 = 0
  decide

theorem machine_roundtrip :
    machineChange.reverse.transport (machineChange.transport machine) = machine :=
  machineChange.transport_roundtrip machine

end Examples.CubicalAuthorTransportCalibration

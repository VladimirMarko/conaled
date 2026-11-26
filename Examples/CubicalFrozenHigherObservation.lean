import Examples.CubicalFrozenAssignment

/-! The actual frozen higher binder retains the selected nonzero cubical identity. -/
noncomputable section
namespace Examples.CubicalCocycleAssignment
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open SquareKit.Cubical.CategoryCocycles
open Examples.FrozenMemoStages

theorem retained_homotopy :
    HEq ((selectedHomotopy cocycleStructuralModel cocycleBase cocycleRootedFamily).down.reindex assignInput)
      (secondIdentity terminal.{0}) :=
  Term.convert_heq homotopy_at_assignment.symm (secondIdentity terminal)

/-- Only the retained type equality is transported; the interpreted source value is used. -/
def selectedNormalizedHomotopy : Term (secondIdentityFamily terminal.{0}) :=
  cast (type_eq_of_heq retained_homotopy)
    ((selectedHomotopy cocycleStructuralModel cocycleBase cocycleRootedFamily).down.reindex assignInput)

theorem selectedNormalizedHomotopy_eq : selectedNormalizedHomotopy = secondIdentity terminal.{0} :=
  eq_of_heq ((cast_heq _ _).trans retained_homotopy)

theorem frozen_higher_observation : secondObservation selectedNormalizedHomotopy = 1 :=
  (congrArg secondObservation selectedNormalizedHomotopy_eq).trans secondObservation_selected

/-- Replacing the selected source homotopy by reflexivity changes its observation. -/
theorem selectedNormalizedHomotopy_ne_secondZero : selectedNormalizedHomotopy ≠ secondZero terminal.{0} := by
  intro h
  have e := (congrArg secondObservation h).trans secondObservation_zero
  exact Int.one_ne_zero (frozen_higher_observation.symm.trans e)

end Examples.CubicalCocycleAssignment

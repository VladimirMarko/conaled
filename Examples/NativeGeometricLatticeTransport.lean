import Examples.NativeLatticeTransportCases

/-! The geometric flat-lattice bridge exercised through both native models. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.NativeGeometricLatticeTransport
open CategoryTheory Examples.LatticeTransportBridge Examples.CompositionalStructureIdentity
open Applications.Matroid
abbrev FlatCarrier := Flat (Geometric.matroid (Set (Fin 2)))
namespace Presheaf
open SquareKit.Cubical.Presheaf StructureIdentity.Native StructuredIdentity
open Examples.NativeLatticeTransport.Presheaf
variable {Γ : Context.{1}}

noncomputable def sourceAdmission := admission (Γ := Γ) (Set (Fin 2))
noncomputable def targetAdmission := admission (Γ := Γ) FlatCarrier

/-- The supplied geometric order isomorphism produces an actual law-bearing path. -/
noncomputable def transport := latticePathData (sourceAdmission (Γ := Γ)) targetAdmission flatsBridge
noncomputable def path := (transport (Γ := Γ)).path

theorem source_eq : (transport (Γ := Γ)).source = sourceObject sourceAdmission :=
  latticePathData_source _ _ _

theorem target_eq : (transport (Γ := Γ)).target = targetObject sourceAdmission targetAdmission flatsBridge :=
  latticePathData_target _ _ _

theorem path_eq : path (Γ := Γ) = latticePath sourceAdmission targetAdmission flatsBridge :=
  latticePathData_path _ _ _

noncomputable def pathRecovery :=
  UaComparison.modelRightInverseAt lattice (transport (Γ := Γ)).source transport.target transport.path

noncomputable def selectedRecovery :=
  equivalenceRecoveryData (sourceAdmission (Γ := Γ)) targetAdmission flatsBridge

theorem selectedRecovery_target : (selectedRecovery (Γ := Γ)).target =
    structuredEquivalence sourceAdmission targetAdmission flatsBridge :=
  equivalenceRecoveryData_target _ _ _

noncomputable def projectionRecovery :=
  latticeProjectionData (sourceAdmission (Γ := Γ)) targetAdmission flatsBridge

/-- Both values use actual native transport along the law-bearing path projection. -/
noncomputable def inclusionWitness (x : Γ.Elements) : OrderedPair FlatCarrier :=
  pathOrderedPair sourceAdmission targetAdmission flatsBridge inclusion x

theorem inclusionWitness_eq (x : Γ.Elements) : inclusionWitness x = flatInclusion :=
  pathOrderedPair_direct _ _ _ _ _

theorem inclusionWitness_strict (x : Γ.Elements) :
    (inclusionWitness x).val.1 ≠ (inclusionWitness x).val.2 := by
  rw [inclusionWitness_eq]
  exact flatInclusion_strict

noncomputable def nativeSolution (x : Γ.Elements) :=
  pathSolution sourceAdmission targetAdmission flatsBridge inclusion x

theorem nativeSolution_recovery (x : Γ.Elements) :
    (presentedSolutionsTransport Examples.NativeStructureRecovery.comparablePair
      sourceAdmission.decoding targetAdmission.decoding flatsBridge.toEquiv (fields sourceAdmission) x).symm
      (nativeSolution x) = orderedWitness sourceAdmission inclusion x := by
  unfold nativeSolution
  rw [pathSolution_moved]
  exact movedWitness_recovery _ _ _ _ _

theorem meet_recovery (x : Γ.Elements) (u v : FlatCarrier) :
    (decode Examples.CompositionalStructureIdentity.rawLattice targetAdmission.decoding x
      ((movedFields sourceAdmission targetAdmission flatsBridge).val x)).1 u v = u ⊓ v :=
  movedFields_meet _ _ _ _ _ _

theorem join_recovery (x : Γ.Elements) (u v : FlatCarrier) :
    (decode Examples.CompositionalStructureIdentity.rawLattice targetAdmission.decoding x
      ((movedFields sourceAdmission targetAdmission flatsBridge).val x)).2 u v = u ⊔ v :=
  movedFields_join _ _ _ _ _ _

end Presheaf
namespace Cartesian
open SquareKit.Cubical.Cartesian StructureIdentity.Native StructuredIdentity
open Examples.NativeLatticeTransport.Cartesian
variable {Γ : Context.{1}}

noncomputable def sourceAdmission := admission (Γ := Γ) (Set (Fin 2))
noncomputable def targetAdmission := admission (Γ := Γ) FlatCarrier

/-- The supplied geometric order isomorphism produces an actual law-bearing path. -/
noncomputable def transport := latticePathData (sourceAdmission (Γ := Γ)) targetAdmission flatsBridge
noncomputable def path := (transport (Γ := Γ)).path

theorem source_eq : (transport (Γ := Γ)).source = sourceObject sourceAdmission :=
  latticePathData_source _ _ _

theorem target_eq : (transport (Γ := Γ)).target = targetObject sourceAdmission targetAdmission flatsBridge :=
  latticePathData_target _ _ _

theorem path_eq : path (Γ := Γ) = latticePath sourceAdmission targetAdmission flatsBridge :=
  latticePathData_path _ _ _

noncomputable def pathRecovery :=
  UaComparison.modelRightInverseAt lattice (transport (Γ := Γ)).source transport.target transport.path

noncomputable def selectedRecovery :=
  equivalenceRecoveryData (sourceAdmission (Γ := Γ)) targetAdmission flatsBridge

theorem selectedRecovery_target : (selectedRecovery (Γ := Γ)).target =
    structuredEquivalence sourceAdmission targetAdmission flatsBridge :=
  equivalenceRecoveryData_target _ _ _

noncomputable def projectionRecovery :=
  latticeProjectionData (sourceAdmission (Γ := Γ)) targetAdmission flatsBridge

/-- Both values use actual native transport along the law-bearing path projection. -/
noncomputable def inclusionWitness (x : Γ.Elements) : OrderedPair FlatCarrier :=
  pathOrderedPair sourceAdmission targetAdmission flatsBridge inclusion x

theorem inclusionWitness_eq (x : Γ.Elements) : inclusionWitness x = flatInclusion :=
  pathOrderedPair_direct _ _ _ _ _

theorem inclusionWitness_strict (x : Γ.Elements) :
    (inclusionWitness x).val.1 ≠ (inclusionWitness x).val.2 := by
  rw [inclusionWitness_eq]
  exact flatInclusion_strict

noncomputable def nativeSolution (x : Γ.Elements) :=
  pathSolution sourceAdmission targetAdmission flatsBridge inclusion x

theorem nativeSolution_recovery (x : Γ.Elements) :
    (presentedSolutionsTransport Examples.NativeStructureRecovery.comparablePair
      sourceAdmission.decoding targetAdmission.decoding flatsBridge.toEquiv (fields sourceAdmission) x).symm
      (nativeSolution x) = orderedWitness sourceAdmission inclusion x := by
  unfold nativeSolution
  rw [pathSolution_moved]
  exact movedWitness_recovery _ _ _ _ _

theorem meet_recovery (x : Γ.Elements) (u v : FlatCarrier) :
    (decode Examples.CompositionalStructureIdentity.rawLattice targetAdmission.decoding x
      ((movedFields sourceAdmission targetAdmission flatsBridge).val x)).1 u v = u ⊓ v :=
  movedFields_meet _ _ _ _ _ _

theorem join_recovery (x : Γ.Elements) (u v : FlatCarrier) :
    (decode Examples.CompositionalStructureIdentity.rawLattice targetAdmission.decoding x
      ((movedFields sourceAdmission targetAdmission flatsBridge).val x)).2 u v = u ⊔ v :=
  movedFields_join _ _ _ _ _ _

end Cartesian

/-- The independently selected native paths have the same complete dependent observation. -/
theorem models_inclusion {Γ : SquareKit.Cubical.Presheaf.Context.{1}}
    (x : (SquareKit.Cubical.Cartesian.restrict Γ).Elements) :
    Presheaf.inclusionWitness ((SquareKit.Cubical.Cartesian.elements Γ).obj x) =
      Cartesian.inclusionWitness x := by
  rw [Presheaf.inclusionWitness_eq, Cartesian.inclusionWitness_eq]

end Examples.NativeGeometricLatticeTransport

import SquareKit.Internal.Cubical.NativeStructureFiniteCoherence
import SquareKit.Internal.Cubical.CartesianNativeStructureFiniteCoherence
import Examples.NativeStructureCoherence

/-! Integer translations exercise finite native coherence on actual admissions. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.NativeFiniteCoherence.Presheaf
open CategoryTheory SquareKit.Cubical.Presheaf StructureIdentity.Coherence
open Examples.NativeStructureCoherence.Presheaf
open Examples.NativeLatticeTransport.Presheaf (admission carrierSet)
variable {Γ : Context.{1}}
variable (admitted : SmallUniverse.LargeConstructors.Result (constantFamily Γ (ULift.{1} ℤ)))

noncomputable def e := move admitted 0 1
noncomputable def f := move admitted 1 2
noncomputable def g := move admitted 3 3
noncomputable def h := move admitted 6 4

noncomputable def triple : Finite.TripleWitnesses (e admitted) (f admitted) (g admitted) where
  pairLeft := HomotopyEquivalence.ofIso ((shift admitted 1) ≪≫ (shift admitted 2))
  pairRight := HomotopyEquivalence.ofIso ((shift admitted 2) ≪≫ (shift admitted 3))
  outerLeft := HomotopyEquivalence.ofIso (((shift admitted 1) ≪≫ (shift admitted 2)) ≪≫ (shift admitted 3))
  outerRight := HomotopyEquivalence.ofIso ((shift admitted 1) ≪≫ ((shift admitted 2) ≪≫ (shift admitted 3)))

noncomputable def selectedAssociator :=
  (triple admitted).selectedAssociator (e admitted) (f admitted) (g admitted) (carrierSet admitted)
noncomputable def compatibility :=
  (triple admitted).compatibility (e admitted) (f admitted) (g admitted) (carrierSet admitted) (carrierSet admitted)
noncomputable def triangle := Finite.triangle (carrierSet admitted) (carrierSet admitted)
  (Coded.path (e admitted)) (Coded.path (f admitted))
noncomputable def pentagon := Finite.pentagon (carrierSet admitted) (carrierSet admitted)
  (Coded.path (e admitted)) (Coded.path (f admitted))
  (Coded.path (g admitted)) (Coded.path (h admitted))

noncomputable def four : Finite.FourWitnesses (e admitted) (f admitted) (g admitted) (h admitted) where
  pair12 := HomotopyEquivalence.ofIso ((shift admitted 1) ≪≫ (shift admitted 2))
  pair23 := HomotopyEquivalence.ofIso ((shift admitted 2) ≪≫ (shift admitted 3))
  pair34 := HomotopyEquivalence.ofIso ((shift admitted 3) ≪≫ (shift admitted 4))
  triple123L := HomotopyEquivalence.ofIso (((shift admitted 1) ≪≫ (shift admitted 2)) ≪≫ (shift admitted 3))
  triple123R := HomotopyEquivalence.ofIso ((shift admitted 1) ≪≫ ((shift admitted 2) ≪≫ (shift admitted 3)))
  triple234L := HomotopyEquivalence.ofIso (((shift admitted 2) ≪≫ (shift admitted 3)) ≪≫ (shift admitted 4))
  triple234R := HomotopyEquivalence.ofIso ((shift admitted 2) ≪≫ ((shift admitted 3) ≪≫ (shift admitted 4)))
  outer0 := HomotopyEquivalence.ofIso ((((shift admitted 1) ≪≫ (shift admitted 2)) ≪≫ (shift admitted 3)) ≪≫ (shift admitted 4))
  outer1 := HomotopyEquivalence.ofIso (((shift admitted 1) ≪≫ ((shift admitted 2) ≪≫ (shift admitted 3))) ≪≫ (shift admitted 4))
  outer2 := HomotopyEquivalence.ofIso ((shift admitted 1) ≪≫ (((shift admitted 2) ≪≫ (shift admitted 3)) ≪≫ (shift admitted 4)))
  outer3 := HomotopyEquivalence.ofIso ((shift admitted 1) ≪≫ ((shift admitted 2) ≪≫ ((shift admitted 3) ≪≫ (shift admitted 4))))
  outer4 := HomotopyEquivalence.ofIso (((shift admitted 1) ≪≫ (shift admitted 2)) ≪≫ ((shift admitted 3) ≪≫ (shift admitted 4)))

noncomputable def selectedPentagon :=
  (four admitted).selectedPentagon (e admitted) (f admitted) (g admitted) (h admitted)
    (carrierSet admitted) (carrierSet admitted) (carrierSet admitted)
noncomputable def identityWitness := HomotopyEquivalence.ofIso (Iso.refl (A admitted))
noncomputable def leftUnit := Finite.leftUnitCompatibility (carrierSet admitted) (carrierSet admitted) (e admitted)
  (identityWitness admitted) (HomotopyEquivalence.ofIso ((Iso.refl (A admitted)) ≪≫ shift admitted 1))
noncomputable def rightUnit := Finite.rightUnitCompatibility (carrierSet admitted) (e admitted)
  (identityWitness admitted) (HomotopyEquivalence.ofIso (shift admitted 1 ≪≫ (Iso.refl (A admitted))))

noncomputable def tripleLeft := (triple admitted).left (e admitted) (f admitted) (g admitted)
noncomputable def tripleRight := (triple admitted).right (e admitted) (f admitted) (g admitted)

theorem tripleLeft_point (n : ℤ) : Term.map (tripleLeft admitted).map (point admitted n) = point admitted (n + 6) := by
  change Term.map (shift admitted 3).hom (Term.map (shift admitted 2).hom (Term.map (shift admitted 1).hom (point admitted n))) = _
  rw [shift_point, shift_point, shift_point]
  congr 1
  omega

noncomputable def tripleLeftRecovery :=
  StructuredIdentity.UaComparison.explicitLeftInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 6).fields (tripleLeft admitted).native
noncomputable def tripleConcatPath :=
  Finite.concat (Finite.concat (Coded.path (e admitted)) (Coded.path (f admitted)))
    (Coded.path (g admitted))
noncomputable def tripleConcatPathRecovery :=
  StructuredIdentity.UaComparison.explicitRightInverseAt description admitted.code
    (system admitted 0).fields admitted.code (system admitted 6).fields (tripleConcatPath admitted)

noncomputable def tripleLeftPathRecovery :=
  StructuredIdentity.UaComparison.explicitRightInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 6).fields (Finite.selected (tripleLeft admitted))

theorem tripleRight_point (n : ℤ) : Term.map (tripleRight admitted).map (point admitted n) = point admitted (n + 6) := by
  change Term.map (shift admitted 3).hom (Term.map (shift admitted 2).hom (Term.map (shift admitted 1).hom (point admitted n))) = _
  rw [shift_point, shift_point, shift_point]
  congr 1
  omega

noncomputable def tripleRightRecovery :=
  StructuredIdentity.UaComparison.explicitLeftInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 6).fields (tripleRight admitted).native
noncomputable def tripleRightPathRecovery :=
  StructuredIdentity.UaComparison.explicitRightInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 6).fields (Finite.selected (tripleRight admitted))

noncomputable def vertex0 := (Finite.compose (Finite.compose (Finite.compose (e admitted) (f admitted) (four
  admitted).pair12) (g admitted) (four admitted).triple123L) (h admitted) (four admitted).outer0)
theorem vertex0_point (n : ℤ) : Term.map (vertex0 admitted).map (point admitted n) = point admitted (n + 10) := by
  change Term.map (shift admitted 4).hom (Term.map (shift admitted 3).hom (Term.map (shift admitted 2).hom
    (Term.map (shift admitted 1).hom (point admitted n)))) = _
  rw [shift_point, shift_point, shift_point, shift_point]
  congr 1
  omega
noncomputable def vertex0Recovery :=
  StructuredIdentity.UaComparison.explicitLeftInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 10).fields (vertex0 admitted).native
noncomputable def vertex0PathRecovery :=
  StructuredIdentity.UaComparison.explicitRightInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 10).fields (Finite.selected (vertex0 admitted))

noncomputable def vertex1 := (Finite.compose (Finite.compose (e admitted) (Finite.compose (f admitted) (g
  admitted) (four admitted).pair23) (four admitted).triple123R) (h admitted) (four admitted).outer1)
theorem vertex1_point (n : ℤ) : Term.map (vertex1 admitted).map (point admitted n) = point admitted (n + 10) := by
  change Term.map (shift admitted 4).hom (Term.map (shift admitted 3).hom (Term.map (shift admitted 2).hom
    (Term.map (shift admitted 1).hom (point admitted n)))) = _
  rw [shift_point, shift_point, shift_point, shift_point]
  congr 1
  omega
noncomputable def vertex1Recovery :=
  StructuredIdentity.UaComparison.explicitLeftInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 10).fields (vertex1 admitted).native
noncomputable def vertex1PathRecovery :=
  StructuredIdentity.UaComparison.explicitRightInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 10).fields (Finite.selected (vertex1 admitted))

noncomputable def vertex2 := (Finite.compose (e admitted) (Finite.compose (Finite.compose (f admitted) (g
  admitted) (four admitted).pair23) (h admitted) (four admitted).triple234L) (four admitted).outer2)
theorem vertex2_point (n : ℤ) : Term.map (vertex2 admitted).map (point admitted n) = point admitted (n + 10) := by
  change Term.map (shift admitted 4).hom (Term.map (shift admitted 3).hom (Term.map (shift admitted 2).hom
    (Term.map (shift admitted 1).hom (point admitted n)))) = _
  rw [shift_point, shift_point, shift_point, shift_point]
  congr 1
  omega
noncomputable def vertex2Recovery :=
  StructuredIdentity.UaComparison.explicitLeftInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 10).fields (vertex2 admitted).native
noncomputable def vertex2PathRecovery :=
  StructuredIdentity.UaComparison.explicitRightInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 10).fields (Finite.selected (vertex2 admitted))

noncomputable def vertex3 := (Finite.compose (e admitted) (Finite.compose (f admitted) (Finite.compose (g
  admitted) (h admitted) (four admitted).pair34) (four admitted).triple234R) (four admitted).outer3)
theorem vertex3_point (n : ℤ) : Term.map (vertex3 admitted).map (point admitted n) = point admitted (n + 10) := by
  change Term.map (shift admitted 4).hom (Term.map (shift admitted 3).hom (Term.map (shift admitted 2).hom
    (Term.map (shift admitted 1).hom (point admitted n)))) = _
  rw [shift_point, shift_point, shift_point, shift_point]
  congr 1
  omega
noncomputable def vertex3Recovery :=
  StructuredIdentity.UaComparison.explicitLeftInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 10).fields (vertex3 admitted).native
noncomputable def vertex3PathRecovery :=
  StructuredIdentity.UaComparison.explicitRightInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 10).fields (Finite.selected (vertex3 admitted))

noncomputable def vertex4 := (Finite.compose (Finite.compose (e admitted) (f admitted) (four admitted).pair12)
  (Finite.compose (g admitted) (h admitted) (four admitted).pair34) (four admitted).outer4)
theorem vertex4_point (n : ℤ) : Term.map (vertex4 admitted).map (point admitted n) = point admitted (n + 10) := by
  change Term.map (shift admitted 4).hom (Term.map (shift admitted 3).hom (Term.map (shift admitted 2).hom
    (Term.map (shift admitted 1).hom (point admitted n)))) = _
  rw [shift_point, shift_point, shift_point, shift_point]
  congr 1
  omega
noncomputable def vertex4Recovery :=
  StructuredIdentity.UaComparison.explicitLeftInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 10).fields (vertex4 admitted).native
noncomputable def vertex4PathRecovery :=
  StructuredIdentity.UaComparison.explicitRightInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 10).fields (Finite.selected (vertex4 admitted))
noncomputable def composeWitness {f g : A admitted ⟶ A admitted}
    (E : HomotopyEquivalence f) (D : HomotopyEquivalence g) : HomotopyEquivalence (f ≫ g) :=
  E.comp D (SmallUniverse.NativeDecode.filling admitted.code) (SmallUniverse.NativeDecode.filling_lawful _)
    (SmallUniverse.NativeDecode.filling admitted.code) (SmallUniverse.NativeDecode.filling_lawful _)
    (SmallUniverse.NativeDecode.filling admitted.code) (SmallUniverse.NativeDecode.filling_lawful _)

noncomputable def composedTriple : Finite.TripleWitnesses (e admitted) (f admitted) (g admitted) where
  pairLeft := composeWitness admitted (e admitted).witness (f admitted).witness
  pairRight := composeWitness admitted (f admitted).witness (g admitted).witness
  outerLeft := composeWitness admitted (composeWitness admitted (e admitted).witness (f admitted).witness) (g admitted).witness
  outerRight := composeWitness admitted (e admitted).witness (composeWitness admitted (f admitted).witness (g admitted).witness)

noncomputable def composedFour : Finite.FourWitnesses (e admitted) (f admitted) (g admitted) (h admitted) where
  pair12 := (composeWitness admitted (e admitted).witness (f admitted).witness)
  pair23 := (composeWitness admitted (f admitted).witness (g admitted).witness)
  pair34 := (composeWitness admitted (g admitted).witness (h admitted).witness)
  triple123L := (composeWitness admitted (composeWitness admitted (e admitted).witness (f admitted).witness) (g admitted).witness)
  triple123R := (composeWitness admitted (e admitted).witness (composeWitness admitted (f admitted).witness (g admitted).witness))
  triple234L := (composeWitness admitted (composeWitness admitted (f admitted).witness (g admitted).witness) (h admitted).witness)
  triple234R := (composeWitness admitted (f admitted).witness (composeWitness admitted (g admitted).witness (h admitted).witness))
  outer0 := (composeWitness admitted (composeWitness admitted (composeWitness admitted (e admitted).witness (f
    admitted).witness) (g admitted).witness) (h admitted).witness)
  outer1 := (composeWitness admitted (composeWitness admitted (e admitted).witness (composeWitness admitted (f
    admitted).witness (g admitted).witness)) (h admitted).witness)
  outer2 := (composeWitness admitted (e admitted).witness (composeWitness admitted (composeWitness admitted (f
    admitted).witness (g admitted).witness) (h admitted).witness))
  outer3 := (composeWitness admitted (e admitted).witness (composeWitness admitted (f admitted).witness
    (composeWitness admitted (g admitted).witness (h admitted).witness)))
  outer4 := (composeWitness admitted (composeWitness admitted (e admitted).witness (f admitted).witness)
    (composeWitness admitted (g admitted).witness (h admitted).witness))

noncomputable def composedAssociator :=
  (composedTriple admitted).selectedAssociator (e admitted) (f admitted) (g admitted) (carrierSet admitted)
noncomputable def composedCompatibility :=
  (composedTriple admitted).compatibility (e admitted) (f admitted) (g admitted) (carrierSet admitted) (carrierSet admitted)
noncomputable def composedPentagon :=
  (composedFour admitted).selectedPentagon (e admitted) (f admitted) (g admitted) (h admitted)
    (carrierSet admitted) (carrierSet admitted) (carrierSet admitted)


/-- Triple translation also rejects the original unchanged endpoint. -/
theorem rejects_triple_unchanged (j : Γ.Elements) :
    ¬ Nonempty (Term (homogeneousPath (A admitted)
      (Term.map (tripleLeft admitted).map (point admitted 0)) (point admitted 0))) := by
  rintro ⟨p⟩
  have hp := constantFamily_path_endpoints (homogeneousPathMap admitted.decoding.hom p)
  have h := congrArg (fun t => (t.val j).down) hp
  rw [tripleLeft_point] at h
  change (admitted.decoding.hom.app j ((point admitted 6).val j)).down =
    (admitted.decoding.hom.app j ((point admitted 0).val j)).down at h
  rw [point_decode, point_decode] at h
  norm_num at h

/-- A wrong unchanged endpoint cannot be joined to the translated point. -/
theorem rejects_unchanged (j : Γ.Elements) :
    ¬ Nonempty (Term (homogeneousPath (A admitted)
      (Term.map (vertex0 admitted).map (point admitted 0)) (point admitted 0))) := by
  rintro ⟨p⟩
  have hp := constantFamily_path_endpoints (homogeneousPathMap admitted.decoding.hom p)
  have h := congrArg (fun t => (t.val j).down) hp
  rw [vertex0_point] at h
  change (admitted.decoding.hom.app j ((point admitted 10).val j)).down =
    (admitted.decoding.hom.app j ((point admitted 0).val j)).down at h
  rw [point_decode, point_decode] at h
  norm_num at h
noncomputable def actualAssociator := selectedAssociator (Γ := Γ) (admission ℤ)
noncomputable def actualCompatibility := compatibility (Γ := Γ) (admission ℤ)
noncomputable def actualTriangle := triangle (Γ := Γ) (admission ℤ)
noncomputable def actualPentagon := pentagon (Γ := Γ) (admission ℤ)
noncomputable def actualSelectedPentagon := selectedPentagon (Γ := Γ) (admission ℤ)
noncomputable def actualLeftUnit := leftUnit (Γ := Γ) (admission ℤ)
noncomputable def actualRightUnit := rightUnit (Γ := Γ) (admission ℤ)
noncomputable def actualTripleLeftRecovery := tripleLeftRecovery (Γ := Γ) (admission ℤ)
noncomputable def actualTripleRightRecovery := tripleRightRecovery (Γ := Γ) (admission ℤ)
noncomputable def actualTripleConcatPathRecovery :=
  tripleConcatPathRecovery (Γ := Γ) (admission ℤ)
example (j : Γ.Elements) :
    ¬ Nonempty (Term (homogeneousPath (A (admission ℤ))
      (Term.map (tripleLeft (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 0))
      (point (admission ℤ) 0))) := rejects_triple_unchanged (admission ℤ) j
noncomputable def actualTripleLeftPathRecovery := tripleLeftPathRecovery (Γ := Γ) (admission ℤ)
noncomputable def actualTripleRightPathRecovery := tripleRightPathRecovery (Γ := Γ) (admission ℤ)
noncomputable def actualVertex0Recovery := vertex0Recovery (Γ := Γ) (admission ℤ)
noncomputable def actualVertex0PathRecovery := vertex0PathRecovery (Γ := Γ) (admission ℤ)
noncomputable def actualVertex1Recovery := vertex1Recovery (Γ := Γ) (admission ℤ)
noncomputable def actualVertex1PathRecovery := vertex1PathRecovery (Γ := Γ) (admission ℤ)
noncomputable def actualVertex2Recovery := vertex2Recovery (Γ := Γ) (admission ℤ)
noncomputable def actualVertex2PathRecovery := vertex2PathRecovery (Γ := Γ) (admission ℤ)
noncomputable def actualVertex3Recovery := vertex3Recovery (Γ := Γ) (admission ℤ)
noncomputable def actualVertex3PathRecovery := vertex3PathRecovery (Γ := Γ) (admission ℤ)
noncomputable def actualVertex4Recovery := vertex4Recovery (Γ := Γ) (admission ℤ)
noncomputable def actualVertex4PathRecovery := vertex4PathRecovery (Γ := Γ) (admission ℤ)
example : Term.map (tripleLeft (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 0) = point (admission ℤ) 6 := tripleLeft_point _ 0
example : Term.map (tripleLeft (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 1) = point (admission ℤ) 7 := tripleLeft_point _ 1
example : Term.map (tripleRight (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 0) = point (admission ℤ) 6 := tripleRight_point _ 0
example : Term.map (tripleRight (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 1) = point (admission ℤ) 7 := tripleRight_point _ 1
example : Term.map (vertex0 (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 0) = point (admission ℤ) 10 := vertex0_point _ 0
example : Term.map (vertex0 (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 1) = point (admission ℤ) 11 := vertex0_point _ 1
example : Term.map (vertex1 (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 0) = point (admission ℤ) 10 := vertex1_point _ 0
example : Term.map (vertex1 (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 1) = point (admission ℤ) 11 := vertex1_point _ 1
example : Term.map (vertex2 (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 0) = point (admission ℤ) 10 := vertex2_point _ 0
example : Term.map (vertex2 (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 1) = point (admission ℤ) 11 := vertex2_point _ 1
example : Term.map (vertex3 (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 0) = point (admission ℤ) 10 := vertex3_point _ 0
example : Term.map (vertex3 (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 1) = point (admission ℤ) 11 := vertex3_point _ 1
example : Term.map (vertex4 (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 0) = point (admission ℤ) 10 := vertex4_point _ 0
example : Term.map (vertex4 (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 1) = point (admission ℤ) 11 := vertex4_point _ 1
noncomputable def actualComposedAssociator := composedAssociator (Γ := Γ) (admission ℤ)
noncomputable def actualComposedCompatibility := composedCompatibility (Γ := Γ) (admission ℤ)
noncomputable def actualComposedPentagon := composedPentagon (Γ := Γ) (admission ℤ)
example (j : Γ.Elements) := rejects_unchanged (Γ := Γ) (admission ℤ) j
noncomputable abbrev intervalProjection : total (interval Γ) ⟶ Γ := projection (interval Γ)

noncomputable def freshLeft
    (F : { F : Filling (SmallUniverse.liftedDecode (intervalProjection ≫ admitted.code)) // F.Lawful }) :=
  (((e admitted).reindex intervalProjection).compWith ((f admitted).reindex intervalProjection)
    ((triple admitted).pairLeft.reindex intervalProjection) F.1 F.2 F.1 F.2).compWith
    ((g admitted).reindex intervalProjection) ((triple admitted).outerLeft.reindex intervalProjection)
    F.1 F.2 F.1 F.2

noncomputable def freshRight
    (F : { F : Filling (SmallUniverse.liftedDecode (intervalProjection ≫ admitted.code)) // F.Lawful }) :=
  ((e admitted).reindex intervalProjection).compWith
    (((f admitted).reindex intervalProjection).compWith ((g admitted).reindex intervalProjection)
      ((triple admitted).pairRight.reindex intervalProjection) F.1 F.2 F.1 F.2)
    ((triple admitted).outerRight.reindex intervalProjection) F.1 F.2 F.1 F.2

noncomputable def freshAssociatorComparison
    (F : { F : Filling (SmallUniverse.liftedDecode (intervalProjection ≫ admitted.code)) // F.Lawful }) :=
  Examples.NativeLatticeTransport.Presheaf.PathData.ofPath (
  (triple admitted).freshAssociatorReindex (e admitted) (f admitted) (g admitted)
    (carrierSet admitted) intervalProjection (freshLeft admitted F) (freshRight admitted F) rfl rfl
)

noncomputable def reindexedTriple :=
  (triple admitted).reindex (e admitted) (f admitted) (g admitted) intervalProjection

noncomputable def freshBinaryRoute :=
  (reindexedTriple admitted).binaryAssociator
    (a := intervalProjection ≫ admitted.code) (b := intervalProjection ≫ admitted.code)
    (c := intervalProjection ≫ admitted.code) (d := intervalProjection ≫ admitted.code)
    ((e admitted).reindex intervalProjection) ((f admitted).reindex intervalProjection)
    ((g admitted).reindex intervalProjection)
    (HomotopyLevels.reindexSet (carrierSet admitted) intervalProjection)
    (HomotopyLevels.reindexSet (carrierSet admitted) intervalProjection)

noncomputable def freshBinaryComparison :=
  Examples.NativeLatticeTransport.Presheaf.PathData.ofPath (
  (triple admitted).freshBinaryAssociatorReindex (a := admitted.code) (b := admitted.code) (c :=
    admitted.code) (d := admitted.code) (e admitted) (f admitted) (g admitted)
    (carrierSet admitted) (carrierSet admitted) intervalProjection
    ((reindexedTriple admitted).left (a := intervalProjection ≫ admitted.code) (b := intervalProjection ≫
      admitted.code) (c := intervalProjection ≫ admitted.code) (d := intervalProjection ≫ admitted.code) ((e
      admitted).reindex intervalProjection)
      ((f admitted).reindex intervalProjection) ((g admitted).reindex intervalProjection))
    ((reindexedTriple admitted).right (a := intervalProjection ≫ admitted.code) (b := intervalProjection ≫
      admitted.code) (c := intervalProjection ≫ admitted.code) (d := intervalProjection ≫ admitted.code) ((e
      admitted).reindex intervalProjection)
      ((f admitted).reindex intervalProjection) ((g admitted).reindex intervalProjection))
    rfl rfl (freshBinaryRoute admitted)
)

noncomputable def actualFreshAssociatorComparison := freshAssociatorComparison (Γ := Γ) (admission ℤ)
  ⟨SmallUniverse.NativeDecode.filling (intervalProjection ≫ (admission ℤ).code),
    SmallUniverse.NativeDecode.filling_lawful _⟩
noncomputable def actualFreshBinaryComparison := freshBinaryComparison (Γ := Γ) (admission ℤ)

variable (F : { F : Filling (SmallUniverse.liftedDecode (intervalProjection ≫ admitted.code)) // F.Lawful })

noncomputable def freshLeftAdjustment :
    Finite.Cell (Finite.selected (a := intervalProjection ≫ admitted.code) (b := intervalProjection ≫
      admitted.code) (freshLeft admitted F)) (Finite.selected (a := intervalProjection ≫ admitted.code) (b :=
      intervalProjection ≫ admitted.code) ((reindexedTriple admitted).left
      (a := intervalProjection ≫ admitted.code) (b := intervalProjection ≫ admitted.code)
      (c := intervalProjection ≫ admitted.code) (d := intervalProjection ≫ admitted.code)
      ((e admitted).reindex intervalProjection) ((f admitted).reindex intervalProjection)
      ((g admitted).reindex intervalProjection))) :=
  Finite.compareSelectedMaps (a := intervalProjection ≫ admitted.code) (b := intervalProjection ≫ admitted.code)
    (HomotopyLevels.reindexSet (carrierSet admitted) intervalProjection)
    (freshLeft admitted F)
    ((reindexedTriple admitted).left (a := intervalProjection ≫ admitted.code) (b := intervalProjection ≫ admitted.code)
      (c := intervalProjection ≫ admitted.code) (d := intervalProjection ≫ admitted.code)
      ((e admitted).reindex intervalProjection) ((f admitted).reindex intervalProjection)
      ((g admitted).reindex intervalProjection))
    (by dsimp only [freshLeft, freshRight, reindexedTriple, Finite.TripleWitnesses.left,
      Finite.TripleWitnesses.right, Finite.TripleWitnesses.reindex, Equivalence.compWith]; rfl)

noncomputable def freshRightAdjustment :
    Finite.Cell (Finite.selected (a := intervalProjection ≫ admitted.code) (b := intervalProjection ≫
      admitted.code) (freshRight admitted F)) (Finite.selected (a := intervalProjection ≫ admitted.code) (b :=
      intervalProjection ≫ admitted.code) ((reindexedTriple admitted).right
      (a := intervalProjection ≫ admitted.code) (b := intervalProjection ≫ admitted.code)
      (c := intervalProjection ≫ admitted.code) (d := intervalProjection ≫ admitted.code)
      ((e admitted).reindex intervalProjection) ((f admitted).reindex intervalProjection)
      ((g admitted).reindex intervalProjection))) :=
  Finite.compareSelectedMaps (a := intervalProjection ≫ admitted.code) (b := intervalProjection ≫ admitted.code)
    (HomotopyLevels.reindexSet (carrierSet admitted) intervalProjection)
    (freshRight admitted F)
    ((reindexedTriple admitted).right (a := intervalProjection ≫ admitted.code) (b := intervalProjection ≫ admitted.code)
      (c := intervalProjection ≫ admitted.code) (d := intervalProjection ≫ admitted.code)
      ((e admitted).reindex intervalProjection) ((f admitted).reindex intervalProjection)
      ((g admitted).reindex intervalProjection))
    (by dsimp only [freshLeft, freshRight, reindexedTriple, Finite.TripleWitnesses.left,
      Finite.TripleWitnesses.right, Finite.TripleWitnesses.reindex, Equivalence.compWith]; rfl)

noncomputable def arbitraryFreshBinaryRoute :
    Finite.Cell (Finite.selected (a := intervalProjection ≫ admitted.code) (b := intervalProjection ≫
      admitted.code) (freshLeft admitted F)) (Finite.selected (a := intervalProjection ≫ admitted.code) (b :=
      intervalProjection ≫ admitted.code) (freshRight admitted F)) :=
  Finite.vertical (Finite.vertical (freshLeftAdjustment admitted F) (freshBinaryRoute admitted))
    (Finite.reverse (freshRightAdjustment admitted F))

noncomputable def arbitraryFreshBinaryComparison :=
  Examples.NativeLatticeTransport.Presheaf.PathData.ofPath (
    (triple admitted).freshBinaryAssociatorReindex
      (a := admitted.code) (b := admitted.code) (c := admitted.code) (d := admitted.code)
      (e admitted) (f admitted) (g admitted) (carrierSet admitted) (carrierSet admitted)
      intervalProjection (freshLeft admitted F) (freshRight admitted F) rfl rfl
      (arbitraryFreshBinaryRoute admitted F))

noncomputable def actualArbitraryFreshBinaryComparison :=
  arbitraryFreshBinaryComparison (Γ := Γ) (admission ℤ)
    ⟨SmallUniverse.NativeDecode.filling (intervalProjection ≫ (admission ℤ).code),
      SmallUniverse.NativeDecode.filling_lawful _⟩
end Examples.NativeFiniteCoherence.Presheaf

namespace Examples.NativeFiniteCoherence.Cartesian
open CategoryTheory SquareKit.Cubical.Cartesian StructureIdentity.Coherence
open Examples.NativeStructureCoherence.Cartesian
open Examples.NativeLatticeTransport.Cartesian (admission carrierSet)
variable {Γ : Context.{1}}
variable (admitted : SmallUniverse.LargeConstructors.Result (constantFamily Γ (ULift.{1} ℤ)))

noncomputable def isoWitness (E : A admitted ≅ A admitted) :=
  HomotopyEquivalence.ofIso E (SmallUniverse.NativeDecode.filling admitted.code)
    (SmallUniverse.NativeDecode.filling_lawful admitted.code)

noncomputable def e := move admitted 0 1
noncomputable def f := move admitted 1 2
noncomputable def g := move admitted 3 3
noncomputable def h := move admitted 6 4

noncomputable def triple : Finite.TripleWitnesses (e admitted) (f admitted) (g admitted) where
  pairLeft := isoWitness admitted ((shift admitted 1) ≪≫ (shift admitted 2))
  pairRight := isoWitness admitted ((shift admitted 2) ≪≫ (shift admitted 3))
  outerLeft := isoWitness admitted (((shift admitted 1) ≪≫ (shift admitted 2)) ≪≫ (shift admitted 3))
  outerRight := isoWitness admitted ((shift admitted 1) ≪≫ ((shift admitted 2) ≪≫ (shift admitted 3)))

noncomputable def selectedAssociator :=
  (triple admitted).selectedAssociator (e admitted) (f admitted) (g admitted) (carrierSet admitted)
noncomputable def compatibility :=
  (triple admitted).compatibility (e admitted) (f admitted) (g admitted) (carrierSet admitted) (carrierSet admitted)
noncomputable def triangle := Finite.triangle (carrierSet admitted) (carrierSet admitted)
  (Coded.path (e admitted)) (Coded.path (f admitted))
noncomputable def pentagon := Finite.pentagon (carrierSet admitted) (carrierSet admitted)
  (Coded.path (e admitted)) (Coded.path (f admitted))
  (Coded.path (g admitted)) (Coded.path (h admitted))

noncomputable def four : Finite.FourWitnesses (e admitted) (f admitted) (g admitted) (h admitted) where
  pair12 := isoWitness admitted ((shift admitted 1) ≪≫ (shift admitted 2))
  pair23 := isoWitness admitted ((shift admitted 2) ≪≫ (shift admitted 3))
  pair34 := isoWitness admitted ((shift admitted 3) ≪≫ (shift admitted 4))
  triple123L := isoWitness admitted (((shift admitted 1) ≪≫ (shift admitted 2)) ≪≫ (shift admitted 3))
  triple123R := isoWitness admitted ((shift admitted 1) ≪≫ ((shift admitted 2) ≪≫ (shift admitted 3)))
  triple234L := isoWitness admitted (((shift admitted 2) ≪≫ (shift admitted 3)) ≪≫ (shift admitted 4))
  triple234R := isoWitness admitted ((shift admitted 2) ≪≫ ((shift admitted 3) ≪≫ (shift admitted 4)))
  outer0 := isoWitness admitted ((((shift admitted 1) ≪≫ (shift admitted 2)) ≪≫ (shift admitted 3)) ≪≫ (shift admitted 4))
  outer1 := isoWitness admitted (((shift admitted 1) ≪≫ ((shift admitted 2) ≪≫ (shift admitted 3))) ≪≫ (shift admitted 4))
  outer2 := isoWitness admitted ((shift admitted 1) ≪≫ (((shift admitted 2) ≪≫ (shift admitted 3)) ≪≫ (shift admitted 4)))
  outer3 := isoWitness admitted ((shift admitted 1) ≪≫ ((shift admitted 2) ≪≫ ((shift admitted 3) ≪≫ (shift admitted 4))))
  outer4 := isoWitness admitted (((shift admitted 1) ≪≫ (shift admitted 2)) ≪≫ ((shift admitted 3) ≪≫ (shift admitted 4)))

noncomputable def selectedPentagon :=
  (four admitted).selectedPentagon (e admitted) (f admitted) (g admitted) (h admitted)
    (carrierSet admitted) (carrierSet admitted) (carrierSet admitted)
noncomputable def identityWitness := isoWitness admitted (Iso.refl (A admitted))
noncomputable def leftUnit := Finite.leftUnitCompatibility (carrierSet admitted) (carrierSet admitted) (e admitted)
  (identityWitness admitted) (isoWitness admitted ((Iso.refl (A admitted)) ≪≫ shift admitted 1))
noncomputable def rightUnit := Finite.rightUnitCompatibility (carrierSet admitted) (e admitted)
  (identityWitness admitted) (isoWitness admitted (shift admitted 1 ≪≫ (Iso.refl (A admitted))))

noncomputable def tripleLeft := (triple admitted).left (e admitted) (f admitted) (g admitted)
noncomputable def tripleRight := (triple admitted).right (e admitted) (f admitted) (g admitted)

theorem tripleLeft_point (n : ℤ) : Term.map (tripleLeft admitted).map (point admitted n) = point admitted (n + 6) := by
  change Term.map (shift admitted 3).hom (Term.map (shift admitted 2).hom (Term.map (shift admitted 1).hom (point admitted n))) = _
  rw [shift_point, shift_point, shift_point]
  congr 1
  omega

noncomputable def tripleLeftRecovery :=
  StructuredIdentity.UaComparison.explicitLeftInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 6).fields (tripleLeft admitted).native
noncomputable def tripleConcatPath :=
  Finite.concat (Finite.concat (Coded.path (e admitted)) (Coded.path (f admitted)))
    (Coded.path (g admitted))
noncomputable def tripleConcatPathRecovery :=
  StructuredIdentity.UaComparison.explicitRightInverseAt description admitted.code
    (system admitted 0).fields admitted.code (system admitted 6).fields (tripleConcatPath admitted)

noncomputable def tripleLeftPathRecovery :=
  StructuredIdentity.UaComparison.explicitRightInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 6).fields (Finite.selected (tripleLeft admitted))

theorem tripleRight_point (n : ℤ) : Term.map (tripleRight admitted).map (point admitted n) = point admitted (n + 6) := by
  change Term.map (shift admitted 3).hom (Term.map (shift admitted 2).hom (Term.map (shift admitted 1).hom (point admitted n))) = _
  rw [shift_point, shift_point, shift_point]
  congr 1
  omega

noncomputable def tripleRightRecovery :=
  StructuredIdentity.UaComparison.explicitLeftInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 6).fields (tripleRight admitted).native
noncomputable def tripleRightPathRecovery :=
  StructuredIdentity.UaComparison.explicitRightInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 6).fields (Finite.selected (tripleRight admitted))

noncomputable def vertex0 := (Finite.compose (Finite.compose (Finite.compose (e admitted) (f admitted) (four
  admitted).pair12) (g admitted) (four admitted).triple123L) (h admitted) (four admitted).outer0)
theorem vertex0_point (n : ℤ) : Term.map (vertex0 admitted).map (point admitted n) = point admitted (n + 10) := by
  change Term.map (shift admitted 4).hom (Term.map (shift admitted 3).hom (Term.map (shift admitted 2).hom
    (Term.map (shift admitted 1).hom (point admitted n)))) = _
  rw [shift_point, shift_point, shift_point, shift_point]
  congr 1
  omega
noncomputable def vertex0Recovery :=
  StructuredIdentity.UaComparison.explicitLeftInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 10).fields (vertex0 admitted).native
noncomputable def vertex0PathRecovery :=
  StructuredIdentity.UaComparison.explicitRightInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 10).fields (Finite.selected (vertex0 admitted))

noncomputable def vertex1 := (Finite.compose (Finite.compose (e admitted) (Finite.compose (f admitted) (g
  admitted) (four admitted).pair23) (four admitted).triple123R) (h admitted) (four admitted).outer1)
theorem vertex1_point (n : ℤ) : Term.map (vertex1 admitted).map (point admitted n) = point admitted (n + 10) := by
  change Term.map (shift admitted 4).hom (Term.map (shift admitted 3).hom (Term.map (shift admitted 2).hom
    (Term.map (shift admitted 1).hom (point admitted n)))) = _
  rw [shift_point, shift_point, shift_point, shift_point]
  congr 1
  omega
noncomputable def vertex1Recovery :=
  StructuredIdentity.UaComparison.explicitLeftInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 10).fields (vertex1 admitted).native
noncomputable def vertex1PathRecovery :=
  StructuredIdentity.UaComparison.explicitRightInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 10).fields (Finite.selected (vertex1 admitted))

noncomputable def vertex2 := (Finite.compose (e admitted) (Finite.compose (Finite.compose (f admitted) (g
  admitted) (four admitted).pair23) (h admitted) (four admitted).triple234L) (four admitted).outer2)
theorem vertex2_point (n : ℤ) : Term.map (vertex2 admitted).map (point admitted n) = point admitted (n + 10) := by
  change Term.map (shift admitted 4).hom (Term.map (shift admitted 3).hom (Term.map (shift admitted 2).hom
    (Term.map (shift admitted 1).hom (point admitted n)))) = _
  rw [shift_point, shift_point, shift_point, shift_point]
  congr 1
  omega
noncomputable def vertex2Recovery :=
  StructuredIdentity.UaComparison.explicitLeftInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 10).fields (vertex2 admitted).native
noncomputable def vertex2PathRecovery :=
  StructuredIdentity.UaComparison.explicitRightInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 10).fields (Finite.selected (vertex2 admitted))

noncomputable def vertex3 := (Finite.compose (e admitted) (Finite.compose (f admitted) (Finite.compose (g
  admitted) (h admitted) (four admitted).pair34) (four admitted).triple234R) (four admitted).outer3)
theorem vertex3_point (n : ℤ) : Term.map (vertex3 admitted).map (point admitted n) = point admitted (n + 10) := by
  change Term.map (shift admitted 4).hom (Term.map (shift admitted 3).hom (Term.map (shift admitted 2).hom
    (Term.map (shift admitted 1).hom (point admitted n)))) = _
  rw [shift_point, shift_point, shift_point, shift_point]
  congr 1
  omega
noncomputable def vertex3Recovery :=
  StructuredIdentity.UaComparison.explicitLeftInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 10).fields (vertex3 admitted).native
noncomputable def vertex3PathRecovery :=
  StructuredIdentity.UaComparison.explicitRightInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 10).fields (Finite.selected (vertex3 admitted))

noncomputable def vertex4 := (Finite.compose (Finite.compose (e admitted) (f admitted) (four admitted).pair12)
  (Finite.compose (g admitted) (h admitted) (four admitted).pair34) (four admitted).outer4)
theorem vertex4_point (n : ℤ) : Term.map (vertex4 admitted).map (point admitted n) = point admitted (n + 10) := by
  change Term.map (shift admitted 4).hom (Term.map (shift admitted 3).hom (Term.map (shift admitted 2).hom
    (Term.map (shift admitted 1).hom (point admitted n)))) = _
  rw [shift_point, shift_point, shift_point, shift_point]
  congr 1
  omega
noncomputable def vertex4Recovery :=
  StructuredIdentity.UaComparison.explicitLeftInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 10).fields (vertex4 admitted).native
noncomputable def vertex4PathRecovery :=
  StructuredIdentity.UaComparison.explicitRightInverseAt description admitted.code (system admitted 0).fields
    admitted.code (system admitted 10).fields (Finite.selected (vertex4 admitted))
noncomputable def composeWitness {f g : A admitted ⟶ A admitted}
    (E : HomotopyEquivalence f) (D : HomotopyEquivalence g) : HomotopyEquivalence (f ≫ g) :=
  E.comp D (SmallUniverse.NativeDecode.filling admitted.code) (SmallUniverse.NativeDecode.filling_lawful _)
    (SmallUniverse.NativeDecode.filling admitted.code) (SmallUniverse.NativeDecode.filling_lawful _)
    (SmallUniverse.NativeDecode.filling admitted.code) (SmallUniverse.NativeDecode.filling_lawful _)

noncomputable def composedTriple : Finite.TripleWitnesses (e admitted) (f admitted) (g admitted) where
  pairLeft := composeWitness admitted (e admitted).witness (f admitted).witness
  pairRight := composeWitness admitted (f admitted).witness (g admitted).witness
  outerLeft := composeWitness admitted (composeWitness admitted (e admitted).witness (f admitted).witness) (g admitted).witness
  outerRight := composeWitness admitted (e admitted).witness (composeWitness admitted (f admitted).witness (g admitted).witness)

noncomputable def composedFour : Finite.FourWitnesses (e admitted) (f admitted) (g admitted) (h admitted) where
  pair12 := (composeWitness admitted (e admitted).witness (f admitted).witness)
  pair23 := (composeWitness admitted (f admitted).witness (g admitted).witness)
  pair34 := (composeWitness admitted (g admitted).witness (h admitted).witness)
  triple123L := (composeWitness admitted (composeWitness admitted (e admitted).witness (f admitted).witness) (g admitted).witness)
  triple123R := (composeWitness admitted (e admitted).witness (composeWitness admitted (f admitted).witness (g admitted).witness))
  triple234L := (composeWitness admitted (composeWitness admitted (f admitted).witness (g admitted).witness) (h admitted).witness)
  triple234R := (composeWitness admitted (f admitted).witness (composeWitness admitted (g admitted).witness (h admitted).witness))
  outer0 := (composeWitness admitted (composeWitness admitted (composeWitness admitted (e admitted).witness (f
    admitted).witness) (g admitted).witness) (h admitted).witness)
  outer1 := (composeWitness admitted (composeWitness admitted (e admitted).witness (composeWitness admitted (f
    admitted).witness (g admitted).witness)) (h admitted).witness)
  outer2 := (composeWitness admitted (e admitted).witness (composeWitness admitted (composeWitness admitted (f
    admitted).witness (g admitted).witness) (h admitted).witness))
  outer3 := (composeWitness admitted (e admitted).witness (composeWitness admitted (f admitted).witness
    (composeWitness admitted (g admitted).witness (h admitted).witness)))
  outer4 := (composeWitness admitted (composeWitness admitted (e admitted).witness (f admitted).witness)
    (composeWitness admitted (g admitted).witness (h admitted).witness))

noncomputable def composedAssociator :=
  (composedTriple admitted).selectedAssociator (e admitted) (f admitted) (g admitted) (carrierSet admitted)
noncomputable def composedCompatibility :=
  (composedTriple admitted).compatibility (e admitted) (f admitted) (g admitted) (carrierSet admitted) (carrierSet admitted)
noncomputable def composedPentagon :=
  (composedFour admitted).selectedPentagon (e admitted) (f admitted) (g admitted) (h admitted)
    (carrierSet admitted) (carrierSet admitted) (carrierSet admitted)


/-- Triple translation also rejects the original unchanged endpoint. -/
theorem rejects_triple_unchanged (j : Γ.Elements) :
    ¬ Nonempty (Term (homogeneousPath (A admitted)
      (Term.map (tripleLeft admitted).map (point admitted 0)) (point admitted 0))) := by
  rintro ⟨p⟩
  have h := (StructureIdentity.Native.presentedPathEquiv admitted.decoding _ _ j (p.val j)).down.down
  rw [tripleLeft_point] at h
  change (admitted.decoding.hom.app j ((point admitted 6).val j)).down =
    (admitted.decoding.hom.app j ((point admitted 0).val j)).down at h
  rw [point_decode, point_decode] at h
  norm_num at h

/-- A wrong unchanged endpoint cannot be joined to the translated point. -/
theorem rejects_unchanged (j : Γ.Elements) :
    ¬ Nonempty (Term (homogeneousPath (A admitted)
      (Term.map (vertex0 admitted).map (point admitted 0)) (point admitted 0))) := by
  rintro ⟨p⟩
  have h := (StructureIdentity.Native.presentedPathEquiv admitted.decoding _ _ j (p.val j)).down.down
  rw [vertex0_point] at h
  change (admitted.decoding.hom.app j ((point admitted 10).val j)).down =
    (admitted.decoding.hom.app j ((point admitted 0).val j)).down at h
  rw [point_decode, point_decode] at h
  norm_num at h
noncomputable def actualAssociator := selectedAssociator (Γ := Γ) (admission ℤ)
noncomputable def actualCompatibility := compatibility (Γ := Γ) (admission ℤ)
noncomputable def actualTriangle := triangle (Γ := Γ) (admission ℤ)
noncomputable def actualPentagon := pentagon (Γ := Γ) (admission ℤ)
noncomputable def actualSelectedPentagon := selectedPentagon (Γ := Γ) (admission ℤ)
noncomputable def actualLeftUnit := leftUnit (Γ := Γ) (admission ℤ)
noncomputable def actualRightUnit := rightUnit (Γ := Γ) (admission ℤ)
noncomputable def actualTripleLeftRecovery := tripleLeftRecovery (Γ := Γ) (admission ℤ)
noncomputable def actualTripleRightRecovery := tripleRightRecovery (Γ := Γ) (admission ℤ)
noncomputable def actualTripleConcatPathRecovery :=
  tripleConcatPathRecovery (Γ := Γ) (admission ℤ)
example (j : Γ.Elements) :
    ¬ Nonempty (Term (homogeneousPath (A (admission ℤ))
      (Term.map (tripleLeft (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 0))
      (point (admission ℤ) 0))) := rejects_triple_unchanged (admission ℤ) j
noncomputable def actualTripleLeftPathRecovery := tripleLeftPathRecovery (Γ := Γ) (admission ℤ)
noncomputable def actualTripleRightPathRecovery := tripleRightPathRecovery (Γ := Γ) (admission ℤ)
noncomputable def actualVertex0Recovery := vertex0Recovery (Γ := Γ) (admission ℤ)
noncomputable def actualVertex0PathRecovery := vertex0PathRecovery (Γ := Γ) (admission ℤ)
noncomputable def actualVertex1Recovery := vertex1Recovery (Γ := Γ) (admission ℤ)
noncomputable def actualVertex1PathRecovery := vertex1PathRecovery (Γ := Γ) (admission ℤ)
noncomputable def actualVertex2Recovery := vertex2Recovery (Γ := Γ) (admission ℤ)
noncomputable def actualVertex2PathRecovery := vertex2PathRecovery (Γ := Γ) (admission ℤ)
noncomputable def actualVertex3Recovery := vertex3Recovery (Γ := Γ) (admission ℤ)
noncomputable def actualVertex3PathRecovery := vertex3PathRecovery (Γ := Γ) (admission ℤ)
noncomputable def actualVertex4Recovery := vertex4Recovery (Γ := Γ) (admission ℤ)
noncomputable def actualVertex4PathRecovery := vertex4PathRecovery (Γ := Γ) (admission ℤ)
example : Term.map (tripleLeft (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 0) = point (admission ℤ) 6 := tripleLeft_point _ 0
example : Term.map (tripleLeft (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 1) = point (admission ℤ) 7 := tripleLeft_point _ 1
example : Term.map (tripleRight (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 0) = point (admission ℤ) 6 := tripleRight_point _ 0
example : Term.map (tripleRight (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 1) = point (admission ℤ) 7 := tripleRight_point _ 1
example : Term.map (vertex0 (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 0) = point (admission ℤ) 10 := vertex0_point _ 0
example : Term.map (vertex0 (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 1) = point (admission ℤ) 11 := vertex0_point _ 1
example : Term.map (vertex1 (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 0) = point (admission ℤ) 10 := vertex1_point _ 0
example : Term.map (vertex1 (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 1) = point (admission ℤ) 11 := vertex1_point _ 1
example : Term.map (vertex2 (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 0) = point (admission ℤ) 10 := vertex2_point _ 0
example : Term.map (vertex2 (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 1) = point (admission ℤ) 11 := vertex2_point _ 1
example : Term.map (vertex3 (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 0) = point (admission ℤ) 10 := vertex3_point _ 0
example : Term.map (vertex3 (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 1) = point (admission ℤ) 11 := vertex3_point _ 1
example : Term.map (vertex4 (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 0) = point (admission ℤ) 10 := vertex4_point _ 0
example : Term.map (vertex4 (Γ := Γ) (admission ℤ)).map (point (admission ℤ) 1) = point (admission ℤ) 11 := vertex4_point _ 1
noncomputable def actualComposedAssociator := composedAssociator (Γ := Γ) (admission ℤ)
noncomputable def actualComposedCompatibility := composedCompatibility (Γ := Γ) (admission ℤ)
noncomputable def actualComposedPentagon := composedPentagon (Γ := Γ) (admission ℤ)
example (j : Γ.Elements) := rejects_unchanged (Γ := Γ) (admission ℤ) j
noncomputable abbrev intervalProjection : total (interval Γ) ⟶ Γ := projection (interval Γ)

noncomputable def freshLeft
    (F : { F : Filling (SmallUniverse.liftedDecode (intervalProjection ≫ admitted.code)) // F.Lawful }) :=
  (((e admitted).reindex intervalProjection).compWith ((f admitted).reindex intervalProjection)
    ((triple admitted).pairLeft.reindex intervalProjection) F.1 F.2 F.1 F.2).compWith
    ((g admitted).reindex intervalProjection) ((triple admitted).outerLeft.reindex intervalProjection)
    F.1 F.2 F.1 F.2

noncomputable def freshRight
    (F : { F : Filling (SmallUniverse.liftedDecode (intervalProjection ≫ admitted.code)) // F.Lawful }) :=
  ((e admitted).reindex intervalProjection).compWith
    (((f admitted).reindex intervalProjection).compWith ((g admitted).reindex intervalProjection)
      ((triple admitted).pairRight.reindex intervalProjection) F.1 F.2 F.1 F.2)
    ((triple admitted).outerRight.reindex intervalProjection) F.1 F.2 F.1 F.2

noncomputable def freshAssociatorComparison
    (F : { F : Filling (SmallUniverse.liftedDecode (intervalProjection ≫ admitted.code)) // F.Lawful }) :=
  Examples.NativeLatticeTransport.Cartesian.PathData.ofPath (
  (triple admitted).freshAssociatorReindex (e admitted) (f admitted) (g admitted)
    (carrierSet admitted) intervalProjection (freshLeft admitted F) (freshRight admitted F) rfl rfl
)

noncomputable def reindexedTriple :=
  (triple admitted).reindex (e admitted) (f admitted) (g admitted) intervalProjection

noncomputable def freshBinaryRoute :=
  (reindexedTriple admitted).binaryAssociator
    (a := intervalProjection ≫ admitted.code) (b := intervalProjection ≫ admitted.code)
    (c := intervalProjection ≫ admitted.code) (d := intervalProjection ≫ admitted.code)
    ((e admitted).reindex intervalProjection) ((f admitted).reindex intervalProjection)
    ((g admitted).reindex intervalProjection)
    (HomotopyLevels.reindexSet (carrierSet admitted) intervalProjection)
    (HomotopyLevels.reindexSet (carrierSet admitted) intervalProjection)

noncomputable def freshBinaryComparison :=
  Examples.NativeLatticeTransport.Cartesian.PathData.ofPath (
  (triple admitted).freshBinaryAssociatorReindex (a := admitted.code) (b := admitted.code) (c :=
    admitted.code) (d := admitted.code) (e admitted) (f admitted) (g admitted)
    (carrierSet admitted) (carrierSet admitted) intervalProjection
    ((reindexedTriple admitted).left (a := intervalProjection ≫ admitted.code) (b := intervalProjection ≫
      admitted.code) (c := intervalProjection ≫ admitted.code) (d := intervalProjection ≫ admitted.code) ((e
      admitted).reindex intervalProjection)
      ((f admitted).reindex intervalProjection) ((g admitted).reindex intervalProjection))
    ((reindexedTriple admitted).right (a := intervalProjection ≫ admitted.code) (b := intervalProjection ≫
      admitted.code) (c := intervalProjection ≫ admitted.code) (d := intervalProjection ≫ admitted.code) ((e
      admitted).reindex intervalProjection)
      ((f admitted).reindex intervalProjection) ((g admitted).reindex intervalProjection))
    rfl rfl (freshBinaryRoute admitted)
)

noncomputable def actualFreshAssociatorComparison := freshAssociatorComparison (Γ := Γ) (admission ℤ)
  ⟨SmallUniverse.NativeDecode.filling (intervalProjection ≫ (admission ℤ).code),
    SmallUniverse.NativeDecode.filling_lawful _⟩
noncomputable def actualFreshBinaryComparison := freshBinaryComparison (Γ := Γ) (admission ℤ)

variable (F : { F : Filling (SmallUniverse.liftedDecode (intervalProjection ≫ admitted.code)) // F.Lawful })

noncomputable def freshLeftAdjustment :
    Finite.Cell (Finite.selected (a := intervalProjection ≫ admitted.code) (b := intervalProjection ≫
      admitted.code) (freshLeft admitted F)) (Finite.selected (a := intervalProjection ≫ admitted.code) (b :=
      intervalProjection ≫ admitted.code) ((reindexedTriple admitted).left
      (a := intervalProjection ≫ admitted.code) (b := intervalProjection ≫ admitted.code)
      (c := intervalProjection ≫ admitted.code) (d := intervalProjection ≫ admitted.code)
      ((e admitted).reindex intervalProjection) ((f admitted).reindex intervalProjection)
      ((g admitted).reindex intervalProjection))) :=
  Finite.compareSelectedMaps (a := intervalProjection ≫ admitted.code) (b := intervalProjection ≫ admitted.code)
    (HomotopyLevels.reindexSet (carrierSet admitted) intervalProjection)
    (freshLeft admitted F)
    ((reindexedTriple admitted).left (a := intervalProjection ≫ admitted.code) (b := intervalProjection ≫ admitted.code)
      (c := intervalProjection ≫ admitted.code) (d := intervalProjection ≫ admitted.code)
      ((e admitted).reindex intervalProjection) ((f admitted).reindex intervalProjection)
      ((g admitted).reindex intervalProjection))
    (by dsimp only [freshLeft, freshRight, reindexedTriple, Finite.TripleWitnesses.left,
      Finite.TripleWitnesses.right, Finite.TripleWitnesses.reindex, Equivalence.compWith]; rfl)

noncomputable def freshRightAdjustment :
    Finite.Cell (Finite.selected (a := intervalProjection ≫ admitted.code) (b := intervalProjection ≫
      admitted.code) (freshRight admitted F)) (Finite.selected (a := intervalProjection ≫ admitted.code) (b :=
      intervalProjection ≫ admitted.code) ((reindexedTriple admitted).right
      (a := intervalProjection ≫ admitted.code) (b := intervalProjection ≫ admitted.code)
      (c := intervalProjection ≫ admitted.code) (d := intervalProjection ≫ admitted.code)
      ((e admitted).reindex intervalProjection) ((f admitted).reindex intervalProjection)
      ((g admitted).reindex intervalProjection))) :=
  Finite.compareSelectedMaps (a := intervalProjection ≫ admitted.code) (b := intervalProjection ≫ admitted.code)
    (HomotopyLevels.reindexSet (carrierSet admitted) intervalProjection)
    (freshRight admitted F)
    ((reindexedTriple admitted).right (a := intervalProjection ≫ admitted.code) (b := intervalProjection ≫ admitted.code)
      (c := intervalProjection ≫ admitted.code) (d := intervalProjection ≫ admitted.code)
      ((e admitted).reindex intervalProjection) ((f admitted).reindex intervalProjection)
      ((g admitted).reindex intervalProjection))
    (by dsimp only [freshLeft, freshRight, reindexedTriple, Finite.TripleWitnesses.left,
      Finite.TripleWitnesses.right, Finite.TripleWitnesses.reindex, Equivalence.compWith]; rfl)

noncomputable def arbitraryFreshBinaryRoute :
    Finite.Cell (Finite.selected (a := intervalProjection ≫ admitted.code) (b := intervalProjection ≫
      admitted.code) (freshLeft admitted F)) (Finite.selected (a := intervalProjection ≫ admitted.code) (b :=
      intervalProjection ≫ admitted.code) (freshRight admitted F)) :=
  Finite.vertical (Finite.vertical (freshLeftAdjustment admitted F) (freshBinaryRoute admitted))
    (Finite.reverse (freshRightAdjustment admitted F))

noncomputable def arbitraryFreshBinaryComparison :=
  Examples.NativeLatticeTransport.Cartesian.PathData.ofPath (
    (triple admitted).freshBinaryAssociatorReindex
      (a := admitted.code) (b := admitted.code) (c := admitted.code) (d := admitted.code)
      (e admitted) (f admitted) (g admitted) (carrierSet admitted) (carrierSet admitted)
      intervalProjection (freshLeft admitted F) (freshRight admitted F) rfl rfl
      (arbitraryFreshBinaryRoute admitted F))

noncomputable def actualArbitraryFreshBinaryComparison :=
  arbitraryFreshBinaryComparison (Γ := Γ) (admission ℤ)
    ⟨SmallUniverse.NativeDecode.filling (intervalProjection ≫ (admission ℤ).code),
      SmallUniverse.NativeDecode.filling_lawful _⟩
end Examples.NativeFiniteCoherence.Cartesian

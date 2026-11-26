import SquareKit.Internal.Cubical.NativeStructureCoherence
import SquareKit.Internal.Cubical.CartesianNativeStructureCoherence
import Examples.NativeLatticeTransport

/-! A admitted translation chain of pointed integer successor systems. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.NativeStructureCoherence
open CategoryTheory

def translation (k : ℤ) : ℤ ≃ ℤ where
  toFun n := n + k
  invFun n := n - k
  left_inv n := by dsimp; omega
  right_inv n := by dsimp; omega

namespace Presheaf
open SquareKit.Cubical.Presheaf StructureIdentity.Coherence
variable {Γ : Context.{1}}
variable (admitted : SmallUniverse.LargeConstructors.Result (constantFamily Γ (ULift.{1} ℤ)))
noncomputable abbrev A := SmallUniverse.liftedDecode admitted.code
noncomputable def point (n : ℤ) : Term (A (Γ := Γ) admitted) :=
  Term.map admitted.decoding.inv ⟨fun _ => ⟨n⟩, fun _ => rfl⟩
noncomputable def shift (k : ℤ) : A (Γ := Γ) admitted ≅ A (Γ := Γ) admitted :=
  StructureIdentity.Native.presentedCarrierIso admitted.decoding admitted.decoding (translation k)
noncomputable def system (n : ℤ) : PointedEndomorphism (A (Γ := Γ) admitted) :=
  ⟨point admitted n, (shift admitted 1).hom⟩

theorem shift_point (n k : ℤ) : Term.map (shift (Γ := Γ) admitted k).hom (point admitted n) = point admitted (n+k) := by
  apply Term.ext
  intro x
  change admitted.decoding.inv.app x
    (ULift.up (((admitted.decoding.hom.app x (admitted.decoding.inv.app x (ULift.up n)))).down + k)) = _
  rw [admitted.decoding.inv_hom_id_app_apply]
  rfl

theorem shift_commute (j k : ℤ) :
    (shift (Γ := Γ) admitted j).hom ≫ (shift admitted k).hom = (shift admitted k).hom ≫ (shift admitted j).hom := by
  ext x z
  change admitted.decoding.inv.app x (ULift.up
    ((admitted.decoding.hom.app x (admitted.decoding.inv.app x
      (ULift.up ((admitted.decoding.hom.app x z).down + j)))).down + k)) = _
  rw [admitted.decoding.inv_hom_id_app_apply]
  change admitted.decoding.inv.app x (ULift.up ((admitted.decoding.hom.app x z).down + j + k)) =
    admitted.decoding.inv.app x (ULift.up ((admitted.decoding.hom.app x
      (admitted.decoding.inv.app x (ULift.up ((admitted.decoding.hom.app x z).down + k)))).down + j))
  rw [admitted.decoding.inv_hom_id_app_apply]
  congr 2
  dsimp
  omega

noncomputable def move (n k : ℤ) : Equivalence (system (Γ := Γ) admitted n) (system admitted (n+k)) where
  map := (shift admitted k).hom
  witness := HomotopyEquivalence.ofIso (shift admitted k)
  point := Term.convert (congrArg (homogeneousPath (A admitted) · (point admitted (n+k))) (shift_point admitted n k).symm)
    (homogeneousRefl (point admitted (n+k)))
  step := Term.convert (congrArg (homogeneousPath (EquivalenceFamilies.maps (A admitted) (A admitted))
    (EquivalenceFamilies.encodeMap ((shift admitted 1).hom ≫ (shift admitted k).hom)))
    (congrArg EquivalenceFamilies.encodeMap (shift_commute admitted 1 k)))
    (homogeneousRefl (EquivalenceFamilies.encodeMap ((shift admitted 1).hom ≫ (shift admitted k).hom)))

noncomputable def composite := (move (Γ := Γ) admitted 0 1).comp (move admitted 1 2)
  (SmallUniverse.NativeDecode.filling admitted.code) (SmallUniverse.NativeDecode.filling_lawful _)
  (SmallUniverse.NativeDecode.filling admitted.code) (SmallUniverse.NativeDecode.filling_lawful _)
  (SmallUniverse.NativeDecode.filling admitted.code) (SmallUniverse.NativeDecode.filling_lawful _)

noncomputable def compositionComparison := Coded.composition
  (a := admitted.code) (b := admitted.code) (c := admitted.code)
  (s := system admitted 0) (t := system admitted 1) (v := system admitted 3) (move (Γ := Γ) admitted 0 1) (move admitted 1 2)
  (composite admitted).witness (Examples.NativeLatticeTransport.Presheaf.carrierSet admitted)
noncomputable def inverseComparison := Coded.inversion
  (a := admitted.code) (b := admitted.code)
  (s := system admitted 0) (t := system admitted 1) (move (Γ := Γ) admitted 0 1)
  (HomotopyEquivalence.ofIso (shift admitted 1).symm)
  (Examples.NativeLatticeTransport.Presheaf.carrierSet admitted)

theorem composite_point : Term.map (composite admitted).map (point admitted 0) = point admitted 3 := by
  change Term.map (shift admitted 2).hom (Term.map (shift admitted 1).hom (point admitted 0)) = _
  rw [shift_point, shift_point]
  norm_num

theorem point_decode (n : ℤ) (x : Γ.Elements) :
    admitted.decoding.hom.app x ((point admitted n).val x) = ULift.up n :=
  admitted.decoding.inv_hom_id_app_apply x _

example (x : Γ.Elements) :
    (admitted.decoding.hom.app x ((Term.map (composite admitted).map (point admitted 0)).val x)).down = 3 := by
  rw [composite_point, point_decode]

example : Term.map (system admitted 3).step (point admitted 3) = point admitted 4 :=
  shift_point admitted 3 1

/-- The unchanged initial point cannot be the endpoint of the selected nonidentity composite. -/
theorem rejects_unchanged (x : Γ.Elements) :
    ¬ Nonempty (Term (homogeneousPath (A admitted)
      (Term.map (composite admitted).map (point admitted 0)) (point admitted 0))) := by
  rintro ⟨p⟩
  have h := homogeneousPathMap admitted.decoding.hom p
  have he := discretePath_endpoints h
  have hx := congrArg (fun t => (t.val x).down) he
  rw [composite_point] at hx
  change (admitted.decoding.hom.app x ((point admitted 3).val x)).down =
    (admitted.decoding.hom.app x ((point admitted 0).val x)).down at hx
  rw [point_decode, point_decode] at hx
  norm_num at hx

/-- Keep both whole paths and their comparison in the existing path-data
interface before specializing the fillers. -/
noncomputable def substitutionComparisonData
    (F : {F : Filling (A admitted) // F.Lawful})
    (G : {F : Filling (SmallUniverse.liftedDecode
      (projection (interval Γ) ≫ admitted.code)) // F.Lawful}) :=
  Examples.NativeLatticeTransport.Presheaf.PathData.ofPath
    (Coded.compositionReindex
      (a := admitted.code) (b := admitted.code) (c := admitted.code)
      (s := system admitted 0) (t := system admitted 1) (v := system admitted 3)
      (move admitted 0 1) (move admitted 1 2) (composite admitted).witness
      (Examples.NativeLatticeTransport.Presheaf.carrierSet admitted) (projection (interval Γ))
      F.1 F.2 F.1 F.2 G.1 G.2 G.1 G.2)

noncomputable def substitutionComparison := substitutionComparisonData admitted
  ⟨SmallUniverse.NativeDecode.filling admitted.code, SmallUniverse.NativeDecode.filling_lawful _⟩
  ⟨SmallUniverse.NativeDecode.filling (projection (interval Γ) ≫ admitted.code),
    SmallUniverse.NativeDecode.filling_lawful _⟩

namespace LatticeControl
open StructureIdentity.Native Examples.CompositionalStructureIdentity
open Examples.NativeLatticeTransport.Presheaf
variable {X Y : Type} [Lattice X] [Lattice Y]

/-- The generic whole-path comparison also applies to the existing lattice
consumer, using its proved native sethood. -/
noncomputable def compare
    (a : SmallUniverse.LargeConstructors.Result (constantFamily Γ (ULift.{1} X)))
    (b : SmallUniverse.LargeConstructors.Result (constantFamily Γ (ULift.{1} Y))) (e : X ≃o Y)
    (q : Term (homogeneousPath (objects rawLattice Γ)
      (objectOf rawLattice a.code (fields a)) (objectOf rawLattice b.code (movedFields a b e))))
    (h : Term (homogeneousPath (SmallUniverse.NativeUnivalence.paths a.code b.code)
      (Term.map (carrierProjection rawLattice a.code b.code (fields a) (movedFields a b e)) (rawPath a b e))
      (Term.map (carrierProjection rawLattice a.code b.code (fields a) (movedFields a b e)) q))) :=
  wholeComparison rawLattice a.code b.code (fields a) (movedFields a b e)
    (carrierSet b) (rawPath a b e) q h
end LatticeControl

end Presheaf
namespace Cartesian
open SquareKit.Cubical.Cartesian StructureIdentity.Coherence
variable {Γ : Context.{1}}
variable (admitted : SmallUniverse.LargeConstructors.Result (constantFamily Γ (ULift.{1} ℤ)))
noncomputable abbrev A := SmallUniverse.liftedDecode admitted.code
noncomputable def point (n : ℤ) : Term (A (Γ := Γ) admitted) :=
  Term.map admitted.decoding.inv ⟨fun _ => ⟨n⟩, fun _ => rfl⟩
noncomputable def shift (k : ℤ) : A (Γ := Γ) admitted ≅ A (Γ := Γ) admitted :=
  StructureIdentity.Native.presentedCarrierIso admitted.decoding admitted.decoding (translation k)
noncomputable def system (n : ℤ) : PointedEndomorphism (A (Γ := Γ) admitted) :=
  ⟨point admitted n, (shift admitted 1).hom⟩

theorem shift_point (n k : ℤ) : Term.map (shift (Γ := Γ) admitted k).hom (point admitted n) = point admitted (n+k) := by
  apply Term.ext
  intro x
  change admitted.decoding.inv.app x
    (ULift.up (((admitted.decoding.hom.app x (admitted.decoding.inv.app x (ULift.up n)))).down + k)) = _
  rw [admitted.decoding.inv_hom_id_app_apply]
  rfl

theorem shift_commute (j k : ℤ) :
    (shift (Γ := Γ) admitted j).hom ≫ (shift admitted k).hom = (shift admitted k).hom ≫ (shift admitted j).hom := by
  ext x z
  change admitted.decoding.inv.app x (ULift.up
    ((admitted.decoding.hom.app x (admitted.decoding.inv.app x
      (ULift.up ((admitted.decoding.hom.app x z).down + j)))).down + k)) = _
  rw [admitted.decoding.inv_hom_id_app_apply]
  change admitted.decoding.inv.app x (ULift.up ((admitted.decoding.hom.app x z).down + j + k)) =
    admitted.decoding.inv.app x (ULift.up ((admitted.decoding.hom.app x
      (admitted.decoding.inv.app x (ULift.up ((admitted.decoding.hom.app x z).down + k)))).down + j))
  rw [admitted.decoding.inv_hom_id_app_apply]
  congr 2
  dsimp
  omega

noncomputable def move (n k : ℤ) : Equivalence (system (Γ := Γ) admitted n) (system admitted (n+k)) where
  map := (shift admitted k).hom
  witness := HomotopyEquivalence.ofIso (shift admitted k)
    (SmallUniverse.NativeDecode.filling admitted.code) (SmallUniverse.NativeDecode.filling_lawful _)
  point := Term.convert (congrArg (homogeneousPath (A admitted) · (point admitted (n+k))) (shift_point admitted n k).symm)
    (homogeneousRefl (point admitted (n+k)))
  step := Term.convert (congrArg (homogeneousPath (EquivalenceFamilies.maps (A admitted) (A admitted))
    (EquivalenceFamilies.encodeMap ((shift admitted 1).hom ≫ (shift admitted k).hom)))
    (congrArg EquivalenceFamilies.encodeMap (shift_commute admitted 1 k)))
    (homogeneousRefl (EquivalenceFamilies.encodeMap ((shift admitted 1).hom ≫ (shift admitted k).hom)))

noncomputable def composite := (move (Γ := Γ) admitted 0 1).comp (move admitted 1 2)
  (SmallUniverse.NativeDecode.filling admitted.code) (SmallUniverse.NativeDecode.filling_lawful _)
  (SmallUniverse.NativeDecode.filling admitted.code) (SmallUniverse.NativeDecode.filling_lawful _)
  (SmallUniverse.NativeDecode.filling admitted.code) (SmallUniverse.NativeDecode.filling_lawful _)

noncomputable def compositionComparison := Coded.composition
  (a := admitted.code) (b := admitted.code) (c := admitted.code)
  (s := system admitted 0) (t := system admitted 1) (v := system admitted 3) (move (Γ := Γ) admitted 0 1) (move admitted 1 2)
  (composite admitted).witness (Examples.NativeLatticeTransport.Cartesian.carrierSet admitted)
noncomputable def inverseWitness : HomotopyEquivalence (move admitted 0 1).witness.selectedInverse := by
  change HomotopyEquivalence ((HomotopyEquivalence.ofIso (shift admitted 1)
    (SmallUniverse.NativeDecode.filling admitted.code) (SmallUniverse.NativeDecode.filling_lawful _)).selectedInverse)
  rw [Selected.inverse_ofIso]
  exact HomotopyEquivalence.ofIso (shift admitted 1).symm
    (SmallUniverse.NativeDecode.filling admitted.code) (SmallUniverse.NativeDecode.filling_lawful _)

noncomputable def inverseComparison := Coded.inversion
  (a := admitted.code) (b := admitted.code)
  (s := system admitted 0) (t := system admitted 1) (move (Γ := Γ) admitted 0 1)
  (inverseWitness admitted)
  (Examples.NativeLatticeTransport.Cartesian.carrierSet admitted)

theorem composite_point : Term.map (composite admitted).map (point admitted 0) = point admitted 3 := by
  change Term.map (shift admitted 2).hom (Term.map (shift admitted 1).hom (point admitted 0)) = _
  rw [shift_point, shift_point]
  norm_num

theorem point_decode (n : ℤ) (x : Γ.Elements) :
    admitted.decoding.hom.app x ((point admitted n).val x) = ULift.up n :=
  admitted.decoding.inv_hom_id_app_apply x _

example (x : Γ.Elements) :
    (admitted.decoding.hom.app x ((Term.map (composite admitted).map (point admitted 0)).val x)).down = 3 := by
  rw [composite_point, point_decode]

example : Term.map (system admitted 3).step (point admitted 3) = point admitted 4 :=
  shift_point admitted 3 1

/-- The unchanged initial point cannot be the endpoint of the selected nonidentity composite. -/
theorem rejects_unchanged (x : Γ.Elements) :
    ¬ Nonempty (Term (homogeneousPath (A admitted)
      (Term.map (composite admitted).map (point admitted 0)) (point admitted 0))) := by
  rintro ⟨p⟩
  have hx := (StructureIdentity.Native.presentedPathEquiv admitted.decoding _ _ x (p.val x)).down.down
  rw [composite_point] at hx
  change (admitted.decoding.hom.app x ((point admitted 3).val x)).down =
    (admitted.decoding.hom.app x ((point admitted 0).val x)).down at hx
  rw [point_decode, point_decode] at hx
  norm_num at hx

/-- Keep both whole paths and their comparison in the existing path-data
interface before specializing the fillers. -/
noncomputable def substitutionComparisonData
    (F : {F : Filling (A admitted) // F.Lawful})
    (G : {F : Filling (SmallUniverse.liftedDecode
      (projection (interval Γ) ≫ admitted.code)) // F.Lawful}) :=
  Examples.NativeLatticeTransport.Cartesian.PathData.ofPath
    (Coded.compositionReindex
      (a := admitted.code) (b := admitted.code) (c := admitted.code)
      (s := system admitted 0) (t := system admitted 1) (v := system admitted 3)
      (move admitted 0 1) (move admitted 1 2) (composite admitted).witness
      (Examples.NativeLatticeTransport.Cartesian.carrierSet admitted) (projection (interval Γ))
      F.1 F.2 F.1 F.2 G.1 G.2 G.1 G.2)

noncomputable def substitutionComparison := substitutionComparisonData admitted
  ⟨SmallUniverse.NativeDecode.filling admitted.code, SmallUniverse.NativeDecode.filling_lawful _⟩
  ⟨SmallUniverse.NativeDecode.filling (projection (interval Γ) ≫ admitted.code),
    SmallUniverse.NativeDecode.filling_lawful _⟩

namespace LatticeControl
open StructureIdentity.Native Examples.CompositionalStructureIdentity
open Examples.NativeLatticeTransport.Cartesian
variable {X Y : Type} [Lattice X] [Lattice Y]

/-- The generic whole-path comparison also applies to the existing lattice
consumer, using its proved native sethood. -/
noncomputable def compare
    (a : SmallUniverse.LargeConstructors.Result (constantFamily Γ (ULift.{1} X)))
    (b : SmallUniverse.LargeConstructors.Result (constantFamily Γ (ULift.{1} Y))) (e : X ≃o Y)
    (q : Term (homogeneousPath (objects rawLattice Γ)
      (objectOf rawLattice a.code (fields a)) (objectOf rawLattice b.code (movedFields a b e))))
    (h : Term (homogeneousPath (SmallUniverse.NativeUnivalence.paths a.code b.code)
      (Term.map (carrierProjection rawLattice a.code b.code (fields a) (movedFields a b e)) (rawPath a b e))
      (Term.map (carrierProjection rawLattice a.code b.code (fields a) (movedFields a b e)) q))) :=
  wholeComparison rawLattice a.code b.code (fields a) (movedFields a b e)
    (carrierSet b) (rawPath a b e) q h
end LatticeControl

end Cartesian
namespace Actual
noncomputable def original {Γ : SquareKit.Cubical.Presheaf.Context.{1}} :=
  Presheaf.compositionComparison (Examples.NativeLatticeTransport.Presheaf.admission (Γ := Γ) ℤ)
noncomputable def cartesian {Γ : SquareKit.Cubical.Cartesian.Context.{1}} :=
  Cartesian.compositionComparison (Examples.NativeLatticeTransport.Cartesian.admission (Γ := Γ) ℤ)
noncomputable def originalInverse {Γ : SquareKit.Cubical.Presheaf.Context.{1}} :=
  Presheaf.inverseComparison (Examples.NativeLatticeTransport.Presheaf.admission (Γ := Γ) ℤ)
noncomputable def cartesianInverse {Γ : SquareKit.Cubical.Cartesian.Context.{1}} :=
  Cartesian.inverseComparison (Examples.NativeLatticeTransport.Cartesian.admission (Γ := Γ) ℤ)
end Actual

end Examples.NativeStructureCoherence

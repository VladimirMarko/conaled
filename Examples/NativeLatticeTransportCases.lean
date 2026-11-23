import Examples.NativeLatticeTransport

/-! Admitted lattice objects, native structure paths and dependent order witnesses. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.NativeLatticeTransport
open CategoryTheory SquareKit.StructureIdentity Examples.CompositionalStructureIdentity
open Examples.NativeStructureRecovery (comparablePair)
open Examples.LatticeTransportBridge
namespace Presheaf
open SquareKit.Cubical.Presheaf StructureIdentity.Native StructuredIdentity
variable {Γ : Context.{1}} {X Y : Type} [Lattice X] [Lattice Y]

noncomputable def swapPath :=
  latticePath (admission (Γ := Γ) (Bool × Bool)) (admission (Bool × Bool)) swap

example (x : Γ.Elements) :
    (pathOrderedPair (admission (Γ := Γ) (Bool × Bool)) (admission (Bool × Bool)) swap ordered x).val =
      ((false, false), (false, true)) := by
  rw [pathOrderedPair_direct]; rfl

/-- Admit a lattice presentation through the public constructor. -/
noncomputable def admittedPath (e : X ≃o Y) :=
  latticePath (admission (Γ := Γ) X) (admission Y) e

noncomputable def dualPath := admittedPath (Γ := Γ) dualBool

noncomputable def tuplePath := admittedPath (Γ := Γ) tupleBridge

noncomputable def admittedWitness (e : X ≃o Y) (p : OrderedPair X) (x : Γ.Elements) : OrderedPair Y :=
  pathOrderedPair (admission (Γ := Γ) X) (admission Y) e p x

noncomputable def dualWitness (x : Γ.Elements) : OrderedPair (OrderDual Bool) :=
  admittedWitness dualBool boolInclusion x

noncomputable def tupleWitness (x : Γ.Elements) : OrderedPair (Bool × Bool) :=
  admittedWitness tupleBridge tupleOrdered x

theorem tupleWitness_recovery (x : Γ.Elements) : tupleWitness (Γ := Γ) x = ordered := by
  change pathOrderedPair _ _ tupleBridge tupleOrdered x = _
  rw [pathOrderedPair_direct]
  exact tuple_ordered_recovery

theorem dualWitness_value (x : Γ.Elements) : (dualWitness (Γ := Γ) x).val = (true, false) := by
  change (pathOrderedPair _ _ dualBool boolInclusion x).val = _
  rw [pathOrderedPair_direct]; rfl

end Presheaf
namespace Cartesian
open SquareKit.Cubical.Cartesian StructureIdentity.Native StructuredIdentity
variable {Γ : Context.{1}} {X Y : Type} [Lattice X] [Lattice Y]

noncomputable def swapPath :=
  latticePath (admission (Γ := Γ) (Bool × Bool)) (admission (Bool × Bool)) swap

example (x : Γ.Elements) :
    (pathOrderedPair (admission (Γ := Γ) (Bool × Bool)) (admission (Bool × Bool)) swap ordered x).val =
      ((false, false), (false, true)) := by
  rw [pathOrderedPair_direct]; rfl

/-- Admit a lattice presentation through the public constructor. -/
noncomputable def admittedPath (e : X ≃o Y) :=
  latticePath (admission (Γ := Γ) X) (admission Y) e

noncomputable def dualPath := admittedPath (Γ := Γ) dualBool

noncomputable def tuplePath := admittedPath (Γ := Γ) tupleBridge

noncomputable def admittedWitness (e : X ≃o Y) (p : OrderedPair X) (x : Γ.Elements) : OrderedPair Y :=
  pathOrderedPair (admission (Γ := Γ) X) (admission Y) e p x

noncomputable def dualWitness (x : Γ.Elements) : OrderedPair (OrderDual Bool) :=
  admittedWitness dualBool boolInclusion x

noncomputable def tupleWitness (x : Γ.Elements) : OrderedPair (Bool × Bool) :=
  admittedWitness tupleBridge tupleOrdered x

theorem tupleWitness_recovery (x : Γ.Elements) : tupleWitness (Γ := Γ) x = ordered := by
  change pathOrderedPair _ _ tupleBridge tupleOrdered x = _
  rw [pathOrderedPair_direct]
  exact tuple_ordered_recovery

theorem dualWitness_value (x : Γ.Elements) : (dualWitness (Γ := Γ) x).val = (true, false) := by
  change (pathOrderedPair _ _ dualBool boolInclusion x).val = _
  rw [pathOrderedPair_direct]; rfl

end Cartesian
namespace Comparison
open SquareKit.Cubical
variable {Γ : Presheaf.Context.{1}} {X Y : Type} [Lattice X] [Lattice Y]

/-- Complete law-bearing models are compared naturally through their host presentation. -/
noncomputable def models
    (a : Presheaf.SmallUniverse.LargeConstructors.Result (Presheaf.constantFamily Γ (ULift.{1} X)))
    (c : Cartesian.SmallUniverse.LargeConstructors.Result
      (Cartesian.constantFamily (Cartesian.restrict Γ) (ULift.{1} X))) :
    Cartesian.restrictFamily (Presheaf.StructureIdentity.Native.modelsFamily lattice
      (Presheaf.SmallUniverse.liftedDecode a.code)) ≅
    Cartesian.StructureIdentity.Native.modelsFamily lattice (Cartesian.SmallUniverse.liftedDecode c.code) :=
  Functor.isoWhiskerLeft (Cartesian.elements Γ)
    (Presheaf.StructureIdentity.Native.presentedModelsIso lattice a.decoding) ≪≫
    (Cartesian.StructureIdentity.Native.presentedModelsIso lattice c.decoding).symm

omit [Lattice X] in
theorem models_recovery
    (a : Presheaf.SmallUniverse.LargeConstructors.Result (Presheaf.constantFamily Γ (ULift.{1} X)))
    (c : Cartesian.SmallUniverse.LargeConstructors.Result
      (Cartesian.constantFamily (Cartesian.restrict Γ) (ULift.{1} X)))
    (x : (Cartesian.restrict Γ).Elements) (s) :
    Cartesian.StructureIdentity.Native.presentedModelsEquiv lattice c.decoding x
      ((models a c).hom.app x s) =
    Presheaf.StructureIdentity.Native.presentedModelsEquiv lattice a.decoding
      ((Cartesian.elements Γ).obj x) s :=
  (Cartesian.StructureIdentity.Native.presentedModelsEquiv lattice c.decoding x).apply_symm_apply _

/-- Restriction comparison commutes with transport of the complete presented model. -/
theorem models_transport
    (a : Presheaf.SmallUniverse.LargeConstructors.Result (Presheaf.constantFamily Γ (ULift.{1} X)))
    (b : Presheaf.SmallUniverse.LargeConstructors.Result (Presheaf.constantFamily Γ (ULift.{1} Y)))
    (c : Cartesian.SmallUniverse.LargeConstructors.Result
      (Cartesian.constantFamily (Cartesian.restrict Γ) (ULift.{1} X)))
    (d : Cartesian.SmallUniverse.LargeConstructors.Result
      (Cartesian.constantFamily (Cartesian.restrict Γ) (ULift.{1} Y)))
    (e : X ≃o Y) (x : (Cartesian.restrict Γ).Elements) (s) :
    (models b d).hom.app x
      ((Presheaf.StructureIdentity.Native.presentedModelsTransport lattice a.decoding b.decoding e.toEquiv).hom.app
        ((Cartesian.elements Γ).obj x) s) =
    (Cartesian.StructureIdentity.Native.presentedModelsTransport lattice c.decoding d.decoding e.toEquiv).hom.app x
      ((models a c).hom.app x s) := by
  apply (Cartesian.StructureIdentity.Native.presentedModelsEquiv lattice d.decoding x).injective
  apply ULift.ext
  exact (congrArg ULift.down (models_recovery b d x _)).trans
    ((Presheaf.StructureIdentity.Native.presentedModelsTransport_recovery lattice
      a.decoding b.decoding e.toEquiv ((Cartesian.elements Γ).obj x) s).trans
      ((congrArg (fun z => lattice.transport e.toEquiv z.down) (models_recovery a c x s)).symm.trans
        (Cartesian.StructureIdentity.Native.presentedModelsTransport_recovery lattice
          c.decoding d.decoding e.toEquiv x ((models a c).hom.app x s)).symm))

/-- Both independent native constructions preserve the same complete dependent value. -/
theorem ordered_transport (e : X ≃o Y) (p : OrderedPair X)
    (x : (Cartesian.restrict Γ).Elements) :
    Examples.NativeLatticeTransport.Presheaf.pathOrderedPair
      (Examples.NativeLatticeTransport.Presheaf.admission (Γ := Γ) X)
      (Examples.NativeLatticeTransport.Presheaf.admission Y) e p ((Cartesian.elements Γ).obj x) =
    Examples.NativeLatticeTransport.Cartesian.pathOrderedPair
      (Examples.NativeLatticeTransport.Cartesian.admission (Γ := Cartesian.restrict Γ) X)
      (Examples.NativeLatticeTransport.Cartesian.admission Y) e p x := by
  rw [Examples.NativeLatticeTransport.Presheaf.pathOrderedPair_direct,
    Examples.NativeLatticeTransport.Cartesian.pathOrderedPair_direct]

end Comparison

end Examples.NativeLatticeTransport

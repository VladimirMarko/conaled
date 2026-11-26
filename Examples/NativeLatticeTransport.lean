import Examples.LatticeTransportBridge
import SquareKit.Internal.Cubical.NativeStructureUaComparison
import SquareKit.Internal.Cubical.CartesianNativeStructureUaComparison

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

/-- The carrier is admitted using its actual discrete filling and small presentation. -/
noncomputable def admission (X : Type) :
    SmallUniverse.LargeConstructors.Result (constantFamily Γ (ULift.{1} X)) :=
  let q : Term (constantFamily Γ PUnit.{2}) := ⟨fun _ => PUnit.unit, fun _ => rfl⟩
  SmallUniverse.LargeConstructors.construct
    ⟨fun _ => X, fun _ => Equiv.ulift.symm⟩
    (discreteFilling q (fun _ => ULift.{1} X)) (discreteFilling_lawful q _)

variable (a : SmallUniverse.LargeConstructors.Result (constantFamily Γ (ULift.{1} X)))
  (b : SmallUniverse.LargeConstructors.Result (constantFamily Γ (ULift.{1} Y)))

noncomputable def fields : Term (family rawLattice (SmallUniverse.liftedDecode a.code)) :=
  Term.map (presentedIso rawLattice a.decoding).inv
    ⟨fun _ => ⟨(latticeModel X).val⟩, fun _ => rfl⟩

theorem fields_decode (x : Γ.Elements) :
    decode rawLattice a.decoding x ((fields a).val x) = (latticeModel X).val :=
  decode_presentedIso_inv rawLattice a.decoding x _

noncomputable def carrier (e : X ≃o Y) := presentedCarrierIso a.decoding b.decoding e.toEquiv

noncomputable def movedFields (e : X ≃o Y) :=
  Term.map (actionIso rawLattice (carrier a b e)).hom (fields a)

theorem movedFields_decode (e : X ≃o Y) (x : Γ.Elements) :
    decode rawLattice b.decoding x ((movedFields a b e).val x) = (latticeModel Y).val := by
  rw [show (movedFields a b e).val x =
    (actionIso rawLattice (presentedCarrierIso a.decoding b.decoding e.toEquiv)).hom.app x
      ((fields a).val x) from rfl,
    decode_action _ _ _ _ _ (decode_presentedCarrierIso _ _ _), fields_decode]
  exact congrArg Subtype.val (orderIso_transport e)

/-- Discrete presentation proves native sethood of the decoded carrier. -/
noncomputable def carrierSet : Term (HomotopyLevels.isSet (SmallUniverse.liftedDecode a.code)) := by
  apply lam
  apply lam
  let A := SmallUniverse.liftedDecode a.code
  let σ := projection (reindex A (projection A)) ≫ projection A
  exact HomotopyLevels.ofSubsingleton _ (fun x =>
    (presentedPathEquiv (reindexPresented a.decoding σ)
      (Term.reindex (generic A) (projection (reindex A (projection A))))
      (generic (reindex A (projection A))) x).injective.subsingleton)

noncomputable def laws (s : Term (family rawLattice (SmallUniverse.liftedDecode a.code)))
    (hs : ∀ x, decode rawLattice a.decoding x (s.val x) = (latticeModel X).val) :
    Term (lawFamily lattice.law s unitContext) :=
  Term.map (presentedLawIso lattice.law a.decoding s unitContext).inv
    ⟨fun x => ⟨⟨by
      change lattice.law.Eval (C := .fixed Unit) (decode rawLattice a.decoding x (s.val x)) ()
      rw [hs x]
      exact (latticeModel X).property⟩⟩,
      fun _ => by apply ULift.ext; apply Subsingleton.elim⟩

noncomputable def sourceObject : Term (modelObjects lattice Γ) :=
  modelObject lattice a.code (fields a) (carrierSet a) (laws a (fields a) (fields_decode a))

noncomputable def targetObject (e : X ≃o Y) : Term (modelObjects lattice Γ) :=
  modelObject lattice b.code (movedFields a b e) (carrierSet b)
    (laws b (movedFields a b e) (movedFields_decode a b e))

noncomputable def preservation (e : X ≃o Y) :
    Term (preserves rawLattice (carrier a b e).hom (carrier a b e).inv
      (fields a) (movedFields a b e)) :=
  Term.map (preservesActionPathIso rawLattice (carrier a b e) (fields a) _).inv
    (homogeneousRefl (movedFields a b e))

noncomputable def structuredEquivalence (e : X ≃o Y) :
    Term (equivalences rawLattice (fields a) (movedFields a b e)) := by
  let k := carrier a b e
  let E := HomotopyEquivalence.ofIso k
  refine sigmaIntro (EquivalenceFamilies.equivSections _ _ ⟨k.hom, E⟩)
    (Term.map (suppliedEquivalenceFiberIso rawLattice k.hom E (fields a) (movedFields a b e)).inv ?_)
  exact preservation a b e

noncomputable def rawPath (e : X ≃o Y) :=
  Term.map (UaComparison.explicitMap rawLattice a.code (fields a) b.code (movedFields a b e))
    (structuredEquivalence a b e)

/-- The native law-bearing lattice path is built from the selected ua construction. -/
noncomputable def latticePath (e : X ≃o Y) :
    Term (homogeneousPath (modelObjects lattice Γ) (sourceObject a) (targetObject a b e)) :=
  Term.map (UaComparison.modelPathInverse lattice (sourceObject a) (targetObject a b e))
    (rawPath a b e)

noncomputable def latticePathProjection (e : X ≃o Y) :=
  UaComparison.modelPathInverseProjection lattice (sourceObject a) (targetObject a b e)
    (rawPath a b e)

noncomputable def latticePathRoundtrip (e : X ≃o Y) :=
  UaComparison.modelRightInverseAt lattice (sourceObject a) (targetObject a b e) (latticePath a b e)

noncomputable def equivalenceRoundtrip (e : X ≃o Y) :=
  UaComparison.explicitLeftInverseAt rawLattice a.code (fields a) b.code (movedFields a b e)
    (structuredEquivalence a b e)

theorem rawPath_carrier (e : X ≃o Y) :
    let E := (EquivalenceFamilies.equivSections _ _).symm
      (sigmaFst (structuredEquivalence a b e))
    Term.map (HomotopyLevels.pathMap (SIP.Exchange.first (SIP.objectFields rawLattice))
      (objectOf rawLattice a.code (fields a)) (objectOf rawLattice b.code (movedFields a b e)))
      (rawPath a b e) = SmallUniverse.NativeUnivalence.ua a.code b.code E.1 E.2 :=
  UaComparison.explicitMap_carrier_ua rawLattice a.code (fields a) b.code (movedFields a b e)
    (structuredEquivalence a b e)

noncomputable def orderedWitness (p : OrderedPair X) (x : Γ.Elements) :
    (solutionsFamily comparablePair (fields a)).obj x :=
  (presentedSolutionsEquiv comparablePair a.decoding (fields a) x).symm
    ⟨⟨p.val, by
      rw [fields_decode]
      exact (show p.val.1 ⊓ p.val.2 = p.val.1 from inf_eq_left.mpr p.property)⟩⟩

noncomputable def movedWitness (e : X ≃o Y) (p : OrderedPair X) (x : Γ.Elements) :=
  presentedSolutionsTransport comparablePair a.decoding b.decoding e.toEquiv (fields a) x
    (orderedWitness a p x)

theorem movedWitness_data (e : X ≃o Y) (p : OrderedPair X) (x : Γ.Elements) :
    decode (.product .carrier .carrier) b.decoding x (movedWitness a b e p x).1 =
      (directTransport e p).val := by
  unfold movedWitness
  rw [presentedSolutionsTransport_data,
    decode_action _ _ _ _ _ (decode_presentedCarrierIso _ _ _)]
  have h := congrArg (fun z => z.down.val)
    ((presentedSolutionsEquiv comparablePair a.decoding (fields a) x).apply_symm_apply
      (⟨⟨p.val, by rw [fields_decode]; exact (show p.val.1 ⊓ p.val.2 = p.val.1 from inf_eq_left.mpr p.property)⟩⟩))
  change decode (.product .carrier .carrier) a.decoding x (orderedWitness a p x).1 = p.val at h
  rw [h]
  rfl

noncomputable def readMovedWitness (e : X ≃o Y) (p : OrderedPair X) (x : Γ.Elements) : OrderedPair Y :=
  ⟨decode (.product .carrier .carrier) b.decoding x (movedWitness a b e p x).1, by
    have h := (presentedSolutionsEquiv comparablePair b.decoding (movedFields a b e) x
      (movedWitness a b e p x)).down.property
    change comparablePair.Eval (decode rawLattice b.decoding x ((movedFields a b e).val x))
      (decode (.product .carrier .carrier) b.decoding x (movedWitness a b e p x).1) at h
    rw [movedFields_decode] at h
    exact inf_eq_left.mp h⟩

theorem native_direct (e : X ≃o Y) (p : OrderedPair X) (x : Γ.Elements) :
    readMovedWitness a b e p x = directTransport e p :=
  Subtype.ext (movedWitness_data a b e p x)

theorem movedFields_meet (e : X ≃o Y) (x : Γ.Elements) (u v : Y) :
    (decode rawLattice b.decoding x ((movedFields a b e).val x)).1 u v = u ⊓ v := by
  rw [movedFields_decode]; rfl

theorem movedFields_join (e : X ≃o Y) (x : Γ.Elements) (u v : Y) :
    (decode rawLattice b.decoding x ((movedFields a b e).val x)).2 u v = u ⊔ v := by
  rw [movedFields_decode]; rfl

theorem movedWitness_recovery (e : X ≃o Y) (p : OrderedPair X) (x : Γ.Elements) :
    (presentedSolutionsTransport comparablePair a.decoding b.decoding e.toEquiv (fields a) x).symm
      (movedWitness a b e p x) = orderedWitness a p x :=
  (presentedSolutionsTransport comparablePair a.decoding b.decoding e.toEquiv (fields a) x).symm_apply_apply _

/-- The independently defined preservation family rejects the bad bijection. -/
theorem bad_preservation_rejected
    (c : SmallUniverse.LargeConstructors.Result (constantFamily Γ (ULift.{1} (Bool × Bool))))
    (x : Γ.Elements) :
    ¬ Nonempty ((preserves rawLattice
      (presentedCarrierIso c.decoding c.decoding badBijection).hom
      (presentedCarrierIso c.decoding c.decoding badBijection).inv (fields c) (fields c)).obj x) := by
  rintro ⟨h⟩
  have hp := ((presentedPreservationEquiv rawLattice c.decoding c.decoding badBijection
    (fields c) (fields c) x) h).down.down
  rw [fields_decode] at hp
  exact badBijection_rejected hp

/-- The selected raw structure path projected to its universe carrier. -/
noncomputable def carrierPath (e : X ≃o Y) :=
  Term.map (HomotopyLevels.pathMap (SIP.Exchange.first (SIP.objectFields rawLattice))
    (objectOf rawLattice a.code (fields a)) (objectOf rawLattice b.code (movedFields a b e)))
    (rawPath a b e)
noncomputable def point (v : X) : Term (SmallUniverse.liftedDecode a.code) :=
  Term.map a.decoding.inv ⟨fun _ => ⟨v⟩, fun _ => rfl⟩
noncomputable def transportedPoint (e : X ≃o Y) (v : X) :=
  Term.map (SmallUniverse.NativeUnivalence.pathToMap (carrierPath a b e)) (point a v)
theorem point_carrier_decode (e : X ≃o Y) (v : X) (x : Γ.Elements) :
    (b.decoding.hom.app x ((Term.map (carrier a b e).hom (point a v)).val x)).down = e v :=
  (decode_presentedCarrierIso a.decoding b.decoding e.toEquiv x ((point a v).val x)).trans
    (congrArg e (congrArg ULift.down (a.decoding.inv_hom_id_app_apply x ⟨v⟩)))
theorem selected_map (e : X ≃o Y) :
    ((EquivalenceFamilies.equivSections _ _).symm (sigmaFst (structuredEquivalence a b e))).1 =
      (carrier a b e).hom :=
  congrArg Sigma.fst ((EquivalenceFamilies.equivSections _ _).symm_apply_apply _)
omit [Lattice X] [Lattice Y] in
theorem ua_decode (f : SmallUniverse.liftedDecode a.code ⟶ SmallUniverse.liftedDecode b.code)
    (E : HomotopyEquivalence f) (v : X) (x : Γ.Elements) :
    (b.decoding.hom.app x ((Term.map (SmallUniverse.NativeUnivalence.pathToMap
      (SmallUniverse.NativeUnivalence.ua a.code b.code f E)) (point a v)).val x)).down =
    (b.decoding.hom.app x ((Term.map f (point a v)).val x)).down := by
  let h := SmallUniverse.NativeUnivalence.uaComparison a.code b.code f E (point a v)
  exact (((presentedPathEquiv b.decoding _ _ x) (h.val x)).down.down).symm
theorem transportedPoint_decode (e : X ≃o Y) (v : X) (x : Γ.Elements) :
    (b.decoding.hom.app x ((transportedPoint a b e v).val x)).down = e v := by
  let E := (EquivalenceFamilies.equivSections _ _).symm (sigmaFst (structuredEquivalence a b e))
  let observe (f : SmallUniverse.liftedDecode a.code ⟶ SmallUniverse.liftedDecode b.code) :=
    (b.decoding.hom.app x ((Term.map f (point a v)).val x)).down
  have hpath : observe (SmallUniverse.NativeUnivalence.pathToMap (carrierPath a b e)) =
      observe (SmallUniverse.NativeUnivalence.pathToMap (SmallUniverse.NativeUnivalence.ua a.code b.code E.1 E.2)) :=
    congrArg (fun (p : Term (SmallUniverse.NativeUnivalence.paths a.code b.code)) =>
      observe (SmallUniverse.NativeUnivalence.pathToMap p)) (rawPath_carrier a b e)
  exact hpath.trans ((ua_decode a b E.1 E.2 v x).trans
    ((congrArg observe (selected_map a b e)).trans (point_carrier_decode a b e v x)))
/-- Project the actual law-bearing lattice path to the universe. -/
noncomputable def latticeCarrierPath (e : X ≃o Y) :=
  Term.map (HomotopyLevels.pathMap (SIP.Exchange.first (SIP.objectFields rawLattice))
    (objectOf rawLattice a.code (fields a)) (objectOf rawLattice b.code (movedFields a b e)))
    (Term.map (HomotopyLevels.pathMap (PropositionExtension.first (objectConditions lattice Γ))
      (sourceObject a) (targetObject a b e)) (latticePath a b e))
/-- The law-bearing projection recovers the selected raw carrier path by a native two-path. -/
noncomputable def carrierProjection (e : X ≃o Y) :
    Term (homogeneousPath (SmallUniverse.NativeUnivalence.paths a.code b.code)
      (latticeCarrierPath a b e) (carrierPath a b e)) :=
  homogeneousPathMap (HomotopyLevels.pathMap (SIP.Exchange.first (SIP.objectFields rawLattice))
    (objectOf rawLattice a.code (fields a)) (objectOf rawLattice b.code (movedFields a b e)))
    (latticePathProjection a b e)

omit [Lattice X] [Lattice Y] in
noncomputable def evaluatePath (v : X) :
    SmallUniverse.NativeUnivalence.paths a.code b.code ⟶ SmallUniverse.liftedDecode b.code :=
  EquivalenceFamilies.decodeMap (lam
    (Term.map (SmallUniverse.NativeUnivalence.pathToMap
      (SmallUniverse.NativeUnivalence.genericPath a.code b.code))
      ((point a v).reindex (projection (SmallUniverse.NativeUnivalence.paths a.code b.code)))))
omit [Lattice X] [Lattice Y] in
theorem evaluatePath_beta (v : X) (p : Term (SmallUniverse.NativeUnivalence.paths a.code b.code)) :
    Term.map (evaluatePath a b v) p = Term.map (SmallUniverse.NativeUnivalence.pathToMap p) (point a v) := by
  have h := congrArg Sigma.fst (SmallUniverse.NativeUnivalence.pathToEquivalence_record_generic p)
  exact (EquivalenceFamilies.decodeMap_lam_apply _ p).trans
    (congrArg (fun k => Term.map k (point a v)) h)

/-- Actual universal-decoder transport along the law-bearing path projection. -/
noncomputable def latticeTransportedPoint (e : X ≃o Y) (v : X) :=
  Term.map (SmallUniverse.NativeUnivalence.pathToMap (latticeCarrierPath a b e)) (point a v)
theorem latticeTransportedPoint_decode (e : X ≃o Y) (v : X) (x : Γ.Elements) :
    (b.decoding.hom.app x ((latticeTransportedPoint a b e v).val x)).down = e v := by
  let h := homogeneousPathMap (evaluatePath a b v) (carrierProjection a b e)
  have hd := ((presentedPathEquiv b.decoding _ _ x) (h.val x)).down.down
  let observe (t : Term (SmallUniverse.liftedDecode b.code)) := (b.decoding.hom.app x (t.val x)).down
  exact (congrArg observe (evaluatePath_beta a b v (latticeCarrierPath a b e))).symm.trans
    (hd.trans ((congrArg observe (evaluatePath_beta a b v (carrierPath a b e))).trans
      (transportedPoint_decode a b e v x)))
/-- Transport both values along the native path and reconstruct their admitted order proof. -/
noncomputable def pathOrderedPair (e : X ≃o Y) (p : OrderedPair X) (x : Γ.Elements) : OrderedPair Y :=
  ⟨((b.decoding.hom.app x ((latticeTransportedPoint a b e p.val.1).val x)).down,
    (b.decoding.hom.app x ((latticeTransportedPoint a b e p.val.2).val x)).down), by
      rw [latticeTransportedPoint_decode, latticeTransportedPoint_decode]
      exact e.monotone p.property⟩
theorem pathOrderedPair_direct (e : X ≃o Y) (p : OrderedPair X) (x : Γ.Elements) :
    pathOrderedPair a b e p x = directTransport e p := by
  apply Subtype.ext
  exact Prod.ext (latticeTransportedPoint_decode a b e p.val.1 x)
    (latticeTransportedPoint_decode a b e p.val.2 x)
/-- Recover the complete native solution from the actual path-transported values. -/
noncomputable def pathSolution (e : X ≃o Y) (p : OrderedPair X) (x : Γ.Elements) :
    (solutionsFamily comparablePair (movedFields a b e)).obj x :=
  (presentedSolutionsEquiv comparablePair b.decoding (movedFields a b e) x).symm
    ⟨⟨(pathOrderedPair a b e p x).val, by
      rw [movedFields_decode]
      exact (show (pathOrderedPair a b e p x).val.1 ⊓ (pathOrderedPair a b e p x).val.2 =
        (pathOrderedPair a b e p x).val.1 from inf_eq_left.mpr (pathOrderedPair a b e p x).property)⟩⟩
theorem pathSolution_moved (e : X ≃o Y) (p : OrderedPair X) (x : Γ.Elements) :
    pathSolution a b e p x = movedWitness a b e p x := by
  apply (presentedSolutionsEquiv comparablePair b.decoding (movedFields a b e) x).injective
  unfold pathSolution
  rw [Equiv.apply_symm_apply]
  apply ULift.ext
  apply Subtype.ext
  exact (congrArg Subtype.val (pathOrderedPair_direct a b e p x)).trans (movedWitness_data a b e p x).symm


/-- Keep both endpoints with their actual native path, so concrete clients need
not repeatedly normalize a deeply dependent result type. -/
structure PathData {Γ : Context.{1}} (A : Family Γ) where
  source : Term A
  target : Term A
  path : Term (homogeneousPath A source target)

def PathData.ofPath {Γ : Context.{1}} {A : Family Γ} {s t : Term A}
    (p : Term (homogeneousPath A s t)) : PathData A := ⟨s, t, p⟩

/-- A computational boundary around the existing law-bearing path, with no new
choice of path or equivalence. -/
noncomputable def latticePathData (e : X ≃o Y) :=
  PathData.ofPath (latticePath a b e)

theorem latticePathData_source (e : X ≃o Y) :
    (latticePathData a b e).source = sourceObject a := rfl

theorem latticePathData_target (e : X ≃o Y) :
    (latticePathData a b e).target = targetObject a b e := rfl

theorem latticePathData_path (e : X ≃o Y) :
    (latticePathData a b e).path = latticePath a b e := rfl

/-- Retain the complete selected equivalence and its native recovery path. -/
noncomputable def equivalenceRecoveryData (e : X ≃o Y) :=
  PathData.ofPath (equivalenceRoundtrip a b e)

theorem equivalenceRecoveryData_target (e : X ≃o Y) :
    (equivalenceRecoveryData a b e).target = structuredEquivalence a b e := rfl

/-- The law-bearing path still projects to the original raw path by the same
native two-path. -/
noncomputable def latticeProjectionData (e : X ≃o Y) :=
  PathData.ofPath (latticePathProjection a b e)

end Presheaf
namespace Cartesian
open SquareKit.Cubical.Cartesian StructureIdentity.Native StructuredIdentity
variable {Γ : Context.{1}} {X Y : Type} [Lattice X] [Lattice Y]

/-- The carrier is admitted using its actual discrete filling and small presentation. -/
noncomputable def admission (X : Type) :
    SmallUniverse.LargeConstructors.Result (constantFamily Γ (ULift.{1} X)) :=
  SmallUniverse.LargeConstructors.construct
    ⟨fun _ => X, fun _ => Equiv.ulift.symm⟩
    (presentedFilling (Iso.refl _)) (presentedFilling_lawful (Iso.refl _))

variable (a : SmallUniverse.LargeConstructors.Result (constantFamily Γ (ULift.{1} X)))
  (b : SmallUniverse.LargeConstructors.Result (constantFamily Γ (ULift.{1} Y)))

noncomputable def fields : Term (family rawLattice (SmallUniverse.liftedDecode a.code)) :=
  Term.map (presentedIso rawLattice a.decoding).inv
    ⟨fun _ => ⟨(latticeModel X).val⟩, fun _ => rfl⟩

theorem fields_decode (x : Γ.Elements) :
    decode rawLattice a.decoding x ((fields a).val x) = (latticeModel X).val :=
  decode_presentedIso_inv rawLattice a.decoding x _

noncomputable def carrier (e : X ≃o Y) := presentedCarrierIso a.decoding b.decoding e.toEquiv

noncomputable def movedFields (e : X ≃o Y) :=
  Term.map (actionIso rawLattice (carrier a b e)).hom (fields a)

theorem movedFields_decode (e : X ≃o Y) (x : Γ.Elements) :
    decode rawLattice b.decoding x ((movedFields a b e).val x) = (latticeModel Y).val := by
  rw [show (movedFields a b e).val x =
    (actionIso rawLattice (presentedCarrierIso a.decoding b.decoding e.toEquiv)).hom.app x
      ((fields a).val x) from rfl,
    decode_action _ _ _ _ _ (decode_presentedCarrierIso _ _ _), fields_decode]
  exact congrArg Subtype.val (orderIso_transport e)

/-- Discrete presentation proves native sethood of the decoded carrier. -/
noncomputable def carrierSet : Term (HomotopyLevels.isSet (SmallUniverse.liftedDecode a.code)) := by
  apply lam
  apply lam
  let A := SmallUniverse.liftedDecode a.code
  let σ := projection (reindex A (projection A)) ≫ projection A
  exact HomotopyLevels.ofSubsingleton _ (fun x =>
    (presentedPathEquiv (reindexPresented a.decoding σ)
      (Term.reindex (generic A) (projection (reindex A (projection A))))
      (generic (reindex A (projection A))) x).injective.subsingleton)

noncomputable def laws (s : Term (family rawLattice (SmallUniverse.liftedDecode a.code)))
    (hs : ∀ x, decode rawLattice a.decoding x (s.val x) = (latticeModel X).val) :
    Term (lawFamily lattice.law s unitContext) :=
  Term.map (presentedLawIso lattice.law a.decoding s unitContext).inv
    ⟨fun x => ⟨⟨by
      change lattice.law.Eval (C := .fixed Unit) (decode rawLattice a.decoding x (s.val x)) ()
      rw [hs x]
      exact (latticeModel X).property⟩⟩,
      fun _ => by apply ULift.ext; apply Subsingleton.elim⟩

noncomputable def sourceObject : Term (modelObjects lattice Γ) :=
  modelObject lattice a.code (fields a) (carrierSet a) (laws a (fields a) (fields_decode a))

noncomputable def targetObject (e : X ≃o Y) : Term (modelObjects lattice Γ) :=
  modelObject lattice b.code (movedFields a b e) (carrierSet b)
    (laws b (movedFields a b e) (movedFields_decode a b e))

noncomputable def preservation (e : X ≃o Y) :
    Term (preserves rawLattice (carrier a b e).hom (carrier a b e).inv
      (fields a) (movedFields a b e)) :=
  Term.map (preservesActionPathIso rawLattice (carrier a b e) (fields a) _).inv
    (homogeneousRefl (movedFields a b e))

noncomputable def structuredEquivalence (e : X ≃o Y) :
    Term (equivalences rawLattice (fields a) (movedFields a b e)) := by
  let k := carrier a b e
  let E := HomotopyEquivalence.ofIso k
    (SmallUniverse.NativeDecode.filling b.code) (SmallUniverse.NativeDecode.filling_lawful b.code)
  refine sigmaIntro (EquivalenceFamilies.equivSections _ _ ⟨k.hom, E⟩)
    (Term.map (suppliedEquivalenceFiberIso rawLattice k.hom E (fields a) (movedFields a b e)).inv ?_)
  exact preservation a b e

noncomputable def rawPath (e : X ≃o Y) :=
  Term.map (UaComparison.explicitMap rawLattice a.code (fields a) b.code (movedFields a b e))
    (structuredEquivalence a b e)

/-- The native law-bearing lattice path is built from the selected ua construction. -/
noncomputable def latticePath (e : X ≃o Y) :
    Term (homogeneousPath (modelObjects lattice Γ) (sourceObject a) (targetObject a b e)) :=
  Term.map (UaComparison.modelPathInverse lattice (sourceObject a) (targetObject a b e))
    (rawPath a b e)

noncomputable def latticePathProjection (e : X ≃o Y) :=
  UaComparison.modelPathInverseProjection lattice (sourceObject a) (targetObject a b e)
    (rawPath a b e)

noncomputable def latticePathRoundtrip (e : X ≃o Y) :=
  UaComparison.modelRightInverseAt lattice (sourceObject a) (targetObject a b e) (latticePath a b e)

noncomputable def equivalenceRoundtrip (e : X ≃o Y) :=
  UaComparison.explicitLeftInverseAt rawLattice a.code (fields a) b.code (movedFields a b e)
    (structuredEquivalence a b e)

theorem rawPath_carrier (e : X ≃o Y) :
    let E := (EquivalenceFamilies.equivSections _ _).symm
      (sigmaFst (structuredEquivalence a b e))
    Term.map (HomotopyLevels.pathMap (SIP.Exchange.first (SIP.objectFields rawLattice))
      (objectOf rawLattice a.code (fields a)) (objectOf rawLattice b.code (movedFields a b e)))
      (rawPath a b e) = SmallUniverse.NativeUnivalence.ua a.code b.code E.1 E.2 :=
  UaComparison.explicitMap_carrier_ua rawLattice a.code (fields a) b.code (movedFields a b e)
    (structuredEquivalence a b e)

noncomputable def orderedWitness (p : OrderedPair X) (x : Γ.Elements) :
    (solutionsFamily comparablePair (fields a)).obj x :=
  (presentedSolutionsEquiv comparablePair a.decoding (fields a) x).symm
    ⟨⟨p.val, by
      rw [fields_decode]
      exact (show p.val.1 ⊓ p.val.2 = p.val.1 from inf_eq_left.mpr p.property)⟩⟩

noncomputable def movedWitness (e : X ≃o Y) (p : OrderedPair X) (x : Γ.Elements) :=
  presentedSolutionsTransport comparablePair a.decoding b.decoding e.toEquiv (fields a) x
    (orderedWitness a p x)

theorem movedWitness_data (e : X ≃o Y) (p : OrderedPair X) (x : Γ.Elements) :
    decode (.product .carrier .carrier) b.decoding x (movedWitness a b e p x).1 =
      (directTransport e p).val := by
  unfold movedWitness
  rw [presentedSolutionsTransport_data,
    decode_action _ _ _ _ _ (decode_presentedCarrierIso _ _ _)]
  have h := congrArg (fun z => z.down.val)
    ((presentedSolutionsEquiv comparablePair a.decoding (fields a) x).apply_symm_apply
      (⟨⟨p.val, by rw [fields_decode]; exact (show p.val.1 ⊓ p.val.2 = p.val.1 from inf_eq_left.mpr p.property)⟩⟩))
  change decode (.product .carrier .carrier) a.decoding x (orderedWitness a p x).1 = p.val at h
  rw [h]
  rfl

noncomputable def readMovedWitness (e : X ≃o Y) (p : OrderedPair X) (x : Γ.Elements) : OrderedPair Y :=
  ⟨decode (.product .carrier .carrier) b.decoding x (movedWitness a b e p x).1, by
    have h := (presentedSolutionsEquiv comparablePair b.decoding (movedFields a b e) x
      (movedWitness a b e p x)).down.property
    change comparablePair.Eval (decode rawLattice b.decoding x ((movedFields a b e).val x))
      (decode (.product .carrier .carrier) b.decoding x (movedWitness a b e p x).1) at h
    rw [movedFields_decode] at h
    exact inf_eq_left.mp h⟩

theorem native_direct (e : X ≃o Y) (p : OrderedPair X) (x : Γ.Elements) :
    readMovedWitness a b e p x = directTransport e p :=
  Subtype.ext (movedWitness_data a b e p x)

theorem movedFields_meet (e : X ≃o Y) (x : Γ.Elements) (u v : Y) :
    (decode rawLattice b.decoding x ((movedFields a b e).val x)).1 u v = u ⊓ v := by
  rw [movedFields_decode]; rfl

theorem movedFields_join (e : X ≃o Y) (x : Γ.Elements) (u v : Y) :
    (decode rawLattice b.decoding x ((movedFields a b e).val x)).2 u v = u ⊔ v := by
  rw [movedFields_decode]; rfl

theorem movedWitness_recovery (e : X ≃o Y) (p : OrderedPair X) (x : Γ.Elements) :
    (presentedSolutionsTransport comparablePair a.decoding b.decoding e.toEquiv (fields a) x).symm
      (movedWitness a b e p x) = orderedWitness a p x :=
  (presentedSolutionsTransport comparablePair a.decoding b.decoding e.toEquiv (fields a) x).symm_apply_apply _

/-- The independently defined preservation family rejects the bad bijection. -/
theorem bad_preservation_rejected
    (c : SmallUniverse.LargeConstructors.Result (constantFamily Γ (ULift.{1} (Bool × Bool))))
    (x : Γ.Elements) :
    ¬ Nonempty ((preserves rawLattice
      (presentedCarrierIso c.decoding c.decoding badBijection).hom
      (presentedCarrierIso c.decoding c.decoding badBijection).inv (fields c) (fields c)).obj x) := by
  rintro ⟨h⟩
  have hp := ((presentedPreservationEquiv rawLattice c.decoding c.decoding badBijection
    (fields c) (fields c) x) h).down.down
  rw [fields_decode] at hp
  exact badBijection_rejected hp

/-- The selected raw structure path projected to its universe carrier. -/
noncomputable def carrierPath (e : X ≃o Y) :=
  Term.map (HomotopyLevels.pathMap (SIP.Exchange.first (SIP.objectFields rawLattice))
    (objectOf rawLattice a.code (fields a)) (objectOf rawLattice b.code (movedFields a b e)))
    (rawPath a b e)
noncomputable def point (v : X) : Term (SmallUniverse.liftedDecode a.code) :=
  Term.map a.decoding.inv ⟨fun _ => ⟨v⟩, fun _ => rfl⟩
noncomputable def transportedPoint (e : X ≃o Y) (v : X) :=
  Term.map (SmallUniverse.NativeUnivalence.pathToMap (carrierPath a b e)) (point a v)
theorem point_carrier_decode (e : X ≃o Y) (v : X) (x : Γ.Elements) :
    (b.decoding.hom.app x ((Term.map (carrier a b e).hom (point a v)).val x)).down = e v :=
  (decode_presentedCarrierIso a.decoding b.decoding e.toEquiv x ((point a v).val x)).trans
    (congrArg e (congrArg ULift.down (a.decoding.inv_hom_id_app_apply x ⟨v⟩)))
theorem selected_map (e : X ≃o Y) :
    ((EquivalenceFamilies.equivSections _ _).symm (sigmaFst (structuredEquivalence a b e))).1 =
      (carrier a b e).hom :=
  congrArg Sigma.fst ((EquivalenceFamilies.equivSections _ _).symm_apply_apply _)
omit [Lattice X] [Lattice Y] in
theorem ua_decode (f : SmallUniverse.liftedDecode a.code ⟶ SmallUniverse.liftedDecode b.code)
    (E : HomotopyEquivalence f) (v : X) (x : Γ.Elements) :
    (b.decoding.hom.app x ((Term.map (SmallUniverse.NativeUnivalence.pathToMap
      (SmallUniverse.NativeUnivalence.ua a.code b.code f E)) (point a v)).val x)).down =
    (b.decoding.hom.app x ((Term.map f (point a v)).val x)).down := by
  let h := SmallUniverse.NativeUnivalence.uaComparison a.code b.code f E (point a v)
  exact (((presentedPathEquiv b.decoding _ _ x) (h.val x)).down.down).symm
theorem transportedPoint_decode (e : X ≃o Y) (v : X) (x : Γ.Elements) :
    (b.decoding.hom.app x ((transportedPoint a b e v).val x)).down = e v := by
  let E := (EquivalenceFamilies.equivSections _ _).symm (sigmaFst (structuredEquivalence a b e))
  let observe (f : SmallUniverse.liftedDecode a.code ⟶ SmallUniverse.liftedDecode b.code) :=
    (b.decoding.hom.app x ((Term.map f (point a v)).val x)).down
  have hpath : observe (SmallUniverse.NativeUnivalence.pathToMap (carrierPath a b e)) =
      observe (SmallUniverse.NativeUnivalence.pathToMap (SmallUniverse.NativeUnivalence.ua a.code b.code E.1 E.2)) :=
    congrArg (fun (p : Term (SmallUniverse.NativeUnivalence.paths a.code b.code)) =>
      observe (SmallUniverse.NativeUnivalence.pathToMap p)) (rawPath_carrier a b e)
  exact hpath.trans ((ua_decode a b E.1 E.2 v x).trans
    ((congrArg observe (selected_map a b e)).trans (point_carrier_decode a b e v x)))
/-- Project the actual law-bearing lattice path to the universe. -/
noncomputable def latticeCarrierPath (e : X ≃o Y) :=
  Term.map (HomotopyLevels.pathMap (SIP.Exchange.first (SIP.objectFields rawLattice))
    (objectOf rawLattice a.code (fields a)) (objectOf rawLattice b.code (movedFields a b e)))
    (Term.map (HomotopyLevels.pathMap (PropositionExtension.first (objectConditions lattice Γ))
      (sourceObject a) (targetObject a b e)) (latticePath a b e))
/-- The law-bearing projection recovers the selected raw carrier path by a native two-path. -/
noncomputable def carrierProjection (e : X ≃o Y) :
    Term (homogeneousPath (SmallUniverse.NativeUnivalence.paths a.code b.code)
      (latticeCarrierPath a b e) (carrierPath a b e)) :=
  homogeneousPathMap (HomotopyLevels.pathMap (SIP.Exchange.first (SIP.objectFields rawLattice))
    (objectOf rawLattice a.code (fields a)) (objectOf rawLattice b.code (movedFields a b e)))
    (latticePathProjection a b e)

omit [Lattice X] [Lattice Y] in
noncomputable def evaluatePath (v : X) :
    SmallUniverse.NativeUnivalence.paths a.code b.code ⟶ SmallUniverse.liftedDecode b.code :=
  SmallUniverse.NativeUnivalence.pathToEquiv a.code b.code ≫ EquivalenceFamilies.evaluate (point a v)
omit [Lattice X] [Lattice Y] in
theorem evaluatePath_beta (v : X) (p : Term (SmallUniverse.NativeUnivalence.paths a.code b.code)) :
    Term.map (evaluatePath a b v) p = Term.map (SmallUniverse.NativeUnivalence.pathToMap p) (point a v) := by
  change Term.map (EquivalenceFamilies.evaluate (point a v))
    (Term.map (SmallUniverse.NativeUnivalence.pathToEquiv a.code b.code) p) = _
  rw [← SmallUniverse.NativeUnivalence.pathToEquiv_beta]
  apply Term.ext
  intro x
  rfl

/-- Actual universal-decoder transport along the law-bearing path projection. -/
noncomputable def latticeTransportedPoint (e : X ≃o Y) (v : X) :=
  Term.map (SmallUniverse.NativeUnivalence.pathToMap (latticeCarrierPath a b e)) (point a v)
theorem latticeTransportedPoint_decode (e : X ≃o Y) (v : X) (x : Γ.Elements) :
    (b.decoding.hom.app x ((latticeTransportedPoint a b e v).val x)).down = e v := by
  let h := homogeneousPathMap (evaluatePath a b v) (carrierProjection a b e)
  have hd := ((presentedPathEquiv b.decoding _ _ x) (h.val x)).down.down
  let observe (t : Term (SmallUniverse.liftedDecode b.code)) := (b.decoding.hom.app x (t.val x)).down
  exact (congrArg observe (evaluatePath_beta a b v (latticeCarrierPath a b e))).symm.trans
    (hd.trans ((congrArg observe (evaluatePath_beta a b v (carrierPath a b e))).trans
      (transportedPoint_decode a b e v x)))
/-- Transport both values along the native path and reconstruct their admitted order proof. -/
noncomputable def pathOrderedPair (e : X ≃o Y) (p : OrderedPair X) (x : Γ.Elements) : OrderedPair Y :=
  ⟨((b.decoding.hom.app x ((latticeTransportedPoint a b e p.val.1).val x)).down,
    (b.decoding.hom.app x ((latticeTransportedPoint a b e p.val.2).val x)).down), by
      rw [latticeTransportedPoint_decode, latticeTransportedPoint_decode]
      exact e.monotone p.property⟩
theorem pathOrderedPair_direct (e : X ≃o Y) (p : OrderedPair X) (x : Γ.Elements) :
    pathOrderedPair a b e p x = directTransport e p := by
  apply Subtype.ext
  exact Prod.ext (latticeTransportedPoint_decode a b e p.val.1 x)
    (latticeTransportedPoint_decode a b e p.val.2 x)
/-- Recover the complete native solution from the actual path-transported values. -/
noncomputable def pathSolution (e : X ≃o Y) (p : OrderedPair X) (x : Γ.Elements) :
    (solutionsFamily comparablePair (movedFields a b e)).obj x :=
  (presentedSolutionsEquiv comparablePair b.decoding (movedFields a b e) x).symm
    ⟨⟨(pathOrderedPair a b e p x).val, by
      rw [movedFields_decode]
      exact (show (pathOrderedPair a b e p x).val.1 ⊓ (pathOrderedPair a b e p x).val.2 =
        (pathOrderedPair a b e p x).val.1 from inf_eq_left.mpr (pathOrderedPair a b e p x).property)⟩⟩
theorem pathSolution_moved (e : X ≃o Y) (p : OrderedPair X) (x : Γ.Elements) :
    pathSolution a b e p x = movedWitness a b e p x := by
  apply (presentedSolutionsEquiv comparablePair b.decoding (movedFields a b e) x).injective
  unfold pathSolution
  rw [Equiv.apply_symm_apply]
  apply ULift.ext
  apply Subtype.ext
  exact (congrArg Subtype.val (pathOrderedPair_direct a b e p x)).trans (movedWitness_data a b e p x).symm


/-- Keep both endpoints with their actual native path, so concrete clients need
not repeatedly normalize a deeply dependent result type. -/
structure PathData {Γ : Context.{1}} (A : Family Γ) where
  source : Term A
  target : Term A
  path : Term (homogeneousPath A source target)

def PathData.ofPath {Γ : Context.{1}} {A : Family Γ} {s t : Term A}
    (p : Term (homogeneousPath A s t)) : PathData A := ⟨s, t, p⟩

/-- A computational boundary around the existing law-bearing path, with no new
choice of path or equivalence. -/
noncomputable def latticePathData (e : X ≃o Y) :=
  PathData.ofPath (latticePath a b e)

theorem latticePathData_source (e : X ≃o Y) :
    (latticePathData a b e).source = sourceObject a := rfl

theorem latticePathData_target (e : X ≃o Y) :
    (latticePathData a b e).target = targetObject a b e := rfl

theorem latticePathData_path (e : X ≃o Y) :
    (latticePathData a b e).path = latticePath a b e := rfl

/-- Retain the complete selected equivalence and its native recovery path. -/
noncomputable def equivalenceRecoveryData (e : X ≃o Y) :=
  PathData.ofPath (equivalenceRoundtrip a b e)

theorem equivalenceRecoveryData_target (e : X ≃o Y) :
    (equivalenceRecoveryData a b e).target = structuredEquivalence a b e := rfl

/-- The law-bearing path still projects to the original raw path by the same
native two-path. -/
noncomputable def latticeProjectionData (e : X ≃o Y) :=
  PathData.ofPath (latticePathProjection a b e)

end Cartesian
end Examples.NativeLatticeTransport

import Examples.CubicalStructuredState
import Examples.CompositionalUnivalence
import SquareKit.Internal.Cubical.ConstructorTransport

/-! Nonreflexive constructor transport for a dependent state-indexed finite
field. The function observation distinguishes backward, forward and unchanged
argument transport. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalConstructorState
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open CubicalStatePackageUa CubicalStateTransport CubicalUnivalenceTransport CubicalGlue
open SmallUniverse

abbrev Ξ := raisedContext terminal.{0}
noncomputable def carrierPath := Univalence.ua (constantLocal terminal Int).code
  (constantLocal terminal Int).code (codeIso successor).hom (HomotopyEquivalence.ofIso (codeIso successor))
noncomputable abbrev a := LargeConstructors.inputLine carrierPath
noncomputable abbrev A := liftedDecode a

noncomputable def linePresentation : A ≅ constantFamily (total (interval Ξ)) (ULift.{1} Int) :=
  Functor.isoWhiskerLeft (raisedIntervalIso terminal).inv.mapElements (Raising.iso successorLineIso)

noncomputable def smallIndex : Term (constantFamily (total successorLine.family) Int) :=
  Term.map (Functor.whiskerLeft (projection successorLine.family).mapElements successorLineIso.hom)
    (generic successorLine.family)

noncomputable def smallField : LocalFamily (total successorLine.family) :=
  LocalFamily.discrete smallIndex (fun n => Fin (n.natAbs + 1))

noncomputable def display : total A ⟶ raisedContext (total successorLine.family) :=
  liftSub (Raising.family successorLine.family) (raisedIntervalIso terminal).inv ≫
    (Raising.totalIso successorLine.family).inv

noncomputable def b : total A ⟶ smallFamilyCodes.{0} := display ≫ smallField.code
noncomputable abbrev B := liftedDecode b

noncomputable def fieldPresentation : B ≅
    reindex (Raising.family smallField.family) display :=
  Functor.isoWhiskerLeft display.mapElements (Raising.iso smallField.decodeCodeIso)

private def numericValue (n : Int) : Fin (n.natAbs + 1) := ⟨n.natAbs - 1, by omega⟩
private theorem cast_numericValue (n m : Int) (h : n = m) :
    cast (congrArg (fun k : Int => Fin (k.natAbs + 1)) h) (numericValue n) = numericValue m := by
  cases h
  rfl
private theorem cast_numericVal (n m : Int) (h : n = m) (z : Fin (n.natAbs + 1)) :
    (cast (congrArg (fun k : Int => Fin (k.natAbs + 1)) h) z).val = z.val := by
  cases h
  rfl

noncomputable def smallValue : Term smallField.family where
  val x := numericValue (smallIndex.val x)
  property f := cast_numericValue _ _ (smallIndex.property f)

noncomputable def fieldSection : Term B :=
  Term.map fieldPresentation.inv ((Raising.raiseTerm smallValue).reindex display)

noncomputable def argument (n : Int) : Term A :=
  Term.map linePresentation.inv (⟨fun _ => ⟨n⟩, fun _ => rfl⟩ : Term (constantFamily _ (ULift.{1} Int)))

noncomputable def suppliedPair : Term (Presheaf.sigma A B) :=
  sigmaIntro (argument 4) (fieldSection.reindex (pair (𝟙 _) (argument 4)))
noncomputable def suppliedFunction : Term (Presheaf.pi A B) := lam fieldSection
noncomputable def initialPair := suppliedPair.reindex (endpointSub Ξ false)
noncomputable def initialFunction := suppliedFunction.reindex (endpointSub Ξ false)
noncomputable def pairComparison := LargeConstructors.pairAlongPath carrierPath b initialPair
noncomputable def functionComparison := LargeConstructors.functionAlongPath carrierPath b initialFunction
noncomputable def filledPair := LargeConstructors.pairSection a b initialPair
noncomputable def filledFunction := LargeConstructors.functionSection a b initialFunction

/-- Natural numeric observation of the varying finite fiber. -/
noncomputable def smallObserve : smallField.family ⟶ constantFamily (total successorLine.family) Nat where
  app _ := TypeCat.ofHom Fin.val
  naturality x y f := by
    apply ConcreteCategory.hom_ext
    intro z
    exact cast_numericVal _ _ (smallIndex.property f) z

noncomputable def fieldObserve : B ⟶ constantFamily (total A) (ULift.{1} Nat) :=
  fieldPresentation.hom ≫ Functor.whiskerLeft display.mapElements (Raising.map smallObserve)

private def sigmaObserve {Γ : Context.{1}} {C : Family Γ} {D : Family (total C)}
    (o : D ⟶ constantFamily (total C) (ULift.{1} Nat)) :
    Presheaf.sigma C D ⟶ constantFamily Γ (ULift.{1} Nat) where
  app x := TypeCat.ofHom (fun z => o.app (extendObj C x z.1) z.2)
  naturality x y f := by
    apply ConcreteCategory.hom_ext
    intro z
    exact o.naturality_apply (extendHom C f z.1) z.2

private def piObserve {Γ : Context.{1}} {C : Family Γ} {D : Family (total C)}
    (o : D ⟶ constantFamily (total C) (ULift.{1} Nat)) (v : Term C) :
    Presheaf.pi C D ⟶ constantFamily Γ (ULift.{1} Nat) where
  app x := TypeCat.ofHom (fun z => o.app (extendObj C x (v.val x)) (z.val (𝟙 x) (v.val x)))
  naturality x y f := by
    apply ConcreteCategory.hom_ext
    intro z
    have hn := z.naturality (𝟙 x) f (v.val x)
    have ho := o.naturality_apply (extendHom C f (v.val x)) (z.val (𝟙 x) (v.val x))
    change o.app (extendObj C y (C.map f (v.val x)))
      (D.map (extendHom C f (v.val x)) (z.val (𝟙 x) (v.val x))) = _ at ho
    rw [hn] at ho
    have hc : 𝟙 x ≫ f = f ≫ 𝟙 y := (Category.id_comp f).trans (Category.comp_id f).symm
    rw [hc] at ho
    change o.app (extendObj C y (v.val y)) (z.val (f ≫ 𝟙 y) (v.val y)) = _
    exact (congrArg (fun a => o.app (extendObj C y a) (z.val (f ≫ 𝟙 y) a)) (v.property f)).symm.trans ho

noncomputable def pairObserve := sigmaObserve fieldObserve
noncomputable def functionObserve (n : Int) := piObserve fieldObserve (argument n)

def point : Ξ.Elements := Ξ.elementsMk (Opposite.op ⟨0⟩) ⟨PUnit.unit⟩
def atEnd (ε : Bool) : (total (interval Ξ)).Elements := (endpointSub Ξ ε).mapElements.obj point

/-- A constant observation of a section is determined by its initial endpoint. -/
theorem observe_filling {V : Type 1} {C : Family (total (interval Ξ))}
    (o : C ⟶ constantFamily (total (interval Ξ)) V)
    (s t : Term C) (h : s.reindex (endpointSub Ξ false) = t.reindex (endpointSub Ξ false)) :
    (Term.map o s).val (atEnd true) = (Term.map o t).val (atEnd true) := by
  calc
    _ = (Term.map o s).val (atEnd false) := constant_section_interval _ point ((endpoint Ξ true).val point) ((endpoint Ξ false).val point)
    _ = (Term.map o t).val (atEnd false) := congrArg (o.app (atEnd false)) (congrArg (fun z => z.val point) h)
    _ = _ := constant_section_interval _ point ((endpoint Ξ false).val point) ((endpoint Ξ true).val point)

end Examples.CubicalConstructorState

namespace Examples.CubicalConstructorState
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open CubicalStatePackageUa CubicalStateTransport CubicalUnivalenceTransport CubicalGlue
open SmallUniverse SmallUniverse.NativeUnivalence

noncomputable def unglue : A ⟶ reindex (liftedDecode (constantLocal terminal Int).code) (projection (interval Ξ)) :=
  Functor.whiskerLeft (raisedIntervalIso terminal).inv.mapElements
    (Raising.map (Univalence.unglueLine _ _ (codeIso successor).hom (HomotopyEquivalence.ofIso (codeIso successor))))

private theorem raise_cast {Γ : Context.{0}} {C D : Family Γ} (h : C = D) :
    Raising.map (eqToHom h) = eqToHom (congrArg Raising.family h) := by
  cases h
  rfl
private theorem raise_comp {Γ : Context.{0}} {C D F : Family Γ} (f : C ⟶ D) (g : D ⟶ F) :
    Raising.map (f ≫ g) = Raising.map f ≫ Raising.map g := rfl

set_option backward.isDefEq.respectTransparency false in
theorem unglue_zero : Functor.whiskerLeft (endpointSub Ξ false).mapElements unglue =
    eqToHom (decode_zero carrierPath) ≫ CompositionalUnivalence.nativeMap successor := by
  have h := congrArg Raising.map
    (Univalence.unglueLine_zero _ _ (codeIso successor).hom (HomotopyEquivalence.ofIso (codeIso successor)))
  rw [raise_comp, raise_cast] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem unglue_one : Functor.whiskerLeft (endpointSub Ξ true).mapElements unglue =
    eqToHom (decode_one carrierPath) := by
  have h := congrArg Raising.map
    (Univalence.unglueLine_one _ _ (codeIso successor).hom (HomotopyEquivalence.ofIso (codeIso successor)))
  rw [raise_cast] at h
  exact h

noncomputable def carrierComparison (n : Int) :=
  IntervalTransport.mapLineComparisonTo (NativeDecode.filling a) (NativeDecode.filling_lawful a)
    (decode_zero carrierPath) (decode_one carrierPath) unglue
    (CompositionalUnivalence.nativeMap successor) unglue_zero unglue_one
    (CompositionalUnivalence.nativeInput n)

/-- Observation distinguishes the actual supplied native ua path from reflexivity. -/
theorem carrierPath_nonreflexive : carrierPath ≠ homogeneousRefl (term (constantLocal terminal Int).code) := by
  intro h
  have ht := CompositionalUnivalence.observe_path (carrierComparison 3)
  have hr := CompositionalUnivalence.observe_path (reflexiveTransportComparison
    (constantLocal terminal Int).code (CompositionalUnivalence.nativeInput 3))
  have hm := congrArg (fun p : Term (paths (constantLocal terminal Int).code (constantLocal terminal Int).code) =>
    CompositionalUnivalence.observe (Term.map (pathToMap p) (CompositionalUnivalence.nativeInput 3))) h
  have hf := (congrArg CompositionalUnivalence.observe
    (CompositionalUnivalence.nativeInput_action successor 3)).trans (CompositionalUnivalence.observe_input 4)
  have bad : constantSection (4 : Int) = constantSection 3 :=
    hf.symm.trans (ht.trans (hm.trans (hr.trans (CompositionalUnivalence.observe_input 3))))
  have hv := congrArg (fun t => t.val CubicalStatePackageUa.point) bad
  change (4 : Int) = 3 at hv
  omega

end Examples.CubicalConstructorState

namespace Examples.CubicalConstructorState
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open CubicalStatePackageUa CubicalStateTransport CubicalUnivalenceTransport CubicalGlue
open SmallUniverse

private theorem iso_apply_inv {Γ : Context.{1}} {C D : Family Γ}
    (j : C ≅ D) (x : Γ.Elements) (z : D.obj x) : j.hom.app x (j.inv.app x z) = z :=
  congrArg (fun k => k.app x z) j.inv_hom_id

/-- Observation after the actual dependent-field decoder, at every generalized point. -/
theorem fieldSection_observation (x : (total A).Elements) :
    (fieldObserve.app x (fieldSection.val x)).down =
      ((linePresentation.hom.app ((projection A).mapElements.obj x) x.val.2).down).natAbs - 1 := by
  change ((fieldPresentation.hom.app x (fieldPresentation.inv.app x
    (((Raising.raiseTerm smallValue).reindex display).val x))).down).val = _
  rw [iso_apply_inv]
  rfl

theorem argument_observation (n : Int) (x : (total (interval Ξ)).Elements) :
    linePresentation.hom.app x ((argument n).val x) = ⟨n⟩ :=
  iso_apply_inv linePresentation x ⟨n⟩

theorem field_argument (n : Int) (x : (total (interval Ξ)).Elements) :
    (fieldObserve.app (extendObj A x ((argument n).val x))
      (fieldSection.val (extendObj A x ((argument n).val x)))).down = n.natAbs - 1 := by
  rw [fieldSection_observation]
  exact congrArg (fun z : ULift.{1} Int => z.down.natAbs - 1) (argument_observation n x)

theorem suppliedPair_observation : (Term.map pairObserve suppliedPair).val (atEnd true) = ⟨3⟩ :=
  ULift.ext (field_argument 4 (atEnd true))

theorem suppliedFunction_observation (n : Int) :
    (Term.map (functionObserve n) suppliedFunction).val (atEnd true) = ⟨n.natAbs - 1⟩ :=
  ULift.ext (field_argument n (atEnd true))

theorem filledPair_observation : (Term.map pairObserve filledPair).val (atEnd true) = ⟨3⟩ :=
  (observe_filling pairObserve filledPair suppliedPair (LargeConstructors.pairSection_zero a b initialPair)).trans
    suppliedPair_observation

theorem filledFunction_observation : (Term.map (functionObserve 4) filledFunction).val (atEnd true) = ⟨3⟩ :=
  (observe_filling (functionObserve 4) filledFunction suppliedFunction
    (LargeConstructors.functionSection_zero a b initialFunction)).trans (suppliedFunction_observation 4)

noncomputable def pairResult := LargeConstructors.sigma a b
noncomputable def functionResult := LargeConstructors.pi a b
noncomputable def pairTransported := Term.map (IntervalTransport.map (NativeDecode.filling pairResult.code))
  (Term.map (Functor.whiskerLeft (endpointSub Ξ false).mapElements pairResult.decoding.inv) initialPair)
noncomputable def functionTransported := Term.map (IntervalTransport.map (NativeDecode.filling functionResult.code))
  (Term.map (Functor.whiskerLeft (endpointSub Ξ false).mapElements functionResult.decoding.inv) initialFunction)
noncomputable def pairOutput := Term.map
  (Functor.whiskerLeft (endpointSub Ξ true).mapElements (pairResult.decoding.hom ≫ pairObserve)) pairTransported
noncomputable def functionOutput := Term.map
  (Functor.whiskerLeft (endpointSub Ξ true).mapElements (functionResult.decoding.hom ≫ functionObserve 4)) functionTransported

private theorem decoded_observation {V : Type 1} {Γ : Context.{1}} {C D : Family Γ}
    (j : C ≅ D) (o : D ⟶ constantFamily Γ V)
    (s : Term C) (t : Term D) (p : Term (homogeneousPath C s (Term.map j.inv t))) :
    Term.map (j.hom ≫ o) s = Term.map o t := by
  have h := constantFamily_path_endpoints (homogeneousPathMap (j.hom ≫ o) p)
  have hr := Term.map_iso_roundtrip j.symm t
  exact h.trans (congrArg (Term.map o) hr)

private theorem pair_path_observation {V : Type 1} {Ω : Context.{1}}
    {a₀ a₁ : Ω ⟶ smallFamilyCodes.{0}} (p : Term (NativeUnivalence.paths a₀ a₁))
    (d : total (liftedDecode (LargeConstructors.inputLine p)) ⟶ smallFamilyCodes.{0})
    (z : Term (reindex (Presheaf.sigma (liftedDecode (LargeConstructors.inputLine p)) (liftedDecode d))
      (endpointSub Ω false)))
    (o : Presheaf.sigma (liftedDecode (LargeConstructors.inputLine p)) (liftedDecode d) ⟶
      constantFamily (total (interval Ω)) V) :
    let R := LargeConstructors.sigma (LargeConstructors.inputLine p) d
    Term.map (Functor.whiskerLeft (endpointSub Ω true).mapElements (R.decoding.hom ≫ o))
      (Term.map (IntervalTransport.map (NativeDecode.filling R.code))
        (Term.map (Functor.whiskerLeft (endpointSub Ω false).mapElements R.decoding.inv) z)) =
    (Term.map o (LargeConstructors.pairSection (LargeConstructors.inputLine p) d z)).reindex
      (endpointSub Ω true) := by
  exact decoded_observation
    (Functor.isoWhiskerLeft (endpointSub Ω true).mapElements (LargeConstructors.sigma _ d).decoding)
    (Functor.whiskerLeft (endpointSub Ω true).mapElements o) _ _
    (LargeConstructors.pairAlongPath p d z)

private theorem function_path_observation {V : Type 1} {Ω : Context.{1}}
    {a₀ a₁ : Ω ⟶ smallFamilyCodes.{0}} (p : Term (NativeUnivalence.paths a₀ a₁))
    (d : total (liftedDecode (LargeConstructors.inputLine p)) ⟶ smallFamilyCodes.{0})
    (z : Term (reindex (Presheaf.pi (liftedDecode (LargeConstructors.inputLine p)) (liftedDecode d))
      (endpointSub Ω false)))
    (o : Presheaf.pi (liftedDecode (LargeConstructors.inputLine p)) (liftedDecode d) ⟶
      constantFamily (total (interval Ω)) V) :
    let R := LargeConstructors.pi (LargeConstructors.inputLine p) d
    Term.map (Functor.whiskerLeft (endpointSub Ω true).mapElements (R.decoding.hom ≫ o))
      (Term.map (IntervalTransport.map (NativeDecode.filling R.code))
        (Term.map (Functor.whiskerLeft (endpointSub Ω false).mapElements R.decoding.inv) z)) =
    (Term.map o (LargeConstructors.functionSection (LargeConstructors.inputLine p) d z)).reindex
      (endpointSub Ω true) := by
  exact decoded_observation
    (Functor.isoWhiskerLeft (endpointSub Ω true).mapElements (LargeConstructors.pi _ d).decoding)
    (Functor.whiskerLeft (endpointSub Ω true).mapElements o) _ _
    (LargeConstructors.functionAlongPath p d z)

theorem pairOutput_observation : (pairOutput.val point).down = 3 := by
  have h := pair_path_observation carrierPath b initialPair pairObserve
  exact congrArg (fun t => (t.val point).down) h |>.trans (congrArg ULift.down filledPair_observation)

/-- The actual universal-decoder Π transport returns the original function at
its backward argument: target 4 reads source 3. -/
theorem functionOutput_observation : (functionOutput.val point).down = 3 := by
  have h := function_path_observation carrierPath b initialFunction (functionObserve 4)
  exact congrArg (fun t => (t.val point).down) h |>.trans (congrArg ULift.down filledFunction_observation)

/-- The endpoint carrier decoder sees the predecessor of the line coordinate. -/
theorem argument_start (n : Int) :
    startIso.hom.app CubicalStatePackageUa.point ((argument n).val (atEnd false)).down = n - 1 := by
  have he := congrArg (fun j => j.hom.app CubicalStatePackageUa.point
    ((argument n).val (atEnd false)).down) successorLineIso_zero
  have hn := congrArg ULift.down (argument_observation n (atEnd false))
  change successorLineIso.hom.app (endpointPoint false)
    ((argument n).val (atEnd false)).down = n at hn
  change successorLineIso.hom.app (endpointPoint false) _ =
    (show Int from startIso.hom.app CubicalStatePackageUa.point ((argument n).val (atEnd false)).down) + 1 at he
  have hv : (show Int from startIso.hom.app CubicalStatePackageUa.point
    ((argument n).val (atEnd false)).down) + 1 = n := he.symm.trans hn
  change (show Int from startIso.hom.app CubicalStatePackageUa.point
    ((argument n).val (atEnd false)).down) = n - 1
  omega

theorem argument_finish (n : Int) :
    finishIso.hom.app CubicalStatePackageUa.point ((argument n).val (atEnd true)).down = n := by
  have he := congrArg (fun j => j.hom.app CubicalStatePackageUa.point
    ((argument n).val (atEnd true)).down) successorLineIso_one
  exact he.symm.trans (congrArg ULift.down (argument_observation n (atEnd true)))

/-- Evaluate the actual initial function at source coordinate k, whose line
coordinate is k+1. `argument_start` checks this indexing through the decoder. -/
noncomputable def initialOutput (k : Int) : Nat :=
  ((Term.map (Functor.whiskerLeft (endpointSub Ξ false).mapElements
    (functionObserve (k + 1))) initialFunction).val point).down

theorem initialOutput_backward : initialOutput 3 = 3 := field_argument 4 (atEnd false)
theorem initialOutput_unchanged : initialOutput 4 = 4 := field_argument 5 (atEnd false)
theorem initialOutput_forward : initialOutput 5 = 5 := field_argument 6 (atEnd false)

/-- The numeric observation separates all three argument directions. -/
theorem function_direction_sensitive :
    (functionOutput.val point).down = initialOutput (successor.symm 4) ∧
    (functionOutput.val point).down ≠ initialOutput 4 ∧
    (functionOutput.val point).down ≠ initialOutput (successor 4) := by
  change (functionOutput.val point).down = initialOutput 3 ∧
    (functionOutput.val point).down ≠ initialOutput 4 ∧
    (functionOutput.val point).down ≠ initialOutput 5
  rw [functionOutput_observation, initialOutput_backward, initialOutput_unchanged, initialOutput_forward]
  decide

/-- The dependent decoder fiber has the cardinality prescribed by its state. -/
noncomputable def fieldFiber (n : Int) :
    B.obj (extendObj A (atEnd true) ((argument n).val (atEnd true))) ≃ Fin (n.natAbs + 1) :=
  (fieldPresentation.app _).toEquiv.trans (Equiv.ulift.trans
    (Equiv.cast (congrArg (fun z : ULift.{1} Int => Fin (z.down.natAbs + 1))
      (argument_observation n (atEnd true)))))

/-- The actual field has fibers of different cardinalities, so it is not a
constant codomain disguised as a dependent function. -/
theorem field_genuinely_dependent : ¬ Nonempty
    (B.obj (extendObj A (atEnd true) ((argument 0).val (atEnd true))) ≃
     B.obj (extendObj A (atEnd true) ((argument 1).val (atEnd true)))) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr ((fieldFiber 0).symm.trans (e.trans (fieldFiber 1)))
  simp at h

private def firstObservation {Γ : Context.{1}} {C : Family Γ} {D : Family (total C)}
    (j : C ⟶ constantFamily Γ (ULift.{1} Int)) :
    Presheaf.sigma C D ⟶ constantFamily Γ (ULift.{1} Int) where
  app x := TypeCat.ofHom (fun z => j.app x z.1)
  naturality x y f := by
    apply ConcreteCategory.hom_ext
    intro z
    exact j.naturality_apply f z.1

noncomputable def pairCarrierObserve := firstObservation (D := B) linePresentation.hom
noncomputable def pairCarrierOutput := Term.map
  (Functor.whiskerLeft (endpointSub Ξ true).mapElements (pairResult.decoding.hom ≫ pairCarrierObserve)) pairTransported

theorem pairCarrierOutput_observation : (pairCarrierOutput.val point).down = 4 := by
  have h := pair_path_observation carrierPath b initialPair pairCarrierObserve
  have hf := observe_filling pairCarrierObserve filledPair suppliedPair
    (LargeConstructors.pairSection_zero a b initialPair)
  have hs : (Term.map pairCarrierObserve suppliedPair).val (atEnd true) = ⟨4⟩ :=
    argument_observation 4 (atEnd true)
  exact congrArg (fun t => (t.val point).down) h |>.trans (congrArg ULift.down (hf.trans hs))

theorem pair_initial_carrier : startIso.hom.app CubicalStatePackageUa.point
    ((initialPair.val point).1).down = (3 : Int) := argument_start 4

end Examples.CubicalConstructorState

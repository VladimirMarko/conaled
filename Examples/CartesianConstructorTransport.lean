import SquareKit.Internal.Cubical.CartesianConstructorTransportSubstitution
import SquareKit.Internal.Cubical.CartesianClassifierComparison
import Examples.CartesianLargeFamilyConstructors

/-! Dependent constructors along independently selected Cartesian ua paths. The
target coordinate admits a varying finite family over the entire native line. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CartesianConstructorTransport
open CategoryTheory SquareKit.Cubical.Cartesian SmallUniverse LargeConstructors
open ClassifierComparison NativeNerve

abbrev three : FiniteCode := ⟨Fin 3, inferInstance⟩
abbrev base : Context.{1} := raisedContext point.{0}
abbrev sourceCode := NativeNerve.realizedConstant three
def swap01 : Fin 3 ≃ Fin 3 := Equiv.swap 0 1
def swap12 : Fin 3 ≃ Fin 3 := Equiv.swap 1 2
def cycle : Fin 3 ≃ Fin 3 := swap01.trans swap12
noncomputable def chosenPath (e : Fin 3 ≃ Fin 3) := uaLoop three e
noncomputable def lineCode (e : Fin 3 ≃ Fin 3) := codeOfPath (chosenPath e)
noncomputable abbrev carrier (e : Fin 3 ≃ Fin 3) := liftedDecode (lineCode e)

/-- Native Glue's target coordinate, with its actual source action. -/
noncomputable def targetCoordinate (e : Fin 3 ≃ Fin 3) :
    carrier e ⟶ constantFamily (total (interval base)) (ULift.{1} (Fin 3)) :=
  NativeUnivalence.unglue sourceCode sourceCode (nativeIso three e).hom (nativeEquivalence three e) ≫
    Functor.whiskerLeft (projection (interval base)).mapElements (decoderPresentation three).hom

noncomputable def coordinate (e : Fin 3 ≃ Fin 3) :
    Term (constantFamily (total (carrier e)) (ULift.{1} Nat)) where
  val x := ⟨((targetCoordinate e).app ((projection (carrier e)).mapElements.obj x) x.val.2).down.val⟩
  property f := congrArg (fun z : ULift.{1} (Fin 3) => (ULift.up z.down.val : ULift.{1} Nat))
    ((Term.map (Functor.whiskerLeft (projection (carrier e)).mapElements (targetCoordinate e))
      (generic (carrier e))).property f)

noncomputable def dependent (e : Fin 3 ≃ Fin 3) :=
  CartesianLargeFamilyConstructors.indexedAdmission (coordinate e)

noncomputable def sourceElement (e : Fin 3 ≃ Fin 3) (n : Fin 3) :
    Term (reindex (carrier e) (endpointSub base false)) :=
  CodeTransport.cast (codeOfPath_zero (chosenPath e)).symm (constantElement three n)

/-- The dependent witness is admitted by the public small-presentation interface. -/
noncomputable def zeroField (e : Fin 3 ≃ Fin 3) : Term (liftedDecode (dependent e).code) :=
  Term.map (dependent e).decoding.inv
    ⟨fun _ => ⟨⟨0, Nat.zero_lt_succ _⟩⟩, fun f => by
      apply ULift.ext
      apply Fin.ext
      have hc : ∀ {m n : ULift.{1} Nat} (h : m = n) (z : ULift.{1} (Fin (m.down+1))),
          (cast (congrArg (fun k : ULift.{1} Nat => ULift.{1} (Fin (k.down+1))) h) z).down.val =
            z.down.val := by
        intro m n h z
        cases h
        rfl
      exact hc ((coordinate e).property f) _⟩

noncomputable def initialPair (e : Fin 3 ≃ Fin 3) (n : Fin 3) :
    Term (reindex (SquareKit.Cubical.Cartesian.sigma (carrier e) (liftedDecode (dependent e).code))
      (endpointSub base false)) :=
  sigmaIntro (B := reindex (liftedDecode (dependent e).code)
    (liftSub (carrier e) (endpointSub base false))) (sourceElement e n)
    (Term.reindex (zeroField e) (pair (endpointSub base false) (sourceElement e n)))

noncomputable def pairLine (e : Fin 3 ≃ Fin 3) (n : Fin 3) :=
  pairSection (lineCode e) (dependent e).code (endpoint base false) (initialPair e n)

/-- This is the selected native comparison, not a supplied preservation proof. -/
noncomputable def pairComparison (e : Fin 3 ≃ Fin 3) (n : Fin 3) :=
  pairAlongPath (chosenPath e) (dependent e).code (initialPair e n)

example (e : Fin 3 ≃ Fin 3) (n : Fin 3) :
    Term.reindex (pairLine e n) (endpointSub base false) = initialPair e n :=
  pairSection_source _ _ _ _

noncomputable def pairOutput (e : Fin 3 ≃ Fin 3) (n : Fin 3) :=
  (LargeConstructors.sigma (lineCode e) (dependent e).code).transportInFamily
    (endpoint base false) (endpoint base true) (initialPair e n)

noncomputable def pairRoundTrip (e : Fin 3 ≃ Fin 3) (n : Fin 3) :=
  (LargeConstructors.sigma (lineCode e) (dependent e).code).roundTripComparison
    (endpoint base false) (endpoint base true) (initialPair e n)

noncomputable def pairObservation (e : Fin 3 ≃ Fin 3) :
    reindex (SquareKit.Cubical.Cartesian.sigma (carrier e) (liftedDecode (dependent e).code))
      (endpointSub base true) ⟶ constantFamily base (ULift.{1} (Fin 3)) :=
  DiscreteRecords.firstMap (reindex (carrier e) (endpointSub base true))
    (reindex (liftedDecode (dependent e).code) (liftSub (carrier e) (endpointSub base true))) ≫
    eqToHom (NativeUnivalence.decode_one (chosenPath e)) ≫ (decoderPresentation three).hom

noncomputable def observedPair (e : Fin 3 ≃ Fin 3) (n : Fin 3) :=
  Term.map (pairObservation e) (pairOutput e n)

set_option backward.isDefEq.respectTransparency false in
theorem pairFirst_action (e : Fin 3 ≃ Fin 3) (n : Fin 3) :
    CodeTransport.cast (codeOfPath_one (chosenPath e))
      (Term.reindex (pairFirst (lineCode e) (dependent e).code (endpoint base false)
        (initialPair e n)) (endpointSub base true)) = constantElement three (e n) := by
  have h := pairFirst_path (chosenPath e) (dependent e).code (initialPair e n)
  change _ = Term.map (NativeUnivalence.pathToMap (uaLoop three e))
    (CodeTransport.cast (codeOfPath_zero (chosenPath e))
      (CodeTransport.cast (codeOfPath_zero (chosenPath e)).symm (constantElement three n))) at h
  simp only [CodeTransport.cast_trans, CodeTransport.cast_refl, uaLoop_map] at h
  apply h.trans
  apply Term.ext
  intro x
  change (decoderPresentation three).inv.app x
    ⟨e (((decoderPresentation three).hom.app x
      ((decoderPresentation three).inv.app x ⟨n⟩)).down)⟩ = _
  rw [(decoderPresentation three).inv_hom_id_app_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem observedPair_action (e : Fin 3 ≃ Fin 3) (n : Fin 3) :
    observedPair e n = (⟨fun _ => ⟨e n⟩, fun _ => rfl⟩ : Term (constantFamily base (ULift.{1} (Fin 3)))) := by
  have hc := homogeneousPath_observe (pairObservation e)
    ((LargeConstructors.sigma (lineCode e) (dependent e).code).comparisonInFamily
      (endpoint base false) (endpoint base true) (pairLine e n))
  have hs := pairSection_source (lineCode e) (dependent e).code (endpoint base false) (initialPair e n)
  change Term.reindex (pairLine e n) (graph (endpoint base false)) = _ at hs
  rw [hs] at hc
  apply hc.trans
  have hf := congrArg (Term.map (decoderPresentation three).hom) (pairFirst_action e n)
  change Term.map (decoderPresentation three).hom
    (Term.map (eqToHom (congrArg liftedDecode (codeOfPath_one (chosenPath e))))
      (Term.reindex (pairFirst (lineCode e) (dependent e).code (endpoint base false)
        (initialPair e n)) (endpointSub base true))) = _
  rw [CodeTransport.cast_map (codeOfPath_one (chosenPath e))]
  exact hf.trans (Term.map_iso_roundtrip (decoderPresentation three).symm _)

noncomputable def action (e : Fin 3 ≃ Fin 3) (n : Fin 3) : Fin 3 :=
  ((observedPair e n).val ((raisedElements point).obj (representableGeneric ⟨0⟩))).down

theorem action_eq (e : Fin 3 ≃ Fin 3) (n : Fin 3) : action e n = e n :=
  congrArg (fun t => (t.val ((raisedElements point).obj (representableGeneric ⟨0⟩))).down)
    (observedPair_action e n)

example : action swap12 (action swap01 0) = 2 := by rw [action_eq, action_eq]; decide
example : action swap01 (action swap12 0) = 1 := by rw [action_eq, action_eq]; decide
example : action swap12 (action swap01 0) ≠ action swap01 (action swap12 0) := by
  simp only [action_eq]
  decide
example (e : Fin 3 ≃ Fin 3) (n : Fin 3) : action e.symm (action e n) = n := by
  rw [action_eq, action_eq, Equiv.symm_apply_apply]
example (n : Fin 3) : action (Equiv.refl _) n = n := action_eq _ _
example : action cycle 0 ≠ action (Equiv.refl _) 0 := by
  rw [action_eq, action_eq]
  decide
theorem cycle_nonidentity : cycle ≠ Equiv.refl (Fin 3) := by
  intro h
  have he := congrArg (fun e => e (0 : Fin 3)) h
  exact (by decide : cycle 0 ≠ (0 : Fin 3)) he

/-- The actual carrier path retains the complete selected equivalence record. -/
theorem carrier_complete (e : Fin 3 ≃ Fin 3) :
    (⟨NativeUnivalence.pathToMap (chosenPath e), NativeUnivalence.pathToEquivalence (chosenPath e)⟩ :
      Σ f : liftedDecode sourceCode ⟶ liftedDecode sourceCode, HomotopyEquivalence f) =
      ⟨(nativeIso three e).hom, nativeEquivalence three e⟩ :=
  ua_complete three _ _

noncomputable def targetElement (e : Fin 3 ≃ Fin 3) (n : Fin 3) :
    Term (reindex (carrier e) (endpointSub base true)) :=
  CodeTransport.cast (codeOfPath_one (chosenPath e)).symm (constantElement three n)

set_option backward.isDefEq.respectTransparency false in
theorem targetCoordinate_one (e : Fin 3 ≃ Fin 3) (n : Fin 3) :
    Term.map (Functor.whiskerLeft (endpointSub base true).mapElements (targetCoordinate e))
      (targetElement e n) = (⟨fun _ => ⟨n⟩, fun _ => rfl⟩ : Term (constantFamily base (ULift.{1} (Fin 3)))) := by
  have hu := NativeUnivalence.unglue_one sourceCode sourceCode (nativeIso three e).hom
    (nativeEquivalence three e)
  have h := congrArg (fun f => Term.map (decoderPresentation three).hom
    (Term.map f (targetElement e n))) hu
  apply h.trans
  change Term.map (decoderPresentation three).hom
    (Term.map (eqToHom (congrArg liftedDecode (codeOfPath_one (chosenPath e))))
      (CodeTransport.cast (codeOfPath_one (chosenPath e)).symm (constantElement three n))) = _
  rw [CodeTransport.cast_map (codeOfPath_one (chosenPath e)), CodeTransport.cast_trans, CodeTransport.cast_refl]
  exact Term.map_iso_roundtrip (decoderPresentation three).symm _

set_option backward.isDefEq.respectTransparency false in
theorem targetCoordinate_zero (e : Fin 3 ≃ Fin 3) (n : Fin 3) :
    Term.map (Functor.whiskerLeft (endpointSub base false).mapElements (targetCoordinate e))
      (sourceElement e n) = (⟨fun _ => ⟨e n⟩, fun _ => rfl⟩ : Term (constantFamily base (ULift.{1} (Fin 3)))) := by
  have hu := NativeUnivalence.unglue_zero sourceCode sourceCode (nativeIso three e).hom
    (nativeEquivalence three e)
  have h := congrArg (fun f => Term.map (decoderPresentation three).hom
    (Term.map f (sourceElement e n))) hu
  apply h.trans
  change Term.map (decoderPresentation three).hom (Term.map (nativeIso three e).hom
    (Term.map (eqToHom (congrArg liftedDecode (codeOfPath_zero (chosenPath e))))
      (CodeTransport.cast (codeOfPath_zero (chosenPath e)).symm (constantElement three n)))) = _
  rw [CodeTransport.cast_map (codeOfPath_zero (chosenPath e)), CodeTransport.cast_trans, CodeTransport.cast_refl]
  apply Term.ext
  intro x
  change (decoderPresentation three).hom.app x ((decoderPresentation three).inv.app x
    ⟨e (((decoderPresentation three).hom.app x
      ((decoderPresentation three).inv.app x ⟨n⟩)).down)⟩) = _
  rw [(decoderPresentation three).inv_hom_id_app_apply, (decoderPresentation three).inv_hom_id_app_apply]

noncomputable def atTarget (e : Fin 3 ≃ Fin 3) (n : Fin 3) : (total (carrier e)).Elements :=
  (pair (endpointSub base true) (targetElement e n)).mapElements.obj
    ((raisedElements point).obj (representableGeneric ⟨0⟩))

noncomputable def varyingFiber (e : Fin 3 ≃ Fin 3) (n : Fin 3) :
    (liftedDecode (dependent e).code).obj (atTarget e n) ≃ Fin (n.val+1) :=
  ((dependent e).decoding.app (atTarget e n)).toEquiv.trans
    (Equiv.ulift.trans (Equiv.cast (congrArg (fun k : ULift.{1} (Fin 3) => Fin (k.down.val+1))
      (congrArg (fun t => t.val ((raisedElements point).obj (representableGeneric ⟨0⟩)))
        (targetCoordinate_one e n)))))

theorem varying_fibers (e : Fin 3 ≃ Fin 3) : ¬ Nonempty
    ((liftedDecode (dependent e).code).obj (atTarget e 0) ≃
      (liftedDecode (dependent e).code).obj (atTarget e 1)) := by
  rintro ⟨h⟩
  have hc := Fintype.card_congr ((varyingFiber e 0).symm.trans (h.trans (varyingFiber e 1)))
  simp at hc

noncomputable def label (e : Fin 3 ≃ Fin 3) :=
  CartesianLargeFamilyConstructors.constant (total (carrier e)) (Fin 3)
noncomputable def output (e : Fin 3 ≃ Fin 3) :=
  LargeConstructors.sigma (label e).code (projection (liftedDecode (label e).code) ≫ (dependent e).code)

noncomputable def outputFiber (e : Fin 3 ≃ Fin 3) (n : Fin 3) :
    (liftedDecode (output e).code).obj (atTarget e n) ≃ (Fin 3 × Fin (n.val+1)) :=
  ((output e).decoding.app (atTarget e n)).toEquiv.trans
    ((Equiv.sigmaCongr (((label e).decoding.app (atTarget e n)).toEquiv.trans Equiv.ulift)
      (fun _ => varyingFiber e n)).trans (Equiv.sigmaEquivProd (Fin 3) (Fin (n.val+1))))

theorem varying_output_fibers (e : Fin 3 ≃ Fin 3) : ¬ Nonempty
    ((liftedDecode (output e).code).obj (atTarget e 0) ≃
      (liftedDecode (output e).code).obj (atTarget e 1)) := by
  rintro ⟨h⟩
  have hc := Fintype.card_congr ((outputFiber e 0).symm.trans (h.trans (outputFiber e 1)))
  simp at hc

noncomputable def inverseCoordinate (e : Fin 3 ≃ Fin 3) :
    Term (constantFamily (total (carrier e)) (ULift.{1} (Fin 3))) where
  val x := ⟨e.symm (((targetCoordinate e).app ((projection (carrier e)).mapElements.obj x) x.val.2).down)⟩
  property f := congrArg (fun z : ULift.{1} (Fin 3) => (ULift.up (e.symm z.down) : ULift.{1} (Fin 3)))
    ((Term.map (Functor.whiskerLeft (projection (carrier e)).mapElements (targetCoordinate e))
      (generic (carrier e))).property f)

/-- An independent whole section fixes the source function and retains its
varying dependent witness. Its target value detects the backwards argument. -/
noncomputable def prescribedFunction (e : Fin 3 ≃ Fin 3) :
    Term (SquareKit.Cubical.Cartesian.pi (carrier e) (liftedDecode (output e).code)) :=
  lam (Term.map (output e).decoding.inv
    (sigmaIntro (B := reindex (liftedDecode (dependent e).code) (projection (liftedDecode (label e).code)))
      (Term.map (label e).decoding.inv (inverseCoordinate e)) (zeroField e)))

noncomputable def initialFunction (e : Fin 3 ≃ Fin 3) :=
  Term.reindex (prescribedFunction e) (endpointSub base false)
noncomputable def functionLine (e : Fin 3 ≃ Fin 3) :=
  functionSection (lineCode e) (output e).code (endpoint base false) (initialFunction e)
noncomputable def functionComparison (e : Fin 3 ≃ Fin 3) :=
  functionAlongPath (chosenPath e) (output e).code (initialFunction e)
noncomputable def functionOutput (e : Fin 3 ≃ Fin 3) :=
  (LargeConstructors.pi (lineCode e) (output e).code).transportInFamily
    (endpoint base false) (endpoint base true) (initialFunction e)

noncomputable def functionRoundTrip (e : Fin 3 ≃ Fin 3) :=
  (LargeConstructors.pi (lineCode e) (output e).code).roundTripComparison
    (endpoint base false) (endpoint base true) (initialFunction e)

noncomputable def outputObservation (e : Fin 3 ≃ Fin 3) :
    liftedDecode (output e).code ⟶ constantFamily (total (carrier e)) (ULift.{1} (Fin 3)) :=
  (output e).decoding.hom ≫ DiscreteRecords.firstMap (liftedDecode (label e).code)
    (reindex (liftedDecode (dependent e).code) (projection (liftedDecode (label e).code))) ≫
      (label e).decoding.hom

noncomputable def functionObservation (e : Fin 3 ≃ Fin 3) (n : Fin 3) :
    reindex (SquareKit.Cubical.Cartesian.pi (carrier e) (liftedDecode (output e).code))
      (endpointSub base true) ⟶ constantFamily base (ULift.{1} (Fin 3)) :=
  (piReindexIso (carrier e) (liftedDecode (output e).code) (endpointSub base true)).hom ≫
    piObservation (Functor.whiskerLeft (liftSub (carrier e) (endpointSub base true)).mapElements
      (outputObservation e)) (targetElement e n)

noncomputable def observedFunction (e : Fin 3 ≃ Fin 3) (n : Fin 3) :=
  Term.map (functionObservation e n) (functionOutput e)

noncomputable def sourceFunctionObservation (e : Fin 3 ≃ Fin 3) (n : Fin 3) :
    reindex (SquareKit.Cubical.Cartesian.pi (carrier e) (liftedDecode (output e).code))
      (endpointSub base false) ⟶ constantFamily base (ULift.{1} (Fin 3)) :=
  (piReindexIso (carrier e) (liftedDecode (output e).code) (endpointSub base false)).hom ≫
    piObservation (Functor.whiskerLeft (liftSub (carrier e) (endpointSub base false)).mapElements
      (outputObservation e)) (sourceElement e n)

set_option backward.isDefEq.respectTransparency false in
theorem initialFunction_identity (e : Fin 3 ≃ Fin 3) (n : Fin 3) :
    Term.map (sourceFunctionObservation e n) (initialFunction e) =
      (⟨fun _ => ⟨n⟩, fun _ => rfl⟩ : Term (constantFamily base (ULift.{1} (Fin 3)))) := by
  apply Term.ext
  intro x
  change (label e).decoding.hom.app _
    (((output e).decoding.hom.app _ ((output e).decoding.inv.app _ _)).1) = _
  rw [(output e).decoding.inv_hom_id_app_apply]
  change (label e).decoding.hom.app _ ((label e).decoding.inv.app _
    ((inverseCoordinate e).val _)) = _
  rw [(label e).decoding.inv_hom_id_app_apply]
  have h := congrArg (fun z : ULift.{1} (Fin 3) => (ULift.up (e.symm z.down) : ULift.{1} (Fin 3)))
    (congrArg (fun t => t.val x) (targetCoordinate_zero e n))
  exact h.trans (congrArg ULift.up (e.symm_apply_apply n))

set_option backward.isDefEq.respectTransparency false in
theorem prescribedFunction_target (e : Fin 3 ≃ Fin 3) (n : Fin 3) :
    Term.map (functionObservation e n) (Term.reindex (prescribedFunction e) (endpointSub base true)) =
      (⟨fun _ => ⟨e.symm n⟩, fun _ => rfl⟩ : Term (constantFamily base (ULift.{1} (Fin 3)))) := by
  apply Term.ext
  intro x
  change (label e).decoding.hom.app _
    (((output e).decoding.hom.app _ ((output e).decoding.inv.app _ _)).1) = _
  rw [(output e).decoding.inv_hom_id_app_apply]
  change (label e).decoding.hom.app _ ((label e).decoding.inv.app _
    ((inverseCoordinate e).val _)) = _
  rw [(label e).decoding.inv_hom_id_app_apply]
  exact congrArg (fun z : ULift.{1} (Fin 3) => (ULift.up (e.symm z.down) : ULift.{1} (Fin 3)))
    (congrArg (fun t => t.val x) (targetCoordinate_one e n))

set_option backward.isDefEq.respectTransparency false in
theorem functionLine_action (e : Fin 3 ≃ Fin 3) (n : Fin 3) :
    Term.map (functionObservation e n) (Term.reindex (functionLine e) (endpointSub base true)) =
      (⟨fun _ => ⟨e.symm n⟩, fun _ => rfl⟩ : Term (constantFamily base (ULift.{1} (Fin 3)))) := by
  let F := piFilling (NativeDecode.filling (lineCode e)) (NativeDecode.filling_lawful (lineCode e))
    (NativeDecode.filling (output e).code)
  have hF : F.Lawful := piFilling_lawful _ (NativeDecode.filling_lawful (lineCode e)) _
    (NativeDecode.filling_lawful (output e).code)
  have hc := homogeneousPath_observe (functionObservation e n)
    (IntervalTransport.prescribedLineComparison F hF (endpoint base false) (endpoint base true)
      (initialFunction e) (prescribedFunction e) rfl)
  rw [IntervalTransport.map_section F hF] at hc
  have hs := congrArg (fun t => Term.map (functionObservation e n)
    (Term.reindex t (endpointSub base true)))
    (functionSection_selected (lineCode e) (output e).code (endpoint base false) (initialFunction e))
  exact hs.trans (hc.trans (prescribedFunction_target e n))

set_option backward.isDefEq.respectTransparency false in
theorem observedFunction_action (e : Fin 3 ≃ Fin 3) (n : Fin 3) :
    observedFunction e n =
      (⟨fun _ => ⟨e.symm n⟩, fun _ => rfl⟩ : Term (constantFamily base (ULift.{1} (Fin 3)))) := by
  have hc := homogeneousPath_observe (functionObservation e n)
    ((LargeConstructors.pi (lineCode e) (output e).code).comparisonInFamily
      (endpoint base false) (endpoint base true) (functionLine e))
  have hs := functionSection_source (lineCode e) (output e).code (endpoint base false) (initialFunction e)
  change Term.reindex (functionLine e) (graph (endpoint base false)) = _ at hs
  rw [hs] at hc
  exact hc.trans (functionLine_action e n)

noncomputable def functionAction (e : Fin 3 ≃ Fin 3) (n : Fin 3) : Fin 3 :=
  ((observedFunction e n).val ((raisedElements point).obj (representableGeneric ⟨0⟩))).down
theorem functionAction_eq (e : Fin 3 ≃ Fin 3) (n : Fin 3) : functionAction e n = e.symm n :=
  congrArg (fun t => (t.val ((raisedElements point).obj (representableGeneric ⟨0⟩))).down)
    (observedFunction_action e n)

example : functionAction cycle 0 = 1 := by rw [functionAction_eq]; decide
example : functionAction cycle 0 ≠ 0 ∧ functionAction cycle 0 ≠ action cycle 0 := by
  rw [functionAction_eq, action_eq]
  decide
example (n : Fin 3) : functionAction cycle.symm (functionAction cycle n) = n := by
  rw [functionAction_eq, functionAction_eq, Equiv.symm_symm, Equiv.apply_symm_apply]

namespace Substitution
abbrev square : Context.{1} := raisedContext (representable.{0} ⟨2⟩)
def forget : square ⟶ base := raisedSub (representableMap (fun i => Fin.elim0 i))
def swapCube : (⟨2⟩ : Cube) ⟶ ⟨2⟩ := fun i => .var (if i = 0 then 1 else 0)
def duplicateCube : (⟨2⟩ : Cube) ⟶ ⟨2⟩ := fun _ => .var 0
def swap : square ⟶ square := raisedSub (representableMap swapCube)
def duplicate : square ⟶ square := raisedSub (representableMap duplicateCube)
def genericPoint : square.Elements := (raisedElements _).obj (representableGeneric ⟨2⟩)

theorem swap_nonidentity : swap ≠ 𝟙 square := by
  intro h
  have he := congrArg (fun f : square ⟶ square => (f.app genericPoint.obj genericPoint.val).down.down 0) h
  change Dim.var (1 : Fin 2) = Dim.var 0 at he
  exact (by decide : (1 : Fin 2) ≠ 0) (Dim.var.inj he)
theorem duplicate_nonidentity : duplicate ≠ 𝟙 square := by
  intro h
  have he := congrArg (fun f : square ⟶ square => (f.app genericPoint.obj genericPoint.val).down.down 1) h
  change Dim.var (0 : Fin 2) = Dim.var 1 at he
  exact Fin.zero_ne_one (Dim.var.inj he)

def first : Term (interval (representable.{0} ⟨2⟩)) where
  val x := ⟨fun _ => x.val.down 0⟩
  property f := by
    apply ULift.ext
    funext i
    exact congrArg (fun h => h.down 0) f.map_val
def cap := UniversalTransport.raiseInterval first
def face : Subcontext square := Subcontext.intervalEq cap (endpoint square false)
theorem variable_cap (b : Bool) : cap ≠ endpoint square b := by
  intro h
  have he := congrArg (fun t => (t.val genericPoint).down 0) h
  change Dim.var (0 : Fin 2) = Dim.endpoint b at he
  cases he
theorem proper_face : ¬ face.Holds genericPoint := by
  intro h
  have he := congrArg (fun t => t.down 0) h
  change Dim.var (0 : Fin 2) = Dim.endpoint false at he
  cases he
def zeroPoint : square.Elements := square.elementsMk (Opposite.op ⟨0⟩)
  ⟨⟨fun _ => .endpoint false⟩⟩
theorem face_nonempty : face.Holds zeroPoint := rfl

noncomputable def a : total (interval square) ⟶ smallFamilyCodes.{0} :=
  intervalSub forget ≫ lineCode cycle
noncomputable def b : total (liftedDecode a) ⟶ smallFamilyCodes.{0} :=
  liftSub (carrier cycle) (intervalSub forget) ≫ (dependent cycle).code
noncomputable def c : total (liftedDecode a) ⟶ smallFamilyCodes.{0} :=
  liftSub (carrier cycle) (intervalSub forget) ≫ (output cycle).code
noncomputable def pairSeed : Term (SquareKit.Cubical.Cartesian.sigma (liftedDecode a) (liftedDecode b)) :=
  Term.reindex (pairLine cycle 0) (intervalSub forget)
noncomputable def pairCap : Term
    (reindex (SquareKit.Cubical.Cartesian.sigma (liftedDecode a) (liftedDecode b)) (graph cap)) :=
  Term.reindex pairSeed (graph cap)
noncomputable def pairFill : Term (SquareKit.Cubical.Cartesian.sigma (liftedDecode a) (liftedDecode b)) :=
  pairSection a b cap pairCap
noncomputable def functionSeed : Term
    (SquareKit.Cubical.Cartesian.pi (liftedDecode a) (liftedDecode c)) := Term.map
  (piReindexIso (carrier cycle) (liftedDecode (output cycle).code) (intervalSub forget)).hom
  (Term.reindex (functionLine cycle) (intervalSub forget))
noncomputable def functionCap : Term
    (reindex (SquareKit.Cubical.Cartesian.pi (liftedDecode a) (liftedDecode c)) (graph cap)) :=
  Term.reindex functionSeed (graph cap)
noncomputable def functionFill : Term (SquareKit.Cubical.Cartesian.pi (liftedDecode a) (liftedDecode c)) :=
  functionSection a c cap functionCap


/-- All fields retain their original full claims. Packaging them lets the closed
admitted example reuse the checked generic interface without expanding its code. -/
structure PairCase
    (a : total (interval square) ⟶ smallFamilyCodes.{0})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{0}) (r s : Term (interval square))
    (z : Term (reindex (SquareKit.Cubical.Cartesian.sigma (liftedDecode a) (liftedDecode b)) (graph r)))
    (σ : square ⟶ square) where
  section_eq :
    pairSection (intervalSub σ ≫ a) (liftSub (liftedDecode a) (intervalSub σ) ≫ b)
      (Term.reindex r σ) (Term.reindex z σ) =
      Term.reindex (pairSection a b r z) (intervalSub σ)
  body_eq :
    pathApp (((LargeConstructors.sigma a b).reindex (intervalSub σ)).comparisonInFamily
      (Term.reindex r σ) (Term.reindex s σ)
      (Term.reindex (pairSection a b r z) (intervalSub σ))) =
      Term.reindex (pathApp ((LargeConstructors.sigma a b).comparisonInFamily r s
        (pairSection a b r z))) (intervalSub σ)
  rebuilt_body_eq :
    pathApp (((LargeConstructors.sigma a b).reindex (intervalSub σ)).comparisonInFamily
      (Term.reindex r σ) (Term.reindex s σ)
      (Term.reindex (pairSection a b r z) (intervalSub σ))) =
    pathApp ((LargeConstructors.sigma (intervalSub σ ≫ a)
      (liftSub (liftedDecode a) (intervalSub σ) ≫ b)).rebuiltComparison
      (Iso.refl _) (Term.reindex r σ) (Term.reindex s σ)
      (Term.reindex (pairSection a b r z) (intervalSub σ))
      (pairSection (intervalSub σ ≫ a) (liftSub (liftedDecode a) (intervalSub σ) ≫ b)
        (Term.reindex r σ) (Term.reindex z σ)) (pairSection_reindex a b r z σ).symm)
  comparison : Term (homogeneousPath
    (reindex (reindex (SquareKit.Cubical.Cartesian.sigma (liftedDecode a) (liftedDecode b))
      (intervalSub σ)) (graph (Term.reindex s σ)))
    (((LargeConstructors.sigma a b).reindex (intervalSub σ)).transportInFamily
      (Term.reindex r σ) (Term.reindex s σ)
      (Term.reindex (Term.reindex (pairSection a b r z) (intervalSub σ)) (graph (Term.reindex r σ))))
    ((LargeConstructors.sigma (intervalSub σ ≫ a) (liftSub (liftedDecode a) (intervalSub σ) ≫ b)).transportInFamily
      (Term.reindex r σ) (Term.reindex s σ)
      (Term.reindex (pairSection (intervalSub σ ≫ a) (liftSub (liftedDecode a) (intervalSub σ) ≫ b)
        (Term.reindex r σ) (Term.reindex z σ)) (graph (Term.reindex r σ)))))

noncomputable def pairCase
    (a : total (interval square) ⟶ smallFamilyCodes.{0})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{0}) (r s : Term (interval square))
    (z : Term (reindex (SquareKit.Cubical.Cartesian.sigma (liftedDecode a) (liftedDecode b)) (graph r)))
    (σ : square ⟶ square) : PairCase a b r s z σ where
  section_eq := pairSection_reindex a b r z σ
  body_eq := Result.comparisonInFamily_body_reindex _ _ _ _ σ
  rebuilt_body_eq := pair_comparison_body_recomputed a b r s z σ
  comparison := pairRecomputedComparison a b r s z σ

noncomputable def functionBoxFor
    (a : total (interval square) ⟶ smallFamilyCodes.{0})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{0}) (r : Term (interval square))
    (z : Term (reindex (SquareKit.Cubical.Cartesian.pi (liftedDecode a) (liftedDecode b)) (graph r)))
    (φ : Subcontext square) : OpenBox (SquareKit.Cubical.Cartesian.pi (liftedDecode a) (liftedDecode b)) φ r where
  tube := ⟨fun x _ => (functionSection a b r z).val x,
    fun f _ => (functionSection a b r z).property f⟩
  base := Term.reindex (functionSection a b r z) (graph r)
  boundary _ _ := rfl

structure FunctionCase
    (a : total (interval square) ⟶ smallFamilyCodes.{0})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{0}) (r s : Term (interval square))
    (z : Term (reindex (SquareKit.Cubical.Cartesian.pi (liftedDecode a) (liftedDecode b)) (graph r)))
    (φ : Subcontext square) (σ : square ⟶ square) where
  section_eq :
    functionSection (intervalSub σ ≫ a) (liftSub (liftedDecode a) (intervalSub σ) ≫ b)
      (Term.reindex r σ) (functionInitialReindex a b r z σ) =
      Term.map (piReindexIso (liftedDecode a) (liftedDecode b) (intervalSub σ)).hom
        (Term.reindex (functionSection a b r z) (intervalSub σ))
  body_eq :
    pathApp (((LargeConstructors.pi a b).reindex (intervalSub σ)).comparisonInFamily
      (Term.reindex r σ) (Term.reindex s σ)
      (Term.reindex (functionSection a b r z) (intervalSub σ))) =
      Term.reindex (pathApp ((LargeConstructors.pi a b).comparisonInFamily r s
        (functionSection a b r z))) (intervalSub σ)
  rebuilt_body_eq :
    pathApp (((LargeConstructors.pi a b).reindex (intervalSub σ)).comparisonInFamily
      (Term.reindex r σ) (Term.reindex s σ)
      (Term.reindex (functionSection a b r z) (intervalSub σ))) =
    pathApp ((LargeConstructors.pi (intervalSub σ ≫ a)
      (liftSub (liftedDecode a) (intervalSub σ) ≫ b)).rebuiltComparison
      (piReindexIso (liftedDecode a) (liftedDecode b) (intervalSub σ)) (Term.reindex r σ) (Term.reindex s σ)
      (Term.reindex (functionSection a b r z) (intervalSub σ))
      (functionSection (intervalSub σ ≫ a) (liftSub (liftedDecode a) (intervalSub σ) ≫ b)
        (Term.reindex r σ) (functionInitialReindex a b r z σ)) (functionSection_reindex a b r z σ).symm)
  comparison : Term (homogeneousPath
    (reindex (reindex (SquareKit.Cubical.Cartesian.pi (liftedDecode a) (liftedDecode b))
      (intervalSub σ)) (graph (Term.reindex s σ)))
    (((LargeConstructors.pi a b).reindex (intervalSub σ)).transportInFamily
      (Term.reindex r σ) (Term.reindex s σ)
      (Term.reindex (Term.reindex (functionSection a b r z) (intervalSub σ)) (graph (Term.reindex r σ))))
    (Term.map (Functor.whiskerLeft (graph (Term.reindex s σ)).mapElements
      (piReindexIso (liftedDecode a) (liftedDecode b) (intervalSub σ)).inv)
      ((LargeConstructors.pi (intervalSub σ ≫ a) (liftSub (liftedDecode a) (intervalSub σ) ≫ b)).transportInFamily
        (Term.reindex r σ) (Term.reindex s σ)
        (Term.reindex (functionSection (intervalSub σ ≫ a) (liftSub (liftedDecode a) (intervalSub σ) ≫ b)
          (Term.reindex r σ) (functionInitialReindex a b r z σ)) (graph (Term.reindex r σ))))))
  face_rebuild :
    FunctionFilling.fill ((NativeDecode.filling a).reindex (intervalSub σ))
      ((NativeDecode.filling_lawful a).reindex _) ((NativeDecode.filling b).reindex
        (liftSub (liftedDecode a) (intervalSub σ))) (𝟙 _) (φ.reindex σ) (Term.reindex r σ)
      (((functionBoxFor a b r z φ).reindex σ).map
        (piReindexIso (liftedDecode a) (liftedDecode b) (intervalSub σ)).hom) =
      Term.map (piReindexIso (liftedDecode a) (liftedDecode b) (intervalSub σ)).hom
        (FunctionFilling.fill (NativeDecode.filling a) (NativeDecode.filling_lawful a)
          (NativeDecode.filling b) (intervalSub σ) (φ.reindex σ) (Term.reindex r σ)
          ((functionBoxFor a b r z φ).reindex σ))

noncomputable def functionCase
    (a : total (interval square) ⟶ smallFamilyCodes.{0})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{0}) (r s : Term (interval square))
    (z : Term (reindex (SquareKit.Cubical.Cartesian.pi (liftedDecode a) (liftedDecode b)) (graph r)))
    (φ : Subcontext square) (σ : square ⟶ square) : FunctionCase a b r s z φ σ where
  section_eq := functionSection_reindex a b r z σ
  body_eq := Result.comparisonInFamily_body_reindex _ _ _ _ σ
  rebuilt_body_eq := function_comparison_body_recomputed a b r s z σ
  comparison := functionRecomputedComparison a b r s z σ
  face_rebuild := FunctionFilling.fill_input_reindex _ _ _ (intervalSub σ) (𝟙 _) _ _ _

noncomputable def pairSwap : PairCase a b cap (endpoint square true) pairCap swap :=
  pairCase a b cap (endpoint square true) pairCap swap
noncomputable def pairDuplicate : PairCase a b cap (endpoint square true) pairCap duplicate :=
  pairCase a b cap (endpoint square true) pairCap duplicate
noncomputable def pairComposite : PairCase a b cap (endpoint square true) pairCap (swap ≫ duplicate) :=
  pairCase a b cap (endpoint square true) pairCap (swap ≫ duplicate)
noncomputable def functionSwap : FunctionCase a c cap (endpoint square true) functionCap face swap :=
  functionCase a c cap (endpoint square true) functionCap face swap
noncomputable def functionDuplicate : FunctionCase a c cap (endpoint square true) functionCap face duplicate :=
  functionCase a c cap (endpoint square true) functionCap face duplicate
noncomputable def functionComposite : FunctionCase a c cap (endpoint square true) functionCap face (swap ≫ duplicate) :=
  functionCase a c cap (endpoint square true) functionCap face (swap ≫ duplicate)
/-- A distinct, nonconstant target cap exercises both graph adapters. -/
def targetCap : Term (interval square) := Term.reindex cap swap

theorem variable_target_cap (b : Bool) : targetCap ≠ endpoint square b := by
  intro h
  have he := congrArg (fun t => (t.val genericPoint).down 0) h
  change Dim.var (1 : Fin 2) = Dim.endpoint b at he
  cases he

theorem targetCap_ne_cap : targetCap ≠ cap := by
  intro h
  have he := congrArg (fun t => (t.val genericPoint).down 0) h
  change Dim.var (1 : Fin 2) = Dim.var 0 at he
  exact (by decide : (1 : Fin 2) ≠ 0) (Dim.var.inj he)

noncomputable def pairIdentity : PairCase a b cap (endpoint square true) pairCap (𝟙 square) :=
  pairCase a b cap (endpoint square true) pairCap (𝟙 square)
noncomputable def functionIdentity : FunctionCase a c cap (endpoint square true) functionCap face (𝟙 square) :=
  functionCase a c cap (endpoint square true) functionCap face (𝟙 square)
noncomputable def pairVariableTarget : PairCase a b cap targetCap pairCap swap :=
  pairCase a b cap targetCap pairCap swap
noncomputable def functionVariableTarget : FunctionCase a c cap targetCap functionCap face swap :=
  functionCase a c cap targetCap functionCap face swap
noncomputable def pairDiagonal : PairCase a b cap cap pairCap (swap ≫ duplicate) :=
  pairCase a b cap cap pairCap (swap ≫ duplicate)
noncomputable def functionDiagonal : FunctionCase a c cap cap functionCap face (swap ≫ duplicate) :=
  functionCase a c cap cap functionCap face (swap ≫ duplicate)

end Substitution

end Examples.CartesianConstructorTransport

import SquareKit.Internal.Cubical.NativeStructurePreservation
import SquareKit.Internal.Cubical.CartesianNativeStructurePreservation
import SquareKit.Internal.Cubical.NativeStructureUaComparison
import SquareKit.Internal.Cubical.CartesianNativeStructureUaComparison
import Examples.NativeStructureDescriptions

/-! Native field transport observes negative occurrences of the carrier in
higher-order functions, including every generalized argument. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.NativeStructureIdentity
open CategoryTheory SquareKit.StructureIdentity

def boolSwap : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv := Bool.not_not
  right_inv := Bool.not_not

namespace Presheaf
open SquareKit.Cubical.Presheaf StructureIdentity.Native StructuredIdentity
open Examples.NativeStructureDescriptions Examples.NativeStructureDescriptions.Presheaf

variable {Γ : Context.{1}}
def swap : boolCarrier (Γ := Γ) ≅ boolCarrier :=
  constantIso (Equiv.ulift.trans (boolSwap.trans Equiv.ulift.symm))

example {A B : Family Γ} (f : A ⟶ B) (g : B ⟶ A) (x y : Γ.Elements)
    (h : x ⟶ y) (p : (family (.function .carrier .carrier) A).obj x) (b : B.obj y) :
    ((action (.function .carrier .carrier) f g).app x p).val h b =
      f.app y (p.val h (g.app y b)) := rfl

example (x : Γ.Elements) :
    (((actionIso pointedUnary swap).hom.app x (selected.val x)).1).down = true := rfl

example (x : Γ.Elements) :
    (((actionIso pointedUnary swap).hom.app x (selected.val x)).2.val (𝟙 x) ⟨false⟩).down = true := rfl

/-- Conjugating evaluation at false by the carrier swap gives evaluation at true. -/
example (x : Γ.Elements) :
    (((actionIso higher swap).hom.app x (higherElement x)).val (𝟙 x) (nativeNegation x)).down = false := rfl

example (x : Γ.Elements) :
    ((actionIso higher swap).inv.app x ((actionIso higher swap).hom.app x (higherElement x))) =
      higherElement x :=
  congrArg (fun k => k.app x (higherElement x)) (actionIso higher swap).hom_inv_id

/-- A higher-order field has an independent preservation witness under Boolean swap. -/
def higherSelected : Term (family higher (boolCarrier (Γ := Γ))) :=
  Term.map (presentedIso higher (Iso.refl _)).inv ⟨fun _ => ⟨fun g => g false⟩, fun _ => rfl⟩

def swapPreservesHigher : Term (preserves higher swap.hom swap.inv
    (higherSelected (Γ := Γ)) (Term.map (actionIso higher swap).hom higherSelected)) :=
  Term.map (preservesActionPathIso higher swap higherSelected _).inv
    (homogeneousRefl (Term.map (actionIso higher swap).hom higherSelected))

noncomputable def boolAdmission : SmallUniverse.LargeConstructors.Result (boolCarrier (Γ := Γ)) :=
  let q : Term (constantFamily Γ PUnit.{2}) := ⟨fun _ => PUnit.unit, fun _ => rfl⟩
  SmallUniverse.LargeConstructors.construct
    ⟨fun _ => Bool, fun _ => Equiv.ulift.symm⟩
    (discreteFilling q (fun _ => ULift.{1} Bool)) (discreteFilling_lawful q _)

variable (admission : SmallUniverse.LargeConstructors.Result (boolCarrier (Γ := Γ)))
noncomputable def codedSwap : SmallUniverse.liftedDecode admission.code ≅
    SmallUniverse.liftedDecode admission.code :=
  admission.decoding ≪≫ swap ≪≫ admission.decoding.symm

noncomputable def codedFalse : Term (SmallUniverse.liftedDecode admission.code) :=
  Term.map admission.decoding.inv ⟨fun _ => ⟨false⟩, fun _ => rfl⟩

noncomputable def codedTrue : Term (SmallUniverse.liftedDecode admission.code) :=
  Term.map (codedSwap admission).hom (codedFalse admission)

theorem codedFalse_read (x : Γ.Elements) :
    (admission.decoding.hom.app x ((codedFalse admission).val x)).down = false :=
  congrArg (fun z : ULift.{1} Bool => z.down) (admission.decoding.inv_hom_id_app_apply x ⟨false⟩)

theorem codedTrue_read (x : Γ.Elements) :
    (admission.decoding.hom.app x ((codedTrue admission).val x)).down = true := by
  change (admission.decoding.hom.app x
    (admission.decoding.inv.app x ((swap (Γ := Γ)).hom.app x
      (admission.decoding.hom.app x ((codedFalse admission).val x))))).down = true
  rw [admission.decoding.inv_hom_id_app_apply]
  change !(admission.decoding.hom.app x ((codedFalse admission).val x)).down = true
  rw [codedFalse_read]
  rfl

theorem codedSwap_rejects_unchanged (x : Γ.Elements) :
    ¬ Nonempty (Term (homogeneousPath (SmallUniverse.liftedDecode admission.code)
      (codedTrue admission) (codedFalse admission))) := by
  rintro ⟨p⟩
  let q := Term.map (HomotopyLevels.pathMap admission.decoding.hom _ _) p
  have h := discretePath_endpoints q
  have h' := congrArg (fun s => (s.val x).down) h
  change (admission.decoding.hom.app x ((codedTrue admission).val x)).down =
    (admission.decoding.hom.app x ((codedFalse admission).val x)).down at h'
  rw [codedTrue_read, codedFalse_read] at h'
  contradiction


example (x : Γ.Elements) :
    ((boolAdmission (Γ := Γ)).decoding.hom.app x
      ((codedTrue boolAdmission).val x)).down = true :=
  codedTrue_read boolAdmission x

example (x : Γ.Elements) :
    ¬ Nonempty (Term (homogeneousPath (SmallUniverse.liftedDecode (boolAdmission (Γ := Γ)).code)
      (codedTrue boolAdmission) (codedFalse boolAdmission))) :=
  codedSwap_rejects_unchanged boolAdmission x

noncomputable def codedSwapEquivalence :
    Term (equivalences .carrier (codedFalse admission) (codedTrue admission)) :=
  let f := (codedSwap admission).hom
  let E := HomotopyEquivalence.ofIso (codedSwap admission)
  sigmaIntro (EquivalenceFamilies.equivSections _ _ ⟨f,E⟩)
    (Term.map (suppliedEquivalenceFiberIso .carrier f E (codedFalse admission) (codedTrue admission)).inv
      (homogeneousRefl (codedTrue admission)))

noncomputable def codedSwapPath :
    Term (homogeneousPath (objects .carrier Γ)
      (objectOf .carrier admission.code (codedFalse admission))
      (objectOf .carrier admission.code (codedTrue admission))) :=
  Term.map (UaComparison.explicitMap .carrier admission.code (codedFalse admission)
    admission.code (codedTrue admission)) (codedSwapEquivalence admission)
example : Term.reindex (pathApp (codedSwapPath admission)) (endpointSub Γ false) =
    objectOf .carrier admission.code (codedFalse admission) := pathApp_zero _
example : Term.reindex (pathApp (codedSwapPath admission)) (endpointSub Γ true) =
    objectOf .carrier admission.code (codedTrue admission) := pathApp_one _

/-- The swap path projects to the selected ua of its complete carrier equivalence. -/
theorem codedSwap_carrier :
    let E := (EquivalenceFamilies.equivSections
      (SmallUniverse.liftedDecode admission.code) (SmallUniverse.liftedDecode admission.code)).symm
        (sigmaFst (codedSwapEquivalence admission))
    Term.map (HomotopyLevels.pathMap (SIP.Exchange.first (SIP.objectFields .carrier))
      (objectOf .carrier admission.code (codedFalse admission))
      (objectOf .carrier admission.code (codedTrue admission))) (codedSwapPath admission) =
        SmallUniverse.NativeUnivalence.ua admission.code admission.code E.1 E.2 :=
  UaComparison.explicitMap_carrier_ua .carrier admission.code (codedFalse admission)
    admission.code (codedTrue admission) (codedSwapEquivalence admission)

/-- Reconstructing the swap path recovers its complete preservation witness natively. -/
noncomputable def codedSwapWitnessRecovery :=
  UaComparison.explicitLeftInverseAt .carrier admission.code (codedFalse admission)
    admission.code (codedTrue admission) (codedSwapEquivalence admission)

/-- Every whole path between these objects is recovered, including its interior. -/
noncomputable def codedSwapPathRecovery
    (p : Term (homogeneousPath (objects .carrier Γ)
      (objectOf .carrier admission.code (codedFalse admission))
      (objectOf .carrier admission.code (codedTrue admission)))) :=
  UaComparison.explicitRightInverseAt .carrier admission.code (codedFalse admission)
    admission.code (codedTrue admission) p


noncomputable def admittedSwapPath := codedSwapPath (boolAdmission (Γ := Γ))

end Presheaf
namespace Cartesian
open SquareKit.Cubical.Cartesian StructureIdentity.Native StructuredIdentity
open Examples.NativeStructureDescriptions Examples.NativeStructureDescriptions.Cartesian

variable {Γ : Context.{1}}
def swap : boolCarrier (Γ := Γ) ≅ boolCarrier :=
  constantIso (Equiv.ulift.trans (boolSwap.trans Equiv.ulift.symm))

example {A B : Family Γ} (f : A ⟶ B) (g : B ⟶ A) (x y : Γ.Elements)
    (h : x ⟶ y) (p : (family (.function .carrier .carrier) A).obj x) (b : B.obj y) :
    ((action (.function .carrier .carrier) f g).app x p).val h b =
      f.app y (p.val h (g.app y b)) := rfl

example (x : Γ.Elements) :
    (((actionIso pointedUnary swap).hom.app x (selected.val x)).1).down = true := rfl

example (x : Γ.Elements) :
    (((actionIso pointedUnary swap).hom.app x (selected.val x)).2.val (𝟙 x) ⟨false⟩).down = true := rfl

/-- Conjugating evaluation at false by the carrier swap gives evaluation at true. -/
example (x : Γ.Elements) :
    (((actionIso higher swap).hom.app x (higherElement x)).val (𝟙 x) (nativeNegation x)).down = false := rfl

example (x : Γ.Elements) :
    ((actionIso higher swap).inv.app x ((actionIso higher swap).hom.app x (higherElement x))) =
      higherElement x :=
  congrArg (fun k => k.app x (higherElement x)) (actionIso higher swap).hom_inv_id

/-- A higher-order field has an independent preservation witness under Boolean swap. -/
def higherSelected : Term (family higher (boolCarrier (Γ := Γ))) :=
  Term.map (presentedIso higher (Iso.refl _)).inv ⟨fun _ => ⟨fun g => g false⟩, fun _ => rfl⟩

def swapPreservesHigher : Term (preserves higher swap.hom swap.inv
    (higherSelected (Γ := Γ)) (Term.map (actionIso higher swap).hom higherSelected)) :=
  Term.map (preservesActionPathIso higher swap higherSelected _).inv
    (homogeneousRefl (Term.map (actionIso higher swap).hom higherSelected))

noncomputable def boolAdmission : SmallUniverse.LargeConstructors.Result (boolCarrier (Γ := Γ)) :=
  SmallUniverse.LargeConstructors.construct
    ⟨fun _ => Bool, fun _ => Equiv.ulift.symm⟩
    (presentedFilling (Iso.refl _)) (presentedFilling_lawful (Iso.refl _))

variable (admission : SmallUniverse.LargeConstructors.Result (boolCarrier (Γ := Γ)))
noncomputable def codedSwap : SmallUniverse.liftedDecode admission.code ≅
    SmallUniverse.liftedDecode admission.code :=
  admission.decoding ≪≫ swap ≪≫ admission.decoding.symm

noncomputable def codedFalse : Term (SmallUniverse.liftedDecode admission.code) :=
  Term.map admission.decoding.inv ⟨fun _ => ⟨false⟩, fun _ => rfl⟩

noncomputable def codedTrue : Term (SmallUniverse.liftedDecode admission.code) :=
  Term.map (codedSwap admission).hom (codedFalse admission)

theorem codedFalse_read (x : Γ.Elements) :
    (admission.decoding.hom.app x ((codedFalse admission).val x)).down = false :=
  congrArg (fun z : ULift.{1} Bool => z.down) (admission.decoding.inv_hom_id_app_apply x ⟨false⟩)

theorem codedTrue_read (x : Γ.Elements) :
    (admission.decoding.hom.app x ((codedTrue admission).val x)).down = true := by
  change (admission.decoding.hom.app x
    (admission.decoding.inv.app x ((swap (Γ := Γ)).hom.app x
      (admission.decoding.hom.app x ((codedFalse admission).val x))))).down = true
  rw [admission.decoding.inv_hom_id_app_apply]
  change !(admission.decoding.hom.app x ((codedFalse admission).val x)).down = true
  rw [codedFalse_read]
  rfl

theorem codedSwap_rejects_unchanged (x : Γ.Elements) :
    ¬ Nonempty (Term (homogeneousPath (SmallUniverse.liftedDecode admission.code)
      (codedTrue admission) (codedFalse admission))) := by
  rintro ⟨p⟩
  let q := Term.map (HomotopyLevels.pathMap admission.decoding.hom _ _) p
  have h := (congrArg (fun t => t.val x) (pathApp_zero q)).symm.trans
    ((constant_section_interval (pathApp q) x ((endpoint Γ false).val x)
      ((endpoint Γ true).val x)).trans (congrArg (fun t => t.val x) (pathApp_one q)))
  have h' := congrArg (fun z : ULift.{1} Bool => z.down) h
  change (admission.decoding.hom.app x ((codedTrue admission).val x)).down =
    (admission.decoding.hom.app x ((codedFalse admission).val x)).down at h'
  rw [codedTrue_read, codedFalse_read] at h'
  contradiction


example (x : Γ.Elements) :
    ((boolAdmission (Γ := Γ)).decoding.hom.app x
      ((codedTrue boolAdmission).val x)).down = true :=
  codedTrue_read boolAdmission x

example (x : Γ.Elements) :
    ¬ Nonempty (Term (homogeneousPath (SmallUniverse.liftedDecode (boolAdmission (Γ := Γ)).code)
      (codedTrue boolAdmission) (codedFalse boolAdmission))) :=
  codedSwap_rejects_unchanged boolAdmission x

noncomputable def codedSwapEquivalence :
    Term (equivalences .carrier (codedFalse admission) (codedTrue admission)) :=
  let f := (codedSwap admission).hom
  let E := HomotopyEquivalence.ofIso (codedSwap admission)
    (SmallUniverse.NativeDecode.filling admission.code) (SmallUniverse.NativeDecode.filling_lawful admission.code)
  sigmaIntro (EquivalenceFamilies.equivSections _ _ ⟨f,E⟩)
    (Term.map (suppliedEquivalenceFiberIso .carrier f E (codedFalse admission) (codedTrue admission)).inv
      (homogeneousRefl (codedTrue admission)))

noncomputable def codedSwapPath :
    Term (homogeneousPath (objects .carrier Γ)
      (objectOf .carrier admission.code (codedFalse admission))
      (objectOf .carrier admission.code (codedTrue admission))) :=
  Term.map (UaComparison.explicitMap .carrier admission.code (codedFalse admission)
    admission.code (codedTrue admission)) (codedSwapEquivalence admission)
example : Term.reindex (pathApp (codedSwapPath admission)) (endpointSub Γ false) =
    objectOf .carrier admission.code (codedFalse admission) := pathApp_zero _
example : Term.reindex (pathApp (codedSwapPath admission)) (endpointSub Γ true) =
    objectOf .carrier admission.code (codedTrue admission) := pathApp_one _

/-- The swap path projects to the selected ua of its complete carrier equivalence. -/
theorem codedSwap_carrier :
    let E := (EquivalenceFamilies.equivSections
      (SmallUniverse.liftedDecode admission.code) (SmallUniverse.liftedDecode admission.code)).symm
        (sigmaFst (codedSwapEquivalence admission))
    Term.map (HomotopyLevels.pathMap (SIP.Exchange.first (SIP.objectFields .carrier))
      (objectOf .carrier admission.code (codedFalse admission))
      (objectOf .carrier admission.code (codedTrue admission))) (codedSwapPath admission) =
        SmallUniverse.NativeUnivalence.ua admission.code admission.code E.1 E.2 :=
  UaComparison.explicitMap_carrier_ua .carrier admission.code (codedFalse admission)
    admission.code (codedTrue admission) (codedSwapEquivalence admission)

/-- Reconstructing the swap path recovers its complete preservation witness natively. -/
noncomputable def codedSwapWitnessRecovery :=
  UaComparison.explicitLeftInverseAt .carrier admission.code (codedFalse admission)
    admission.code (codedTrue admission) (codedSwapEquivalence admission)

/-- Every whole path between these objects is recovered, including its interior. -/
noncomputable def codedSwapPathRecovery
    (p : Term (homogeneousPath (objects .carrier Γ)
      (objectOf .carrier admission.code (codedFalse admission))
      (objectOf .carrier admission.code (codedTrue admission)))) :=
  UaComparison.explicitRightInverseAt .carrier admission.code (codedFalse admission)
    admission.code (codedTrue admission) p


noncomputable def admittedSwapPath := codedSwapPath (boolAdmission (Γ := Γ))

end Cartesian
end Examples.NativeStructureIdentity

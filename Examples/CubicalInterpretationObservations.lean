import Examples.FiniteUniverseLoops
import Examples.CubicalFiniteStateIdentity

/-! A bounded change of setting: actual native transport between constant codes
is observed as a host bijection. Higher selected witnesses remain native data. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalInterpretationObservations
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open SmallUniverse SmallUniverse.NativeUnivalence
open Examples.CubicalGlue Examples.CubicalUnivalenceTransport
open Examples.CompositionalUnivalence

variable {S T V : Type}

noncomputable def lowerMap (p : Term (paths (code S) (code T))) :
    Presheaf.decode (code S) ⟶ Presheaf.decode (code T) :=
  Raising.lowerMap (A := Presheaf.decode (code S)) (B := Presheaf.decode (code T)) (pathToMap p)

noncomputable def constantMap (p : Term (paths (code S) (code T))) :
    constantFamily terminal S ⟶ constantFamily terminal T :=
  (constantLocal terminal S).decodeCodeIso.inv ≫ lowerMap p ≫
    (constantLocal terminal T).decodeCodeIso.hom

noncomputable def constantEquivalence (p : Term (paths (code S) (code T))) :
    HomotopyEquivalence (constantMap p) :=
  (Raising.lowerEquivalence (f := lowerMap p) (pathToEquivalence p)).conjugateIso
    (constantLocal terminal S).decodeCodeIso.symm (constantLocal terminal T).decodeCodeIso

/-- This target arrow uses the actual transport map and its selected fibers. -/
noncomputable def pathBijection (p : Term (paths (code S) (code T))) : S ≃ T :=
  DiscreteEquivalences.closedEquiv (constantMap p) (constantEquivalence p)

theorem pathBijection_apply (p : Term (paths (code S) (code T))) (s : S) :
    pathBijection p s =
      (observe (Term.map (pathToMap p) (nativeInput s))).val DiscreteEquivalences.point := rfl

theorem pathBijection_loop (p : Term (FiniteUniverseLoops.loops S)) :
    pathBijection p = FiniteUniverseLoops.loopPermutation p := rfl

/-- Recover the entire native carrier map in this constant-code fragment. -/
theorem bijection_map (p : Term (paths (code S) (code T))) :
    nativeMap (pathBijection p) = pathToMap p := by
  let i := (constantLocal terminal S).decodeCodeIso
  let j := (constantLocal terminal T).decodeCodeIso
  have hc : (constantIso (pathBijection p)).hom = constantMap p := by
    apply NatTrans.ext
    funext x
    apply ConcreteCategory.hom_ext
    intro s
    exact (DiscreteEquivalences.closedEquiv_app (constantMap p) (constantEquivalence p) x s).symm
  have hl : (codeIso (pathBijection p)).hom = lowerMap p := by
    change i.hom ≫ (constantIso (pathBijection p)).hom ≫ j.inv = _
    rw [hc]
    change i.hom ≫ (i.inv ≫ lowerMap p ≫ j.hom) ≫ j.inv = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  exact congrArg Raising.map hl

theorem transport_input (p : Term (paths (code S) (code T))) (s : S) :
    Term.map (pathToMap p) (nativeInput s) = nativeInput (pathBijection p s) := by
  rw [← bijection_map p]
  exact nativeInput_action _ _

theorem pathBijection_ua (e : S ≃ T) : pathBijection (equivalencePath e) = e := by
  apply Equiv.ext
  intro s
  rw [pathBijection_apply]
  exact congrArg (fun t => t.val DiscreteEquivalences.point)
    (Examples.CubicalNativeUnivalenceTransport.observedNative_eq e s)

/-- A native comparison gives an equality of target arrows, not recovery of its body. -/
theorem pathBijection_comparison {p q : Term (paths (code S) (code T))}
    (h : Term (homogeneousPath (paths (code S) (code T)) p q)) :
    pathBijection p = pathBijection q := by
  apply Equiv.ext
  intro s
  exact congrArg (fun t => t.val DiscreteEquivalences.point)
    (observe_path (transportTwoPath (code S) (code T) h (nativeInput s)))

/-- Arbitrary closed paths, rather than only selected ua representatives. -/
theorem pathBijection_concat (p : Term (paths (code S) (code T)))
    (q : Term (paths (code T) (code V))) :
    pathBijection (homogeneousConcat (filling _) (filling_lawful _) p q) =
      (pathBijection p).trans (pathBijection q) := by
  apply Equiv.ext
  intro s
  have h := observe_path (concatTransportComparison (code S) (code T) (code V) p q (nativeInput s))
  rw [transport_input p, transport_input q, observe_input] at h
  exact congrArg (fun t => t.val DiscreteEquivalences.point) h

theorem pathBijection_reverse (p : Term (paths (code S) (code T))) :
    pathBijection (homogeneousReverse p) = (pathBijection p).symm := by
  apply Equiv.ext
  intro t
  have h := observe_path (reverseTransportLeft (code S) (code T) p
    (nativeInput ((pathBijection p).symm t)))
  rw [transport_input p, Equiv.apply_symm_apply, transport_input, observe_input, observe_input] at h
  exact congrArg (fun x => x.val DiscreteEquivalences.point) h

/-- Identifying the two Boolean loops prevents factorization of actual transport. -/
theorem no_collapsing_action {Q : Sort*}
    (erase : Term (FiniteUniverseLoops.loops Bool) → Q)
    (collapse : erase FiniteUniverseLoops.booleanIdentityLoop =
      erase FiniteUniverseLoops.booleanNegationLoop) :
    ¬ ∃ act : Q → Bool → Bool, ∀ p b, act (erase p) b = pathBijection p b := by
  rintro ⟨act, h⟩
  have bad := (h FiniteUniverseLoops.booleanIdentityLoop true).symm.trans
    ((congrArg (fun q => act q true) collapse).trans (h FiniteUniverseLoops.booleanNegationLoop true))
  change FiniteUniverseLoops.loopPermutation (homogeneousRefl (term (code Bool))) true =
    FiniteUniverseLoops.loopPermutation (equivalencePath booleanTransposition) true at bad
  rw [FiniteUniverseLoops.loopPermutation_refl, FiniteUniverseLoops.loopPermutation_ua] at bad
  exact (by decide : true ≠ false) bad

theorem no_subsingleton_action {Q : Sort*} [Subsingleton Q]
    (erase : Term (FiniteUniverseLoops.loops Bool) → Q) :
    ¬ ∃ act : Q → Bool → Bool, ∀ p b, act (erase p) b = pathBijection p b :=
  no_collapsing_action erase (Subsingleton.elim _ _)

/-- Host equality loops are proof irrelevant and cannot carry this action. -/
theorem no_host_equality_action {A : Sort*} (a : A)
    (erase : Term (FiniteUniverseLoops.loops Bool) → (a = a)) :
    ¬ ∃ act : (a = a) → Bool → Bool, ∀ p b, act (erase p) b = pathBijection p b :=
  no_subsingleton_action erase

/-- A set-valued target can preserve the action when its arrows remain distinct. -/
theorem permutation_action_exists :
    ∃ act : (Bool ≃ Bool) → Bool → Bool,
      ∀ p b, act (pathBijection p) b = pathBijection (S := Bool) (T := Bool) p b :=
  ⟨fun e b => e b, fun _ _ => rfl⟩

/-- Observe the public chosen composition square with its full supplied records. -/
theorem selected_composition
    (f : liftedDecode (code S) ⟶ liftedDecode (code T)) (E : HomotopyEquivalence f)
    (g : liftedDecode (code T) ⟶ liftedDecode (code V)) (D : HomotopyEquivalence g) :
    pathBijection (ua (code S) (code V) (f ≫ g)
      (compositeEquivalence (code S) (code T) (code V) f E g D)) =
    (pathBijection (ua (code S) (code T) f E)).trans
      (pathBijection (ua (code T) (code V) g D)) :=
  (pathBijection_comparison (NaturalUnivalenceLaws.composition
    (code S) (code T) (code V) f E g D)).trans (pathBijection_concat _ _)

/-- The target inverse is the image of the actual selected native inverse. -/
theorem selected_inverse
    (f : liftedDecode (code S) ⟶ liftedDecode (code T)) (E : HomotopyEquivalence f) :
    pathBijection (ua (code T) (code S) (inverseMap (code S) (code T) f E)
      (inverseEquivalence (code S) (code T) f E)) =
      (pathBijection (ua (code S) (code T) f E)).symm :=
  (pathBijection_comparison (NaturalUnivalenceLaws.inverse (code S) (code T) f E)).trans
    (pathBijection_reverse _)

theorem selected_identity (S : Type) :
    pathBijection (ua (code S) (code S) (𝟙 _) (HomotopyEquivalence.ofIso (Iso.refl _))) =
      Equiv.refl S :=
  (pathBijection_comparison (NaturalUnivalenceLaws.identity (code S))).trans
    (FiniteUniverseLoops.loopPermutation_refl S)

/-- Connect the path observer to the carrier used by full native package recovery.
Lowering retains the supplied equivalence data through its existing adapter. -/
theorem ua_admittedCarrier
    (f : liftedDecode (code S) ⟶ liftedDecode (code T)) (E : HomotopyEquivalence f) :
    pathBijection (ua (code S) (code T) f E) =
      CubicalStructuredState.admittedCarrier (Raising.lowerMap f) (Raising.lowerEquivalence E) := by
  apply Equiv.ext
  intro s
  rw [pathBijection_apply]
  exact congrArg (fun t => t.val DiscreteEquivalences.point)
    (observe_path (uaComparison (code S) (code T) f E (nativeInput s))).symm

/-- Equality of the entire package, including its invariant and both proof fields. -/
theorem package_observation
    (f : liftedDecode (code S) ⟶ liftedDecode (code T)) (E : HomotopyEquivalence f)
    (p : CubicalStateTransport.StatePackage S) :
    CubicalStructuredState.targetPackage (Raising.lowerMap f) (Raising.lowerEquivalence E) p =
      p.conjugate (pathBijection (ua (code S) (code T) f E)) := by
  rw [CubicalStructuredState.targetPackage_eq, ua_admittedCarrier]

/-- The observed package also reconstructs the entire native filled section. -/
theorem package_section_recovery
    (f : liftedDecode (code S) ⟶ liftedDecode (code T)) (E : HomotopyEquivalence f)
    (p : CubicalStateTransport.StatePackage S) :
    CubicalStructuredState.transported (Raising.lowerMap f) (Raising.lowerEquivalence E) p =
      CubicalStatePackageFamily.pullPackage
        (CubicalStructuredState.admittedLine (Raising.lowerMap f) (Raising.lowerEquivalence E))
        (CubicalStructuredState.admittedPresentation (Raising.lowerMap f) (Raising.lowerEquivalence E))
        (p.conjugate (pathBijection (ua (code S) (code T) f E))) := by
  rw [ua_admittedCarrier]
  exact CubicalStructuredState.transported_recovery _ _ p

/-- Independent 0→1→2 and 0→0→1 calculations detect composition reversal. -/
theorem finite_order_observations :
    pathBijection FiniteUniverseLoops.forwardLoop 0 = (2 : Fin 3) ∧
      pathBijection FiniteUniverseLoops.backwardLoop 0 = (1 : Fin 3) := by
  constructor
  · unfold FiniteUniverseLoops.forwardLoop
    rw [pathBijection_concat, pathBijection_ua, pathBijection_ua]
    rfl
  · unfold FiniteUniverseLoops.backwardLoop
    rw [pathBijection_concat, pathBijection_ua, pathBijection_ua]
    rfl

/-- Mixed carriers: the finite machine keeps the complete transported package. -/
theorem finite_package_observation :
    CubicalStructuredState.targetPackage
      (Raising.lowerMap (nativeMap CubicalFiniteStateIdentity.presentation))
      (Raising.lowerEquivalence (nativeEquivalence CubicalFiniteStateIdentity.presentation))
      CubicalFiniteStateIdentity.machine = CubicalFiniteStateIdentity.presentedMachine := by
  exact (package_observation (nativeMap CubicalFiniteStateIdentity.presentation)
    (nativeEquivalence CubicalFiniteStateIdentity.presentation) CubicalFiniteStateIdentity.machine).trans
    (congrArg CubicalFiniteStateIdentity.machine.conjugate
      (pathBijection_ua CubicalFiniteStateIdentity.presentation))

end Examples.CubicalInterpretationObservations

import Examples.CartesianWitnessPreservation
import SquareKit.Internal.Cubical.CartesianFilling
import SquareKit.Internal.Cubical.CartesianDiscreteRecords

/-! Independently filled Cartesian packages with complete generalized-function recovery. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CartesianPackageRecomputation
open CategoryTheory SquareKit.Cubical
open CartesianWitnessPreservation CubicalStateTransport
open Cartesian
variable {Γ : Cartesian.Context.{0}} {A : Cartesian.Family Γ} {S : Type}

@[ext] theorem package_ext {x : Γ.Elements} {p q : TargetPackage A x}
    (hi : p.initial = q.initial) (hs : p.step = q.step) (hv : p.invariant = q.invariant) : p = q := by
  cases p
  cases q
  cases hi
  cases hs
  cases hv
  congr <;> exact Subsingleton.elim _ _

def fromConstant (e : A ≅ constantFamily Γ S) (x : Γ.Elements) (p : StatePackage S) :
    TargetPackage A x where
  initial := e.inv.app x p.initial
  step := {
    val := fun {y} _ a => e.inv.app y (p.step (e.hom.app y a))
    naturality := by
      intro y z f g a
      change A.map g (e.inv.app y (p.step (e.hom.app y a))) =
        e.inv.app z (p.step (e.hom.app z (A.map g a)))
      rw [← e.inv.naturality_apply, e.hom.naturality_apply]
      rfl }
  invariant := {
    val := fun {y} _ a => p.Invariant (e.hom.app y a)
    naturality := by
      intro y z f g a
      change p.Invariant (e.hom.app y a) = p.Invariant (e.hom.app z (A.map g a))
      rw [e.hom.naturality_apply]
      rfl }
  initialInvariantWitness := ⟨by
    change p.Invariant (e.hom.app x (e.inv.app x p.initial))
    rw [e.inv_hom_id_app_apply]
    exact p.initial_valid⟩
  preserves := fun {y} _ a => ⟨by
    change p.Invariant (e.hom.app y a) →
      p.Invariant (e.hom.app y (e.inv.app y (p.step (e.hom.app y a))))
    rw [e.inv_hom_id_app_apply]
    exact p.preserves _⟩

def toConstant (e : A ≅ constantFamily Γ S) (x : Γ.Elements) (p : TargetPackage A x) :
    StatePackage S := p.readOut.conjugate (e.app x).toEquiv

theorem to_from (e : A ≅ constantFamily Γ S) (x : Γ.Elements) (p : StatePackage S) :
    toConstant e x (fromConstant e x p) = p := by
  apply CubicalStatePackageFamily.statePackage_ext
  · exact e.inv_hom_id_app_apply _ _
  · funext a
    change e.hom.app x (e.inv.app x (p.step (e.hom.app x (e.inv.app x a)))) = p.step a
    rw [e.inv_hom_id_app_apply, e.inv_hom_id_app_apply]
  · funext a
    change p.Invariant (e.hom.app x (e.inv.app x a)) = p.Invariant a
    rw [e.inv_hom_id_app_apply]

theorem from_to (e : A ≅ constantFamily Γ S) (x : Γ.Elements) (p : TargetPackage A x) :
    fromConstant e x (toConstant e x p) = p := by
  apply package_ext
  · exact e.hom_inv_id_app_apply _ _
  · apply PiElement.ext
    intro y f a
    have lift (s : S) : A.map f (e.inv.app x s) = e.inv.app y s :=
      (e.inv.naturality_apply f s).symm
    have ha : A.map f (e.inv.app x (e.hom.app y a)) = a :=
      (lift _).trans (e.hom_inv_id_app_apply _ _)
    have h := p.step.naturality (𝟙 x) f (e.inv.app x (e.hom.app y a))
    change A.map f (p.step.val (𝟙 x) (e.inv.app x (e.hom.app y a))) =
      p.step.val ((𝟙 x) ≫ f) (A.map f (e.inv.app x (e.hom.app y a))) at h
    rw [Category.id_comp, ha] at h
    change e.inv.app y (e.hom.app x (p.step.val (𝟙 x) (e.inv.app x (e.hom.app y a)))) = _
    exact (lift _).symm.trans ((congrArg (A.map f)
      (e.hom_inv_id_app_apply x _)).trans h)
  · apply PiElement.ext
    intro y f a
    have ha : A.map f (e.inv.app x (e.hom.app y a)) = a :=
      (e.inv.naturality_apply f _).symm.trans (e.hom_inv_id_app_apply _ _)
    have h := p.invariant.naturality (𝟙 x) f (e.inv.app x (e.hom.app y a))
    change p.invariant.val (𝟙 x) (e.inv.app x (e.hom.app y a)) =
      p.invariant.val ((𝟙 x) ≫ f) (A.map f (e.inv.app x (e.hom.app y a))) at h
    rw [Category.id_comp, ha] at h
    exact h

def packageRestrict {x y : Γ.Elements} (f : x ⟶ y) (p : TargetPackage A x) :
    TargetPackage A y where
  initial := A.map f p.initial
  step := p.step.restrict f
  invariant := p.invariant.restrict f
  initialInvariantWitness := ⟨by
    have h := p.invariant.naturality (𝟙 x) f p.initial
    change p.invariant.val (𝟙 x) p.initial =
      p.invariant.val ((𝟙 x) ≫ f) (A.map f p.initial) at h
    change p.invariant.val (f ≫ 𝟙 y) (A.map f p.initial)
    rw [Category.id_comp] at h
    rw [Category.comp_id, ← h]
    exact p.initialInvariantWitness.down⟩
  preserves := fun g a => p.preserves (f ≫ g) a

def packageFamily (A : Cartesian.Family Γ) : Cartesian.Family Γ where
  obj x := TargetPackage A x
  map f := TypeCat.ofHom (packageRestrict f)
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro p
    apply package_ext
    · exact ConcreteCategory.congr_hom (A.map_id x) p.initial
    · apply PiElement.ext
      intro y f a
      exact congrArg (fun g => p.step.val g a) (Category.id_comp f)
    · apply PiElement.ext
      intro y f a
      exact congrArg (fun g => p.invariant.val g a) (Category.id_comp f)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro p
    apply package_ext
    · exact ConcreteCategory.congr_hom (A.map_comp f g) p.initial
    · apply PiElement.ext
      intro y h a
      exact congrArg (fun k => p.step.val k a) (Category.assoc f g h)
    · apply PiElement.ext
      intro y h a
      exact congrArg (fun k => p.invariant.val k a) (Category.assoc f g h)

theorem fromConstant_natural (e : A ≅ constantFamily Γ S) {x y : Γ.Elements}
    (f : x ⟶ y) (p : StatePackage S) :
    packageRestrict f (fromConstant e x p) = fromConstant e y p := by
  apply package_ext
  · exact (e.inv.naturality_apply f p.initial).symm
  · rfl
  · rfl

/-- Classification retains both generalized functions and both dependent proof fields. -/
def packagePresentation (e : A ≅ constantFamily Γ S) :
    packageFamily A ≅ constantFamily Γ (StatePackage S) :=
  (NatIso.ofComponents (F := constantFamily Γ (StatePackage S)) (G := packageFamily A)
    (fun x => (show StatePackage S ≃ TargetPackage A x from {
    toFun := fromConstant e x
    invFun := toConstant e x
    left_inv := to_from e x
    right_inv := from_to e x }).toIso) (by
      intro x y f
      apply ConcreteCategory.hom_ext
      intro p
      exact (fromConstant_natural e f p).symm)).symm

def pullTargetPackage (e : A ≅ constantFamily Γ S) (p : StatePackage S) :
    Cartesian.Term (packageFamily A) :=
  Cartesian.Term.map (packagePresentation e).inv ⟨fun _ => p, fun _ => rfl⟩

def emptySubcontext (Γ : Cartesian.Context.{0}) : Subcontext Γ where
  Holds _ := False
  natural _ := False.elim

def packageBox {A : Cartesian.Family (Cartesian.total (Cartesian.interval Γ))}
    (e : A ≅ constantFamily _ S) (r : Cartesian.Term (Cartesian.interval Γ))
    (p : StatePackage S) : OpenBox (packageFamily A) (emptySubcontext Γ) r where
  tube := { val := fun _ h => h.elim, natural := fun _ h => h.elim }
  base := Cartesian.Term.reindex (pullTargetPackage e p) (graph r)
  boundary _ h := h.elim

/-- Recompute by the target all-box operation, supplied only the source graph. -/
def recomputed {A : Cartesian.Family (Cartesian.total (Cartesian.interval Γ))}
    (e : A ≅ constantFamily _ S) (r : Cartesian.Term (Cartesian.interval Γ))
    (p : StatePackage S) : Cartesian.Term (packageFamily A) :=
  (packageBox e r p).presentedFill (packagePresentation e)

theorem recomputed_eq {A : Cartesian.Family (Cartesian.total (Cartesian.interval Γ))}
    (e : A ≅ constantFamily _ S) (r : Cartesian.Term (Cartesian.interval Γ))
    (p : StatePackage S) : recomputed e r p = pullTargetPackage e p :=
  ((packageBox e r p).presentedFill_unique (packagePresentation e) (pullTargetPackage e p) rfl).symm

theorem recomputed_fills {A : Cartesian.Family (Cartesian.total (Cartesian.interval Γ))}
    (e : A ≅ constantFamily _ S) (r : Cartesian.Term (Cartesian.interval Γ))
    (p : StatePackage S) : (packageBox e r p).Fills (recomputed e r p) :=
  (packageBox e r p).presentedFill_fills (packagePresentation e)

theorem source_pull_comparison {Δ : Presheaf.Context.{0}}
    (A : Presheaf.LocalFamily Δ) (e : A.family ≅ Presheaf.constantFamily Δ S)
    (p : StatePackage S) (τ : Γ ⟶ Cartesian.restrict Δ) (x : Γ.Elements) :
    (packageComparison A (τ.mapElements.obj x)
      ((CubicalStatePackageFamily.pullPackage A e p).val
        ((Cartesian.elements Δ).obj (τ.mapElements.obj x)))).reindex τ x =
    fromConstant (Functor.isoWhiskerLeft τ.mapElements
      (Functor.isoWhiskerLeft (Cartesian.elements Δ) e)) x p := by
  apply package_ext
  · rfl
  · apply PiElement.ext
    intro y f a
    rfl
  · apply PiElement.ext
    intro y f a
    rfl

theorem package_filling_lawful (e : A ≅ constantFamily Γ S) :
    (presentedFilling (packagePresentation e)).Lawful :=
  presentedFilling_lawful (packagePresentation e)

theorem pullTargetPackage_reindex {Δ : Cartesian.Context.{0}}
    (e : A ≅ constantFamily Γ S) (p : StatePackage S) (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    ((pullTargetPackage e p).val (σ.mapElements.obj x)).reindex σ x =
      (pullTargetPackage (Functor.isoWhiskerLeft σ.mapElements e) p).val x := by
  apply package_ext <;> rfl

theorem recomputed_reindex {Δ : Cartesian.Context.{0}}
    {A : Cartesian.Family (Cartesian.total (Cartesian.interval Γ))}
    (e : A ≅ constantFamily _ S) (r : Cartesian.Term (Cartesian.interval Γ))
    (p : StatePackage S) (σ : Δ ⟶ Γ) (x : (Cartesian.total (Cartesian.interval Δ)).Elements) :
    ((recomputed e r p).val ((intervalSub σ).mapElements.obj x)).reindex (intervalSub σ) x =
      (recomputed (Functor.isoWhiskerLeft (intervalSub σ).mapElements e)
        (Cartesian.Term.reindex r σ) p).val x := by
  exact (congrArg (fun t : Cartesian.Term (packageFamily A) =>
    (t.val ((intervalSub σ).mapElements.obj x)).reindex (intervalSub σ) x)
      (recomputed_eq e r p)).trans
    ((pullTargetPackage_reindex e p (intervalSub σ) x).trans
      (congrArg (fun t => t.val x) (recomputed_eq
        (Functor.isoWhiskerLeft (intervalSub σ).mapElements e)
        (Cartesian.Term.reindex r σ) p)).symm)

def endpointTerm (Γ : Cartesian.Context.{0}) (b : Bool) : Cartesian.Term (Cartesian.interval Γ) where
  val x := ⟨Cartesian.Cube.endpoint x.obj.unop b⟩
  property _ := rfl

open CubicalFiniteStateIdentity CubicalStructuredState

noncomputable def selectedCarrier := Cartesian.relativeFamily
  (admittedLine (CubicalUnivalenceTransport.codeIso presentation).hom nativeEquivalence).family

noncomputable def selectedPresentation : selectedCarrier ≅
    constantFamily (Cartesian.total (Cartesian.interval (Cartesian.restrict Presheaf.terminal))) Phase :=
  Functor.isoWhiskerLeft (Cartesian.intervalElements Presheaf.terminal)
    (admittedPresentation (CubicalUnivalenceTransport.codeIso presentation).hom nativeEquivalence)

noncomputable def selectedHostPackage := machine.conjugate
  (admittedCarrier (CubicalUnivalenceTransport.codeIso presentation).hom nativeEquivalence)

noncomputable def recomputedSelected : Cartesian.Term (packageFamily selectedCarrier) :=
  recomputed selectedPresentation (endpointTerm (Cartesian.restrict Presheaf.terminal) false)
    selectedHostPackage

/-- Exact equality includes the operation and invariant at every generalized input. -/
theorem recomputedSelected_eq (x : (Cartesian.total
    (Cartesian.interval (Cartesian.restrict Presheaf.terminal))).Elements) :
    recomputedSelected.val x = cartesianPackage x := by
  rw [recomputedSelected, recomputed_eq]
  change fromConstant selectedPresentation x selectedHostPackage = _
  have h := source_pull_comparison
    (admittedLine (CubicalUnivalenceTransport.codeIso presentation).hom nativeEquivalence)
    (admittedPresentation (CubicalUnivalenceTransport.codeIso presentation).hom nativeEquivalence)
    selectedHostPackage (Cartesian.intervalContextInclusion Presheaf.terminal) x
  have hr := transported_recovery (CubicalUnivalenceTransport.codeIso presentation).hom nativeEquivalence machine
  change fromConstant selectedPresentation x selectedHostPackage =
    (packageComparison _ ((Cartesian.intervalContextInclusion Presheaf.terminal).mapElements.obj x)
      (frozenPackage.val ((Cartesian.intervalElements Presheaf.terminal).obj x))).reindex
        (Cartesian.intervalContextInclusion Presheaf.terminal) x
  rw [show frozenPackage = _ from hr]
  exact h.symm

/-- Recomputing after a base change preserves the entire selected package. -/
theorem recomputedSelected_reindex {Δ : Cartesian.Context.{0}}
    (σ : Δ ⟶ Cartesian.restrict Presheaf.terminal)
    (x : (Cartesian.total (Cartesian.interval Δ)).Elements) :
    (recomputed (Functor.isoWhiskerLeft (intervalSub σ).mapElements selectedPresentation)
      (Cartesian.Term.reindex (endpointTerm (Cartesian.restrict Presheaf.terminal) false) σ)
      selectedHostPackage).val x =
    (cartesianPackage ((intervalSub σ).mapElements.obj x)).reindex (intervalSub σ) x := by
  rw [← recomputed_reindex, ← recomputedSelected_eq]
  rfl

/-- Two actual interval projections preserve the freshly recomputed package. -/
theorem recomputedSelected_two_projections (x) :
    let τ := Cartesian.projection (Cartesian.interval (Cartesian.restrict Presheaf.terminal));
    let σ := Cartesian.projection (Cartesian.interval (Cartesian.total
      (Cartesian.interval (Cartesian.restrict Presheaf.terminal))));
    (recomputed (Functor.isoWhiskerLeft (intervalSub (σ ≫ τ)).mapElements selectedPresentation)
      (Cartesian.Term.reindex (endpointTerm (Cartesian.restrict Presheaf.terminal) false) (σ ≫ τ))
      selectedHostPackage).val x =
    (cartesianPackage ((intervalSub (σ ≫ τ)).mapElements.obj x)).reindex (intervalSub (σ ≫ τ)) x :=
  recomputedSelected_reindex _ x

noncomputable def recomputedFinish : StatePackage Phase :=
  (recomputedSelected.val (targetEndpoint true)).readOut.conjugate
    ((admittedFinish (CubicalUnivalenceTransport.codeIso presentation).hom nativeEquivalence).app
      Presheaf.DiscreteEquivalences.point).toEquiv

theorem recomputedFinish_eq : recomputedFinish = machineTransported := by
  unfold recomputedFinish
  rw [recomputedSelected_eq]
  exact cartesianFinish_eq

theorem recomputed_observation : observer (recomputedFinish.step recomputedFinish.initial) = 1 := by
  rw [recomputedFinish_eq]
  exact transported_observation

theorem recomputed_invariant : recomputedFinish.Invariant .ready ∧ ¬ recomputedFinish.Invariant .failed := by
  rw [recomputedFinish_eq]
  exact transported_invariant

theorem recomputed_wrong_transition :
    wrongPresentation (machine.step 0) ≠ recomputedFinish.step (wrongPresentation 0) := by
  rw [recomputedFinish_eq, machineTransported_eq]
  exact wrong_transition

end Examples.CartesianPackageRecomputation

namespace Examples.CartesianPackageRecomputation.NativeRecords
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open SmallUniverse SmallUniverse.NativeUnivalence
open Examples.CompositionalUnivalence

def presentation (S : Type) : liftedDecode (code S) ≅
    constantFamily (raisedContext terminal) (ULift.{1} S) :=
  Raising.iso (Examples.CubicalGlue.constantLocal terminal S).decodeCodeIso

theorem inverse_record {S T : Type} (e : S ≃ T) :
    (⟨inverseMap (code S) (code T) (nativeMap e) (nativeEquivalence e),
      inverseEquivalence (code S) (code T) (nativeMap e) (nativeEquivalence e)⟩ :
      Σ f : liftedDecode (code T) ⟶ liftedDecode (code S), HomotopyEquivalence f) =
    ⟨(Raising.iso (Examples.CubicalUnivalenceTransport.codeIso e)).inv,
      HomotopyEquivalence.ofIso (Raising.iso (Examples.CubicalUnivalenceTransport.codeIso e)).symm⟩ :=
  DiscreteRecords.inverseEquivalence_record (code S) (code T) (presentation S) (presentation T)
    (Raising.iso (Examples.CubicalUnivalenceTransport.codeIso e)) (nativeEquivalence e)

theorem inverse_recipes {S T : Type} (e : S ≃ T) :
    (nativeEquivalence e).discreteInverse = inverseMap (code S) (code T) (nativeMap e)
      (nativeEquivalence e) :=
  DiscreteRecords.discreteInverse_eq_inverseMap (code S) (code T) (presentation S) (presentation T)
    (Raising.iso (Examples.CubicalUnivalenceTransport.codeIso e)) (nativeEquivalence e)

theorem composite_record {S T V : Type} (e : S ≃ T) (d : T ≃ V) :
    (⟨nativeMap e ≫ nativeMap d,
      compositeEquivalence (code S) (code T) (code V) (nativeMap e) (nativeEquivalence e)
        (nativeMap d) (nativeEquivalence d)⟩ :
      Σ f : liftedDecode (code S) ⟶ liftedDecode (code V), HomotopyEquivalence f) =
    ⟨(Raising.iso (Examples.CubicalUnivalenceTransport.codeIso e) ≪≫
      Raising.iso (Examples.CubicalUnivalenceTransport.codeIso d)).hom,
      HomotopyEquivalence.ofIso (Raising.iso (Examples.CubicalUnivalenceTransport.codeIso e) ≪≫
        Raising.iso (Examples.CubicalUnivalenceTransport.codeIso d))⟩ :=
  DiscreteRecords.compositeEquivalence_record (code S) (code T) (code V) (presentation S) (presentation V)
    (Raising.iso (Examples.CubicalUnivalenceTransport.codeIso e))
    (Raising.iso (Examples.CubicalUnivalenceTransport.codeIso d))
    (nativeEquivalence e) (nativeEquivalence d)
def restrictRecord {Γ : Presheaf.Context} {A B : Presheaf.Family Γ}
    (p : Σ f : A ⟶ B, HomotopyEquivalence f) : Σ f : A ⟶ B, Cartesian.Equivalence f :=
  ⟨p.1, Cartesian.restrictEquivalence p.2⟩

theorem inverse_recomputed {S T : Type} (e : S ≃ T) :
    restrictRecord ⟨inverseMap (code S) (code T) (nativeMap e) (nativeEquivalence e),
      inverseEquivalence (code S) (code T) (nativeMap e) (nativeEquivalence e)⟩ =
    ⟨(Raising.iso (Examples.CubicalUnivalenceTransport.codeIso e)).inv,
      Cartesian.recomputeEquivalence (presentation S)
        (Raising.iso (Examples.CubicalUnivalenceTransport.codeIso e)).symm⟩ := by
  have h := congrArg restrictRecord (inverse_record e)
  exact h.trans (congrArg (Sigma.mk _)
    (Cartesian.recomputeEquivalence_eq (presentation S)
      (Raising.iso (Examples.CubicalUnivalenceTransport.codeIso e)).symm _).symm)

theorem composite_recomputed {S T V : Type} (e : S ≃ T) (d : T ≃ V) :
    restrictRecord ⟨nativeMap e ≫ nativeMap d,
      compositeEquivalence (code S) (code T) (code V) (nativeMap e) (nativeEquivalence e)
        (nativeMap d) (nativeEquivalence d)⟩ =
    ⟨(Raising.iso (Examples.CubicalUnivalenceTransport.codeIso e) ≪≫
      Raising.iso (Examples.CubicalUnivalenceTransport.codeIso d)).hom,
      Cartesian.recomputeEquivalence (presentation V)
        (Raising.iso (Examples.CubicalUnivalenceTransport.codeIso e) ≪≫
          Raising.iso (Examples.CubicalUnivalenceTransport.codeIso d))⟩ := by
  have h := congrArg restrictRecord (composite_record e d)
  exact h.trans (congrArg (Sigma.mk _)
    (Cartesian.recomputeEquivalence_eq (presentation V)
      (Raising.iso (Examples.CubicalUnivalenceTransport.codeIso e) ≪≫
        Raising.iso (Examples.CubicalUnivalenceTransport.codeIso d)) _).symm)

example : (nativeEquivalence Examples.FiniteUniverseLoops.swap01).discreteInverse =
    inverseMap (code (Fin 3)) (code (Fin 3)) (nativeMap Examples.FiniteUniverseLoops.swap01)
      (nativeEquivalence Examples.FiniteUniverseLoops.swap01) := inverse_recipes _
end Examples.CartesianPackageRecomputation.NativeRecords

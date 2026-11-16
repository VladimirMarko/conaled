import SquareKit.Internal.Cubical.CartesianWitnesses
import Examples.FiniteUniverseLoops
import Examples.CubicalFiniteStateIdentity

/-! Cartesian restriction on the selected finite universe and dependent state witnesses. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CartesianWitnessPreservation
open CategoryTheory
open SquareKit.Cubical

/-- Restriction of the De Morgan represented interval is not the Cartesian interval. -/
theorem no_interval_retraction
    (η : Cartesian.inclusion.op ⋙ yoneda.obj (⟨1⟩ : SquareKit.Cubical.Cube) ⟶
      yoneda.obj (⟨1⟩ : Cartesian.Cube))
    (h : ∀ b, η.app (.op ⟨0⟩) (Cube.endpoint ⟨0⟩ b) = Cartesian.Cube.endpoint ⟨0⟩ b) : False := by
  have hn (b : Bool) := η.naturality_apply (Quiver.Hom.op (Cartesian.Cube.endpoint ⟨0⟩ b)) Cube.reversal
  have he (b : Bool) : Cartesian.Cube.comp (Cartesian.Cube.endpoint ⟨0⟩ b)
      (η.app (.op ⟨1⟩) Cube.reversal) = Cartesian.Cube.endpoint ⟨0⟩ (!b) := by
    have hh := hn b
    change η.app (.op ⟨0⟩) (Cube.comp (Cartesian.inclusion.map (Cartesian.Cube.endpoint ⟨0⟩ b)) Cube.reversal) =
      Cartesian.Cube.comp (Cartesian.Cube.endpoint ⟨0⟩ b) (η.app (.op ⟨1⟩) Cube.reversal) at hh
    rw [Cartesian.inclusion_endpoint] at hh
    exact hh.symm.trans ((congrArg (η.app (.op ⟨0⟩)) (Cube.endpoint_reversal ⟨0⟩ b)).trans (h (!b)))
  have h₀ := congrFun (he false) 0
  have h₁ := congrFun (he true) 0
  change Cartesian.Dim.subst (Cartesian.Cube.endpoint ⟨0⟩ false) ((η.app (.op ⟨1⟩) Cube.reversal) 0) = .endpoint true at h₀
  change Cartesian.Dim.subst (Cartesian.Cube.endpoint ⟨0⟩ true) ((η.app (.op ⟨1⟩) Cube.reversal) 0) = .endpoint false at h₁
  cases hv : ((η.app (.op ⟨1⟩) Cube.reversal) 0) with
  | endpoint b =>
    cases b <;> simp [hv, Cartesian.Dim.subst] at h₀ h₁
  | var i =>
    have hi := Fin.eq_zero i
    subst i
    simp [hv, Cartesian.Dim.subst, Cartesian.Cube.endpoint] at h₀


open CubicalStatePackageFamily CubicalStateTransport

/-- The target package uses Cartesian generalized functions for both operation and predicate.
The two dependent proof fields are retained at all generalized arguments. -/
structure TargetPackage {Γ : Cartesian.Context.{0}} (A : Cartesian.Family Γ) (x : Γ.Elements) where
  initial : A.obj x
  step : Cartesian.PiElement A ((Cartesian.projection A).mapElements ⋙ A) x
  invariant : Cartesian.PiElement A ((Functor.const (Cartesian.total A).Elements).obj Prop) x
  initial_valid : PLift (invariant.val (𝟙 x) initial)
  preserves : ∀ {y : Γ.Elements} (f : x ⟶ y) (a : A.obj y),
    PLift (invariant.val f a → invariant.val f (step.val f a))

noncomputable def packageComparison {Γ : Presheaf.Context.{0}} (A : Presheaf.LocalFamily Γ)
    (x : (Cartesian.restrict Γ).Elements) (z : (package A).family.obj ((Cartesian.elements Γ).obj x)) :
    TargetPackage (Cartesian.restrictFamily A.family) x where
  initial := z.1.1
  step := (Cartesian.piComparison A.family (Presheaf.reindex A.family (Presheaf.projection A.family))).app x z.1.2.1
  invariant := (Cartesian.piComparison A.family (Presheaf.constantFamily (Presheaf.total A.family) Prop)).app x z.1.2.2
  initial_valid := z.2.1
  preserves {y} f a := by
    have h := z.2.2.val (Presheaf.extendHom (data A).family ((Cartesian.elements Γ).map f) z.1) a
    change PLift (z.1.2.2.val (((Cartesian.elements Γ).map f) ≫ 𝟙 _) a →
      z.1.2.2.val (((Cartesian.elements Γ).map f) ≫ 𝟙 _)
        (z.1.2.1.val (((Cartesian.elements Γ).map f) ≫ 𝟙 _) a)) at h
    exact cast (congrArg (fun k => PLift (z.1.2.2.val k a →
      z.1.2.2.val k (z.1.2.1.val k a))) (Category.comp_id ((Cartesian.elements Γ).map f))) h

def TargetPackage.readOut {Γ : Cartesian.Context.{0}} {A : Cartesian.Family Γ}
    {x : Γ.Elements} (z : TargetPackage A x) : StatePackage (A.obj x) where
  initial := z.initial
  step a := z.step.val (𝟙 x) a
  invariant a := z.invariant.val (𝟙 x) a
  initial_valid := z.initial_valid.down
  preserves a h := (z.preserves (𝟙 x) a).down h

/-- Equality of the full five-field readout includes the dependent proof fields. -/
theorem packageComparison_readOut {Γ : Presheaf.Context.{0}} (A : Presheaf.LocalFamily Γ)
    (x : (Cartesian.restrict Γ).Elements) (z : (package A).family.obj ((Cartesian.elements Γ).obj x)) :
    (packageComparison A x z).readOut = readOut A ((Cartesian.elements Γ).obj x) z := rfl

open CubicalFiniteStateIdentity CubicalStructuredState CubicalStatePackageUa

noncomputable def frozenPackage :=
  CubicalStructuredState.transported (CubicalUnivalenceTransport.codeIso presentation).hom
    CubicalFiniteStateIdentity.nativeEquivalence machine

/-- The chosen filled section itself is retained before any forward Pi comparison. -/
noncomputable def restrictedPackage := Cartesian.restrictTerm frozenPackage

theorem restrictedPackage_recovers (s : Presheaf.Term (package
    (admittedLine (CubicalUnivalenceTransport.codeIso presentation).hom
      CubicalFiniteStateIdentity.nativeEquivalence)).family)
    (h : Cartesian.restrictTerm s = restrictedPackage) : s = frozenPackage :=
  Cartesian.restrictTerm_injective h

/-- Every Cartesian generalized point retains all five fields of the chosen filler. -/
theorem frozenPackage_five_fields (x : (Cartesian.restrict _).Elements) :
    (packageComparison _ x (restrictedPackage.val x)).readOut =
      readOut _ ((Cartesian.elements _).obj x) (frozenPackage.val ((Cartesian.elements _).obj x)) :=
  packageComparison_readOut _ x _

end Examples.CartesianWitnessPreservation
namespace Examples.CartesianWitnessPreservation
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open SmallUniverse SmallUniverse.NativeUnivalence
open Examples.CompositionalUnivalence FiniteUniverseLoops
noncomputable def cartesianLoop {S : Type} (p : Term (loops S)) := Cartesian.homogeneousTerm p
noncomputable abbrev cartesianTwoPaths {S : Type} (p q : Term (loops S)) :=
  Cartesian.homogeneousPath _ (cartesianLoop p) (cartesianLoop q)
theorem reflect_closed_twoPath {S : Type} (p q : Term (loops S))
    (h : Cartesian.Term (cartesianTwoPaths p q)) :
    Nonempty (Term (homogeneousPath (loops S) p q)) := by
  let e := Cartesian.twoPathIso (family (raisedContext terminal)) (term (code S)) (term (code S)) p q
  exact ⟨Cartesian.recoverClosedTerm (fun _ => (show Subsingleton (ULift PUnit) from inferInstance)) (ULift.up PUnit.unit)
    (Cartesian.Term.map e.inv h)⟩
theorem boolean_no_twoPath :
    ¬ Nonempty (Cartesian.Term (cartesianTwoPaths booleanIdentityLoop booleanNegationLoop)) :=
  fun ⟨h⟩ => booleanLoops_no_twoPath (reflect_closed_twoPath _ _ h)
theorem fin3_no_twoPath :
    ¬ Nonempty (Cartesian.Term (cartesianTwoPaths forwardLoop backwardLoop)) :=
  fun ⟨h⟩ => compositeLoops_no_twoPath (reflect_closed_twoPath _ _ h)
end Examples.CartesianWitnessPreservation
namespace Examples.CartesianWitnessPreservation
open CategoryTheory SquareKit.Cubical
open CubicalStatePackageFamily CubicalStateTransport
/-- Pull all five package fields back along a target context substitution. -/
def TargetPackage.reindex {Γ Δ : Cartesian.Context.{0}} {A : Cartesian.Family Γ}
    (τ : Δ ⟶ Γ) (x : Δ.Elements) (z : TargetPackage A (τ.mapElements.obj x)) :
    TargetPackage (τ.mapElements ⋙ A) x where
  initial := z.initial
  step := {
    val := fun f a => z.step.val (τ.mapElements.map f) a
    naturality := fun f g a => z.step.naturality (τ.mapElements.map f) (τ.mapElements.map g) a }
  invariant := {
    val := fun f a => z.invariant.val (τ.mapElements.map f) a
    naturality := fun f g a => z.invariant.naturality (τ.mapElements.map f) (τ.mapElements.map g) a }
  initial_valid := z.initial_valid
  preserves f a := z.preserves (τ.mapElements.map f) a

theorem TargetPackage.reindex_readOut {Γ Δ : Cartesian.Context.{0}} {A : Cartesian.Family Γ}
    (τ : Δ ⟶ Γ) (x : Δ.Elements) (z : TargetPackage A (τ.mapElements.obj x)) :
    (z.reindex τ x).readOut = z.readOut := rfl

open CubicalFiniteStateIdentity CubicalStructuredState CubicalStatePackageUa
noncomputable def cartesianPackage (x : (Cartesian.total (Cartesian.interval
    (Cartesian.restrict Presheaf.terminal.{0}))).Elements) :=
  (packageComparison _ ((Cartesian.intervalContextInclusion Presheaf.terminal).mapElements.obj x)
    ((Cartesian.relativeTerm frozenPackage).val x)).reindex
      (Cartesian.intervalContextInclusion Presheaf.terminal) x

/-- Recovery uses the actual Cartesian interval section before forward Pi comparison. -/
theorem cartesianPackageSection_recovers {s}
    (h : Cartesian.relativeTerm s = Cartesian.relativeTerm frozenPackage) : s = frozenPackage :=
  Cartesian.relativeTerm_injective h

theorem cartesianPackage_five_fields (x : (Cartesian.total (Cartesian.interval
    (Cartesian.restrict Presheaf.terminal.{0}))).Elements) :
    (cartesianPackage x).readOut =
      readOut _ ((Cartesian.intervalElements _).obj x)
        (frozenPackage.val ((Cartesian.intervalElements _).obj x)) := rfl
end Examples.CartesianWitnessPreservation
namespace Examples.CartesianWitnessPreservation
open CategoryTheory SquareKit.Cubical
open CubicalStatePackageFamily CubicalStateTransport

theorem TargetPackage.reindex_comp {Γ Δ Θ : Cartesian.Context.{0}} {A : Cartesian.Family Γ}
    (τ : Δ ⟶ Γ) (σ : Θ ⟶ Δ) (x : Θ.Elements)
    (z : TargetPackage A ((σ ≫ τ).mapElements.obj x)) :
    (z.reindex τ (σ.mapElements.obj x)).reindex σ x = z.reindex (σ ≫ τ) x := rfl

open CubicalFiniteStateIdentity CubicalStructuredState CubicalStatePackageUa

def targetEndpoint (b : Bool) : (Cartesian.total (Cartesian.interval
    (Cartesian.restrict Presheaf.terminal.{0}))).Elements :=
  (Cartesian.total (Cartesian.interval (Cartesian.restrict Presheaf.terminal))).elementsMk
    (.op ⟨0⟩) ⟨PUnit.unit, ⟨Cartesian.Cube.endpoint ⟨0⟩ b⟩⟩

noncomputable def cartesianFinish : StatePackage Phase :=
  (cartesianPackage (targetEndpoint true)).readOut.conjugate
    ((admittedFinish (CubicalUnivalenceTransport.codeIso presentation).hom nativeEquivalence).app
      Presheaf.DiscreteEquivalences.point).toEquiv

theorem cartesianFinish_eq : cartesianFinish = machineTransported := rfl

theorem cartesianFinish_observation : observer (cartesianFinish.step cartesianFinish.initial) = 1 :=
  transported_observation

theorem cartesianFinish_invariant : cartesianFinish.invariant .ready ∧ ¬ cartesianFinish.invariant .failed :=
  transported_invariant

theorem cartesian_wrong_transition :
    wrongPresentation (machine.step 0) ≠ cartesianFinish.step (wrongPresentation 0) := by
  rw [cartesianFinish_eq, machineTransported_eq]
  exact wrong_transition
end Examples.CartesianWitnessPreservation
namespace Examples.CartesianWitnessPreservation
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open SmallUniverse SmallUniverse.NativeUnivalence
open Examples.CompositionalUnivalence FiniteUniverseLoops
universe u
noncomputable def cartesianComparison {Γ : Context.{u+1}} {a b : Γ ⟶ smallFamilyCodes.{u}}
    {p q : Term (paths a b)} (H : Term (homogeneousPath (paths a b) p q)) :=
  Cartesian.Term.map (Cartesian.twoPathIso (family Γ) (term a) (term b) p q).hom
    (Cartesian.restrictTerm H)

theorem cartesianComparison_injective {Γ : Context.{u+1}} {a b : Γ ⟶ smallFamilyCodes.{u}}
    {p q : Term (paths a b)} : Function.Injective (cartesianComparison (p := p) (q := q)) := by
  intro H K h
  apply Cartesian.restrictTerm_injective
  have hi := congrArg (Cartesian.Term.map (Cartesian.twoPathIso (family Γ) (term a) (term b) p q).inv) h
  apply Cartesian.Term.ext
  intro x
  have hx := congrArg (fun t => t.val x) hi
  exact ((congrArg (fun k => k ((Cartesian.restrictTerm H).val x))
    ((Cartesian.twoPathIso (family Γ) (term a) (term b) p q).hom_inv_id_app x)).symm.trans hx).trans
      (congrArg (fun k => k ((Cartesian.restrictTerm K).val x))
        ((Cartesian.twoPathIso (family Γ) (term a) (term b) p q).hom_inv_id_app x))

noncomputable def squareValue {Γ : Context.{u+1}} {a b : Γ ⟶ smallFamilyCodes.{u}}
    {p q : Term (paths a b)} (H : Term (homogeneousPath (paths a b) p q))
    (x : (Cartesian.restrict Γ).Elements) (r s : (Cartesian.interval (Cartesian.restrict Γ)).obj x) :=
  (((cartesianComparison H).val x).val.val (𝟙 x) r).val.val (𝟙 x) s

/-- Both interval coordinates and all interior code values are those of the frozen source square. -/
theorem squareValue_source {Γ : Context.{u+1}} {a b : Γ ⟶ smallFamilyCodes.{u}}
    {p q : Term (paths a b)} (H : Term (homogeneousPath (paths a b) p q))
    (x : (Cartesian.restrict Γ).Elements) (r s : (Cartesian.interval (Cartesian.restrict Γ)).obj x) :
    squareValue H x r s = (comparisonSquare H).val
      ((total (interval (total (interval Γ)))).elementsMk (Cartesian.inclusion.op.obj x.obj)
        ⟨⟨x.val, ⟨Cartesian.inclusion.map r.down⟩⟩, ⟨Cartesian.inclusion.map s.down⟩⟩) := rfl

theorem squareValue_left {Γ : Context.{u+1}} {a b : Γ ⟶ smallFamilyCodes.{u}}
    {p q : Term (paths a b)} (H : Term (homogeneousPath (paths a b) p q))
    (x : (Cartesian.restrict Γ).Elements) (r : (Cartesian.interval (Cartesian.restrict Γ)).obj x) :
    squareValue H x r ⟨Cartesian.Cube.endpoint x.obj.unop false⟩ = (term a).val ((Cartesian.elements Γ).obj x) :=
  ((((cartesianComparison H).val x).val.val (𝟙 x) r).property (𝟙 x)).1

theorem squareValue_right {Γ : Context.{u+1}} {a b : Γ ⟶ smallFamilyCodes.{u}}
    {p q : Term (paths a b)} (H : Term (homogeneousPath (paths a b) p q))
    (x : (Cartesian.restrict Γ).Elements) (r : (Cartesian.interval (Cartesian.restrict Γ)).obj x) :
    squareValue H x r ⟨Cartesian.Cube.endpoint x.obj.unop true⟩ = (term b).val ((Cartesian.elements Γ).obj x) :=
  ((((cartesianComparison H).val x).val.val (𝟙 x) r).property (𝟙 x)).2

theorem squareValue_zero {Γ : Context.{u+1}} {a b : Γ ⟶ smallFamilyCodes.{u}}
    {p q : Term (paths a b)} (H : Term (homogeneousPath (paths a b) p q))
    (x : (Cartesian.restrict Γ).Elements) (s : (Cartesian.interval (Cartesian.restrict Γ)).obj x) :
    squareValue H x ⟨Cartesian.Cube.endpoint x.obj.unop false⟩ s =
      ((Cartesian.homogeneousTerm p).val x).val.val (𝟙 x) s :=
  congrArg (fun v => v.val.val (𝟙 x) s) (((cartesianComparison H).val x).property (𝟙 x)).1

theorem squareValue_one {Γ : Context.{u+1}} {a b : Γ ⟶ smallFamilyCodes.{u}}
    {p q : Term (paths a b)} (H : Term (homogeneousPath (paths a b) p q))
    (x : (Cartesian.restrict Γ).Elements) (s : (Cartesian.interval (Cartesian.restrict Γ)).obj x) :
    squareValue H x ⟨Cartesian.Cube.endpoint x.obj.unop true⟩ s =
      ((Cartesian.homogeneousTerm q).val x).val.val (𝟙 x) s :=
  congrArg (fun v => v.val.val (𝟙 x) s) (((cartesianComparison H).val x).property (𝟙 x)).2

noncomputable def frozenSwapSquare := cartesianComparison swapComposition
noncomputable def frozenComposite := Cartesian.restrictEquivalence
  (compositeEquivalence (code (Fin 3)) (code (Fin 3)) (code (Fin 3))
    (nativeMap swap01) (nativeEquivalence swap01) (nativeMap swap12) (nativeEquivalence swap12))
noncomputable def frozenInverse := Cartesian.restrictEquivalence
  (inverseEquivalence (code (Fin 3)) (code (Fin 3)) (nativeMap swap01) (nativeEquivalence swap01))
end Examples.CartesianWitnessPreservation

namespace Examples.CartesianWitnessPreservation
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open SmallUniverse SmallUniverse.NativeUnivalence
open Examples.CompositionalUnivalence FiniteUniverseLoops

/-- Recovery concerns the chosen square, including its interior, rather than only its boundary. -/
theorem frozenSwapSquare_recovers {H} (h : cartesianComparison H = frozenSwapSquare) :
    comparisonSquare H = comparisonSquare swapComposition :=
  congrArg comparisonSquare (cartesianComparison_injective h)

/-- The top face is the ordered concatenation; reversing the swaps fails the no-two-path control. -/
theorem frozenSwapSquare_top (x : (Cartesian.restrict (raisedContext terminal)).Elements)
    (r : (Cartesian.interval (Cartesian.restrict (raisedContext terminal))).obj x) :
    squareValue swapComposition x ⟨Cartesian.Cube.endpoint x.obj.unop true⟩ r =
      ((cartesianLoop forwardLoop).val x).val.val (𝟙 x) r :=
  squareValue_one swapComposition x r

/-- The original composite contraction survives two nonidentity interval projections. -/
theorem frozenComposite_base_change :
    (frozenComposite.fibers.reindex (Cartesian.projection (Cartesian.interval _))).reindex
      (Cartesian.projection (Cartesian.interval _)) =
    frozenComposite.fibers.reindex
      (Cartesian.projection (Cartesian.interval _) ≫ Cartesian.projection (Cartesian.interval _)) :=
  Cartesian.Contractible.forget_two_intervals _

/-- The same comparison holds for the actual selected inverse record. -/
theorem frozenInverse_base_change :
    (frozenInverse.fibers.reindex (Cartesian.projection (Cartesian.interval _))).reindex
      (Cartesian.projection (Cartesian.interval _)) =
    frozenInverse.fibers.reindex
      (Cartesian.projection (Cartesian.interval _) ≫ Cartesian.projection (Cartesian.interval _)) :=
  Cartesian.Contractible.forget_two_intervals _

/-- Generalized package fields, including both proofs, compose under two interval projections. -/
theorem frozenPackage_base_change (x) :
    let τ := Cartesian.projection (Cartesian.interval (Cartesian.restrict
      (Presheaf.total (Presheaf.interval Presheaf.terminal.{0}))));
    let σ := Cartesian.projection (Cartesian.interval (Cartesian.total (Cartesian.interval
      (Cartesian.restrict (Presheaf.total (Presheaf.interval Presheaf.terminal.{0}))))));
    let z := packageComparison _ ((σ ≫ τ).mapElements.obj x)
      (restrictedPackage.val ((σ ≫ τ).mapElements.obj x));
    (z.reindex τ (σ.mapElements.obj x)).reindex σ x = z.reindex (σ ≫ τ) x := rfl
/-- Iterated restriction preserves the entire chosen square, not only its edge readouts. -/
theorem frozenSwapSquare_base_change :
    Cartesian.Term.reindex (Cartesian.Term.reindex frozenSwapSquare (Cartesian.projection (Cartesian.interval _)))
      (Cartesian.projection (Cartesian.interval _)) =
    Cartesian.Term.reindex frozenSwapSquare
      (Cartesian.projection (Cartesian.interval _) ≫ Cartesian.projection (Cartesian.interval _)) := rfl

example : ¬ Function.Injective ((Cartesian.projection (Cartesian.interval
    (Cartesian.restrict terminal.{0}))).app (.op ⟨0⟩)) :=
  Cartesian.interval_projection_not_injective _ PUnit.unit

example : ¬ Function.Injective ((Cartesian.projection (Cartesian.interval
    (Cartesian.total (Cartesian.interval (Cartesian.restrict terminal.{0}))))).app (.op ⟨0⟩)) :=
  Cartesian.interval_projection_not_injective _ ⟨PUnit.unit, ⟨Cartesian.Cube.endpoint ⟨0⟩ false⟩⟩
end Examples.CartesianWitnessPreservation

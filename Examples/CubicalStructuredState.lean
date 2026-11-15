import Examples.CubicalStatePackageUa
import SquareKit.Internal.Cubical.DiscreteEquivalences

/-! Proof-bearing state paths with a specified discrete carrier presentation. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalStructuredState
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open CubicalStatePackageFamily CubicalStatePackageUa CubicalStateTransport

variable {Γ : Context.{0}} {S : Type}

/-- Reading every generalized point recovers the full native section, including
function values at nonidentity substitutions and both discrete proof fields. -/
theorem readOut_injective (A : LocalFamily Γ) (s t : Term (package A).family)
    (h : ∀ x, readOut A x (s.val x) = readOut A x (t.val x)) : s = t := by
  apply Term.ext
  intro x
  apply package_ext
  apply Sigma.ext
  · exact congrArg StatePackage.initial (h x)
  · apply heq_of_eq
    apply Sigma.ext
    · apply PiElement.ext
      intro y f a
      have hs := congrArg (fun z => z.val (𝟙 y) a) ((stepSection s).property f)
      have ht := congrArg (fun z => z.val (𝟙 y) a) ((stepSection t).property f)
      have he := congrArg (fun z : StatePackage (A.family.obj y) => z.step a) (h y)
      change ((stepSection s).val x).val (f ≫ 𝟙 y) a = _ at hs
      change ((stepSection t).val x).val (f ≫ 𝟙 y) a = _ at ht
      have hc : f ≫ 𝟙 y = f := Category.comp_id f
      exact (congrArg (fun k => ((stepSection s).val x).val k a) hc).symm.trans
        ((hs.trans (he.trans ht.symm)).trans (congrArg (fun k => ((stepSection t).val x).val k a) hc))
    · apply heq_of_eq
      apply PiElement.ext
      intro y f a
      have hs := congrArg (fun z => z.val (𝟙 y) a) ((invariantSection s).property f)
      have ht := congrArg (fun z => z.val (𝟙 y) a) ((invariantSection t).property f)
      have he := congrArg (fun z : StatePackage (A.family.obj y) => z.invariant a) (h y)
      change ((invariantSection s).val x).val (f ≫ 𝟙 y) a = _ at hs
      change ((invariantSection t).val x).val (f ≫ 𝟙 y) a = _ at ht
      have hc : f ≫ 𝟙 y = f := Category.comp_id f
      exact (congrArg (fun k => ((invariantSection s).val x).val k a) hc).symm.trans
        ((hs.trans (he.trans ht.symm)).trans (congrArg (fun k => ((invariantSection t).val x).val k a) hc))

theorem observe_injective (A : LocalFamily Γ)
    (e : A.family ≅ constantFamily Γ S) : Function.Injective (observe A e) := by
  intro s t h
  apply readOut_injective A
  intro x
  have he := congrArg (fun z => (z.val x).conjugate (e.app x).toEquiv.symm) h
  change ((readOut A x (s.val x)).conjugate (e.app x).toEquiv).conjugate _ =
    ((readOut A x (t.val x)).conjugate (e.app x).toEquiv).conjugate _ at he
  simpa only [conjugate_symm] using he

/-- A full section on the interval is fixed by its initial restriction. This
is a theorem of the discrete presentation, not proof irrelevance for paths. -/
theorem section_initial_injective (A : LocalFamily (total (interval Γ)))
    (e : A.family ≅ constantFamily (total (interval Γ)) S)
    (s t : Term (package A).family)
    (h : s.reindex (endpointSub Γ false) = t.reindex (endpointSub Γ false)) : s = t := by
  apply observe_injective A e
  apply Term.ext
  intro x
  rcases x with @⟨I, ⟨γ, r⟩⟩
  let y := Γ.elementsMk I γ
  let z := extendObj (interval Γ) y ((endpoint Γ false).val y)
  calc
    _ = (observe A e s).val z := constant_section_interval _ y r ((endpoint Γ false).val y)
    _ = (observe A e t).val z := congrArg
      (fun v => (readOut A z v).conjugate (e.app z).toEquiv) (congrArg (fun v => v.val y) h)
    _ = _ := constant_section_interval _ y ((endpoint Γ false).val y) r

/-- Exact recovery of the native six-field section from its initial value. -/
theorem filling_recovery (A : LocalFamily (total (interval Γ)))
    (e : A.family ≅ constantFamily (total (interval Γ)) S)
    (s : Term (package A).family) :
    IntervalTransport.forward (package A).toNative.filling (𝟙 Γ)
      (s.reindex (endpointSub Γ false)) = s :=
  section_initial_injective A e _ s
    (IntervalTransport.forward_zero (package A).toNative.filling (package A).toNative.lawful (𝟙 Γ) _)

end Examples.CubicalStructuredState

namespace Examples.CubicalStructuredState
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open CubicalStatePackageFamily CubicalStatePackageUa CubicalStateTransport

variable {S T : Type}

/-- Preservation includes the dependent invariant and both proof fields.
Those fields are discrete PLift propositions in the admitted native package. -/
structure Preserves (e : S ≃ T) (p : StatePackage S) (q : StatePackage T) : Prop where
  initial : (p.conjugate e).initial = q.initial
  step : (p.conjugate e).step = q.step
  invariant : (p.conjugate e).invariant = q.invariant
  initial_valid : HEq (p.conjugate e).initial_valid q.initial_valid
  preserves : HEq (p.conjugate e).preserves q.preserves

theorem Preserves.package_eq {e : S ≃ T} {p : StatePackage S} {q : StatePackage T}
    (h : Preserves e p q) : p.conjugate e = q :=
  statePackage_ext _ _ h.initial h.step h.invariant

theorem Preserves.of_eq {e : S ≃ T} {p : StatePackage S} {q : StatePackage T}
    (h : p.conjugate e = q) : Preserves e p q := by
  cases h
  exact ⟨rfl, rfl, rfl, HEq.rfl, HEq.rfl⟩

variable (A : LocalFamily (total (interval terminal.{0})))
  (j : A.family ≅ constantFamily (total (interval terminal.{0})) T)
  (e : S ≃ T) (p : StatePackage S) (q : StatePackage T)

/-- Both endpoints are whole six-field native packages, presented on the same
carrier line. The source is expressed in the target coordinates by conjugation. -/
noncomputable abbrev StructuredPath :=
  Term (path (package A).family
    ((pullPackage A j (p.conjugate e)).reindex (endpointSub terminal false))
    ((pullPackage A j q).reindex (endpointSub terminal true)))

theorem pathPreserves (r : StructuredPath A j e p q) : Preserves e p q := by
  apply Preserves.of_eq
  let z₀ := endpointPoint false
  let z₁ := endpointPoint true
  have h₀ := congrArg (fun t => t.val point) (pathApp_zero r)
  have h₁ := congrArg (fun t => t.val point) (pathApp_one r)
  have ho₀ := congrArg (fun t => t.val z₀) (observe_pull A j (p.conjugate e))
  have ho₁ := congrArg (fun t => t.val z₁) (observe_pull A j q)
  calc
    p.conjugate e = (observe A j (pullPackage A j (p.conjugate e))).val z₀ := ho₀.symm
    _ = (observe A j (pathApp r)).val z₀ := congrArg
      (fun v => (readOut A z₀ v).conjugate (j.app z₀).toEquiv) h₀.symm
    _ = (observe A j (pathApp r)).val z₁ := constant_section_interval _ point _ _
    _ = (observe A j (pullPackage A j q)).val z₁ := congrArg
      (fun v => (readOut A z₁ v).conjugate (j.app z₁).toEquiv) h₁
    _ = q := ho₁

noncomputable def preservesPath (h : Preserves e p q) : StructuredPath A j e p q :=
  pathLam (pullPackage A j (p.conjugate e)) rfl
    (congrArg (fun s => (pullPackage A j s).reindex (endpointSub terminal true)) h.package_eq)

/-- Recovery compares actual native path bodies. It does not apply host proof
irrelevance to the Type-valued native path or its dependent proof fields. -/
theorem preservesPath_pathPreserves (r : StructuredPath A j e p q) :
    preservesPath A j e p q (pathPreserves A j e p q r) = r := by
  apply pathApp_injective
  apply section_initial_injective A j
  exact (pathApp_zero _).trans (pathApp_zero r).symm

/-- A fixed-equivalence structure identity correspondence, with exact recovery
of native six-field path sections in the discrete presentation fragment. -/
noncomputable def structureIdentity : StructuredPath A j e p q ≃ Preserves e p q where
  toFun := pathPreserves A j e p q
  invFun := preservesPath A j e p q
  left_inv := preservesPath_pathPreserves A j e p q
  right_inv _ := Subsingleton.elim _ _

end Examples.CubicalStructuredState

namespace Examples.CubicalStructuredState
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open CubicalStatePackageFamily CubicalStatePackageUa CubicalStateTransport
open CubicalUnivalenceTransport CubicalGlue

variable {Γ : Context.{0}}

/-- The existing whole-package ua presentation generalized to the exact supplied
contraction record. Its underlying map is known invertible, but the ua code
retains E rather than replacing it by the isomorphism's canonical contraction. -/
noncomputable def uaPresentation
    (a b : raisedContext Γ ⟶ smallFamilyCodes.{0}) (e : decode a ≅ decode b)
    (E : HomotopyEquivalence e.hom) :
    decode (Univalence.uaCode a b e.hom E) ≅ reindex (decode b) (projection (interval Γ)) := by
  haveI : IsIso (Univalence.boundaryLeft a b e.hom) := by
    exact ((eqToIso (Univalence.boundary_left a b)) ≪≫
      Functor.isoWhiskerLeft (restrictInclusion (intervalFace Γ false) ≫ projection (interval Γ)).mapElements e).isIso_hom
  haveI : IsIso (Univalence.boundaryRight a b) := by
    exact (eqToIso (Univalence.boundary_right a b)).isIso_hom
  haveI : IsIso (Univalence.boundaryMap a b e.hom) := gluedMap_isIso _ _ _
  exact Glue.codeNativeIso Univalence.face (Univalence.ambient b) (CodeSystem.boundary a b)
    (Univalence.boundaryMap a b e.hom) (Univalence.boundaryEquivalence a b e.hom E) ≪≫
    Glue.familyIso _ _ _ _ ≪≫ compatibleUnglueIso _ _ _ (asIso (Univalence.boundaryMap a b e.hom))

theorem uaPresentation_hom
    (a b : raisedContext Γ ⟶ smallFamilyCodes.{0}) (e : decode a ≅ decode b)
    (E : HomotopyEquivalence e.hom) :
    (uaPresentation a b e E).hom = Univalence.unglueLine a b e.hom E :=
  (Glue.codeUnglue_native _ _ _ _ _).symm

variable {S T : Type}

noncomputable def admittedIso
    (f : decode (constantLocal terminal S).code ⟶ decode (constantLocal terminal T).code)
    (E : HomotopyEquivalence f) :
    decode (constantLocal terminal S).code ≅ decode (constantLocal terminal T).code :=
  E.discreteIso
    (PathDiscrete.ofIso (constant_pathDiscrete S) (constantLocal terminal S).decodeCodeIso)
    (decodedLocalFamily (constantLocal terminal S).code).toNative.filling
    (decodedLocalFamily (constantLocal terminal S).code).toNative.lawful
    (PathDiscrete.ofIso (constant_pathDiscrete T) (constantLocal terminal T).decodeCodeIso)

noncomputable def admittedCarrier
    (f : decode (constantLocal terminal S).code ⟶ decode (constantLocal terminal T).code)
    (E : HomotopyEquivalence f) : S ≃ T :=
  (((constantLocal terminal S).decodeCodeIso.symm ≪≫ admittedIso f E ≪≫
    (constantLocal terminal T).decodeCodeIso).app point).toEquiv

noncomputable def admittedLine
    (f : decode (constantLocal terminal S).code ⟶ decode (constantLocal terminal T).code)
    (E : HomotopyEquivalence f) : LocalFamily (total (interval terminal.{0})) :=
  decodedLocalFamily (Univalence.uaCode (constantLocal terminal S).code
    (constantLocal terminal T).code f E)

noncomputable def admittedPresentation
    (f : decode (constantLocal terminal S).code ⟶ decode (constantLocal terminal T).code)
    (E : HomotopyEquivalence f) : (admittedLine f E).family ≅
      constantFamily (total (interval terminal.{0})) T :=
  uaPresentation _ _ (admittedIso f E) E ≪≫
    Functor.isoWhiskerLeft (projection (interval terminal.{0})).mapElements
      (constantLocal terminal T).decodeCodeIso

/-- All genuine native equivalences of the admitted discrete carriers qualify.
The selected equivalence, decoder maps and whole-package filling are retained. -/
noncomputable def uaStructureIdentity
    (f : decode (constantLocal terminal S).code ⟶ decode (constantLocal terminal T).code)
    (E : HomotopyEquivalence f) (p : StatePackage S) (q : StatePackage T) :
    StructuredPath (admittedLine f E) (admittedPresentation f E) (admittedCarrier f E) p q ≃
      Preserves (admittedCarrier f E) p q :=
  structureIdentity (admittedLine f E) (admittedPresentation f E) (admittedCarrier f E) p q

/-- This native contraction justifies the singleton proof-fiber boundary. -/
def proofFiberContractible {Δ : Context.{0}} (r : Term (constantFamily Δ Prop))
    (h : Term (proofFamily r).family) : HomotopyContractible (proofFamily r).family :=
  subsingletonContractible (fun x => show Subsingleton (PLift (r.val x)) from inferInstance) h

end Examples.CubicalStructuredState

namespace Examples.CubicalStructuredState
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open CubicalStatePackageFamily CubicalStatePackageUa CubicalStateTransport
open CubicalUnivalenceTransport CubicalGlue

variable {S T : Type}
variable (f : decode (constantLocal terminal S).code ⟶ decode (constantLocal terminal T).code)
  (E : HomotopyEquivalence f)

noncomputable def admittedStart : reindex (admittedLine f E).family (endpointSub terminal false) ≅
    constantFamily terminal S :=
  eqToIso (congrArg decode (Univalence.uaCode_zero _ _ f E)) ≪≫
    (constantLocal terminal S).decodeCodeIso

noncomputable def admittedFinish : reindex (admittedLine f E).family (endpointSub terminal true) ≅
    constantFamily terminal T :=
  eqToIso (congrArg decode (Univalence.uaCode_one _ _ f E)) ≪≫
    (constantLocal terminal T).decodeCodeIso

noncomputable def carrierPresentation : constantFamily terminal S ≅ constantFamily terminal T :=
  (constantLocal terminal S).decodeCodeIso.symm ≪≫ admittedIso f E ≪≫
    (constantLocal terminal T).decodeCodeIso

set_option backward.isDefEq.respectTransparency false in
theorem admittedPresentation_zero :
    Functor.isoWhiskerLeft (endpointSub terminal false).mapElements (admittedPresentation f E) =
      admittedStart f E ≪≫ carrierPresentation f E := by
  apply Iso.ext
  change Functor.whiskerLeft (endpointSub terminal false).mapElements (uaPresentation _ _ (admittedIso f E) E).hom ≫
    (constantLocal terminal T).decodeCodeIso.hom = _
  rw [uaPresentation_hom, Univalence.unglueLine_zero]
  dsimp only [admittedStart, carrierPresentation, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem admittedPresentation_one :
    Functor.isoWhiskerLeft (endpointSub terminal true).mapElements (admittedPresentation f E) =
      admittedFinish f E := by
  apply Iso.ext
  change Functor.whiskerLeft (endpointSub terminal true).mapElements (uaPresentation _ _ (admittedIso f E) E).hom ≫
    (constantLocal terminal T).decodeCodeIso.hom = _
  rw [uaPresentation_hom, Univalence.unglueLine_one]
  rfl

noncomputable def sourcePackage (p : StatePackage S) : StatePackage S :=
  (readOut (admittedLine f E) (endpointPoint false)
    ((pullPackage (admittedLine f E) (admittedPresentation f E)
      (p.conjugate (admittedCarrier f E))).val (endpointPoint false))).conjugate
    ((admittedStart f E).app point).toEquiv

private theorem source_read {Δ : Context.{0}} (A : LocalFamily Δ)
    (j : A.family ≅ constantFamily Δ T) (x : Δ.Elements)
    (k : A.family.obj x ≅ S) (e : S ≃ T)
    (he : (j.app x).toEquiv = k.toEquiv.trans e) (p : StatePackage S) :
    (readOut A x ((pullPackage A j (p.conjugate e)).val x)).conjugate k.toEquiv = p := by
  rw [readOut_pull, he, conjugate_trans]
  have hc : (k.toEquiv.trans e).symm.trans k.toEquiv = e.symm := by
    ext n
    exact k.toEquiv.apply_symm_apply _
  rw [hc]
  exact conjugate_symm p e

set_option backward.isDefEq.respectTransparency false in
theorem sourcePackage_eq (p : StatePackage S) : sourcePackage f E p = p := by
  apply source_read (admittedLine f E) (admittedPresentation f E) (endpointPoint false)
    ((admittedStart f E).app point) (admittedCarrier f E) _ p
  have he := congrArg (fun e => (e.app point).toEquiv) (admittedPresentation_zero f E)
  simp only [NatIso.trans_app, Iso.toEquiv_comp] at he
  exact he

noncomputable def transported (p : StatePackage S) : Term (package (admittedLine f E)).family :=
  filledPackage (admittedLine f E) (admittedPresentation f E) (p.conjugate (admittedCarrier f E))

noncomputable def targetPackage (p : StatePackage S) : StatePackage T :=
  (readOut (admittedLine f E) (endpointPoint true) ((transported f E p).val (endpointPoint true))).conjugate
    ((admittedFinish f E).app point).toEquiv

theorem targetPackage_eq (p : StatePackage S) : targetPackage f E p = p.conjugate (admittedCarrier f E) := by
  have h := congrArg (fun s => s.val (endpointPoint true))
    (filledPackage_observed (admittedLine f E) (admittedPresentation f E) (p.conjugate (admittedCarrier f E)))
  change (readOut (admittedLine f E) (endpointPoint true) ((transported f E p).val (endpointPoint true))).conjugate
    ((admittedPresentation f E).app (endpointPoint true)).toEquiv = _ at h
  have he := congrArg (fun e => e.app point) (admittedPresentation_one f E)
  change (admittedPresentation f E).app (endpointPoint true) = (admittedFinish f E).app point at he
  rw [he] at h
  exact h

/-- This equality concerns the entire transported native section. -/
theorem transported_recovery (p : StatePackage S) : transported f E p =
    pullPackage (admittedLine f E) (admittedPresentation f E) (p.conjugate (admittedCarrier f E)) :=
  filling_recovery (admittedLine f E) (admittedPresentation f E) _

end Examples.CubicalStructuredState

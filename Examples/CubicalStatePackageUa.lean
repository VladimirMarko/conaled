import Examples.CubicalStatePackageFamily
import Examples.CubicalUnivalenceTransport

/-! Whole-package filling along the actual successor ua carrier line. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalStatePackageUa
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalStatePackageFamily Examples.CubicalStateTransport
open Examples.CubicalGlue Examples.CubicalUnivalenceTransport

variable {Γ : Context.{0}}

set_option backward.isDefEq.respectTransparency false in
def compatibleUnglueIso (φ : Cofibration Γ) (A : Family Γ)
    (T : Family (restrictContext φ)) (e : T ≅ reindex A (restrictInclusion φ)) :
    Glue.compatibleFamily φ A T e.hom ≅ A where
  hom := Glue.compatibleUnglue φ A T e.hom
  inv :=
    { app := fun x => TypeCat.ofHom fun a =>
        { ambient := a
          face := fun {y} f h => e.inv.app (Glue.faceObj φ y h) (A.map f a)
          naturality := by
            intro y z f g h
            exact (e.inv.naturality_apply (Glue.faceHom φ g h) (A.map f a)).symm.trans
              (congrArg (e.inv.app _) ((ConcreteCategory.congr_hom (A.map_comp f g) a).symm))
          compatible := by
            intro y f h
            exact congrArg (fun k => k.app (Glue.faceObj φ y h) (A.map f a)) e.inv_hom_id }
      naturality := by
        intro x y f
        apply ConcreteCategory.hom_ext
        intro a
        apply Glue.CompatibleElement.ext
        · rfl
        · intro z g h
          exact congrArg (e.inv.app _) ((ConcreteCategory.congr_hom (A.map_comp f g) a).symm) }
  hom_inv_id := by
    ext x a
    apply Glue.CompatibleElement.ext
    · rfl
    · intro y f h
      change e.inv.app (Glue.faceObj φ y h) (A.map f a.ambient) = a.face f h
      rw [← a.compatible f h]
      exact congrArg (fun k => k.app (Glue.faceObj φ y h) (a.face f h)) e.hom_inv_id
  inv_hom_id := rfl

set_option backward.isDefEq.respectTransparency false in
theorem gluedMap_isIso {φ ψ : Cofibration Γ}
    {A B : Family (restrictContext (φ.join ψ))}
    (a : reindex A (CodeSystem.includeLeft φ ψ) ⟶ reindex B (CodeSystem.includeLeft φ ψ))
    (b : reindex A (CodeSystem.includeRight φ ψ) ⟶ reindex B (CodeSystem.includeRight φ ψ))
    (c : CodeSystem.Maps.Compatible a b) [IsIso a] [IsIso b] :
    IsIso (CodeSystem.Maps.glue a b c) := by
  have : ∀ x, IsIso ((CodeSystem.Maps.glue a b c).app x) := by
    intro x
    apply (isIso_iff_bijective _).mpr
    by_cases h : φ.full (CodeSystem.Maps.original x)
    · have he : (CodeSystem.Maps.glue a b c).app x = a.app (CodeSystem.Maps.left x h) := by
        apply ConcreteCategory.hom_ext
        intro z
        exact CodeSystem.Maps.value_left a b x h z
      rw [he]
      exact ((asIso a).app (CodeSystem.Maps.left x h)).toEquiv.bijective
    · have k := ((Cofibration.full_join φ ψ _).mp x.val.property).resolve_left h
      have he : (CodeSystem.Maps.glue a b c).app x = b.app (CodeSystem.Maps.right x k) := by
        apply ConcreteCategory.hom_ext
        intro z
        exact CodeSystem.Maps.value_right a b c x k z
      rw [he]
      exact ((asIso b).app (CodeSystem.Maps.right x k)).toEquiv.bijective
  exact NatIso.isIso_of_isIso_app _

noncomputable def uaUnglueIso
    (a b : raisedContext Γ ⟶ smallFamilyCodes.{0}) (e : decode a ≅ decode b) :
    decode (Univalence.uaCode a b e.hom (HomotopyEquivalence.ofIso e)) ≅
      reindex (decode b) (projection (interval Γ)) := by
  haveI : IsIso (Univalence.boundaryLeft a b e.hom) := by
    exact ((eqToIso (Univalence.boundary_left a b)) ≪≫
      Functor.isoWhiskerLeft (restrictInclusion (intervalFace Γ false) ≫ projection (interval Γ)).mapElements e).isIso_hom
  haveI : IsIso (Univalence.boundaryRight a b) := by
    exact (eqToIso (Univalence.boundary_right a b)).isIso_hom
  haveI : IsIso (Univalence.boundaryMap a b e.hom) :=
    gluedMap_isIso _ _ _
  exact Glue.codeNativeIso Univalence.face (Univalence.ambient b) (CodeSystem.boundary a b)
      (Univalence.boundaryMap a b e.hom) (Univalence.boundaryEquivalence a b e.hom (HomotopyEquivalence.ofIso e)) ≪≫
    Glue.familyIso _ _ _ _ ≪≫ compatibleUnglueIso _ _ _ (asIso (Univalence.boundaryMap a b e.hom))

theorem uaUnglueIso_hom
    (a b : raisedContext Γ ⟶ smallFamilyCodes.{0}) (e : decode a ≅ decode b) :
    (uaUnglueIso a b e).hom = Univalence.unglueLine a b e.hom (HomotopyEquivalence.ofIso e) :=
  (Glue.codeUnglue_native _ _ _ _ _).symm

noncomputable def successorLine : LocalFamily (total (interval terminal.{0})) :=
  decodedLocalFamily (Univalence.uaCode (constantLocal terminal Int).code
    (constantLocal terminal Int).code (codeIso successor).hom (HomotopyEquivalence.ofIso (codeIso successor)))

noncomputable def successorLineIso : successorLine.family ≅
    constantFamily (total (interval terminal.{0})) Int :=
  uaUnglueIso _ _ (codeIso successor) ≪≫
    Functor.isoWhiskerLeft (projection (interval terminal.{0})).mapElements
      (constantLocal terminal Int).decodeCodeIso

noncomputable def startIso : reindex successorLine.family (endpointSub terminal false) ≅
    constantFamily terminal Int :=
  eqToIso (congrArg decode (Univalence.uaCode_zero _ _ (codeIso successor).hom
    (HomotopyEquivalence.ofIso (codeIso successor)))) ≪≫ (constantLocal terminal Int).decodeCodeIso

noncomputable def finishIso : reindex successorLine.family (endpointSub terminal true) ≅
    constantFamily terminal Int :=
  eqToIso (congrArg decode (Univalence.uaCode_one _ _ (codeIso successor).hom
    (HomotopyEquivalence.ofIso (codeIso successor)))) ≪≫ (constantLocal terminal Int).decodeCodeIso

set_option backward.isDefEq.respectTransparency false in
theorem successorLineIso_zero :
    Functor.isoWhiskerLeft (endpointSub terminal false).mapElements successorLineIso =
      startIso ≪≫ constantIso successor := by
  apply Iso.ext
  change Functor.whiskerLeft (endpointSub terminal false).mapElements (uaUnglueIso _ _ (codeIso successor)).hom ≫
    (constantLocal terminal Int).decodeCodeIso.hom = _
  rw [uaUnglueIso_hom, Univalence.unglueLine_zero]
  dsimp only [startIso, codeIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem successorLineIso_one :
    Functor.isoWhiskerLeft (endpointSub terminal true).mapElements successorLineIso = finishIso := by
  apply Iso.ext
  change Functor.whiskerLeft (endpointSub terminal true).mapElements (uaUnglueIso _ _ (codeIso successor)).hom ≫
    (constantLocal terminal Int).decodeCodeIso.hom = _
  rw [uaUnglueIso_hom, Univalence.unglueLine_one]
  rfl

noncomputable def suppliedPackage : Term (package successorLine).family :=
  pullPackage successorLine successorLineIso oddPackage

noncomputable def transportedPackage : Term (package successorLine).family :=
  filledPackage successorLine successorLineIso oddPackage

def point : terminal.{0}.Elements := terminal.elementsMk (Opposite.op ⟨0⟩) PUnit.unit

def endpointPoint (ε : Bool) : (total (interval terminal.{0})).Elements :=
  (endpointSub terminal ε).mapElements.obj point

noncomputable def initialPackage : StatePackage Int :=
  (readOut successorLine (endpointPoint false) (suppliedPackage.val (endpointPoint false))).conjugate
    (startIso.app point).toEquiv

noncomputable def finalPackage : StatePackage Int :=
  (readOut successorLine (endpointPoint true) (transportedPackage.val (endpointPoint true))).conjugate
    (finishIso.app point).toEquiv

/-- The chosen filler transports the entire package, including invariant proofs. -/
theorem finalPackage_eq : finalPackage = oddPackage := by
  have h := congrArg (fun s => s.val (endpointPoint true))
    (filledPackage_observed successorLine successorLineIso oddPackage)
  change (readOut successorLine (endpointPoint true) (transportedPackage.val (endpointPoint true))).conjugate
    (successorLineIso.app (endpointPoint true)).toEquiv = oddPackage at h
  have he := congrArg (fun e => e.app point) successorLineIso_one
  change successorLineIso.app (endpointPoint true) = finishIso.app point at he
  rw [he] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The initial restriction is the whole original even-state package. -/
theorem initialPackage_eq : initialPackage = evenPackage := by
  have he := congrArg (fun e => (e.app point).toEquiv) successorLineIso_zero
  change (successorLineIso.app (endpointPoint false)).toEquiv =
    (startIso.app point).toEquiv.trans successor at he
  unfold initialPackage suppliedPackage
  rw [readOut_pull, he, conjugate_trans]
  have hcomp : ((startIso.app point).toEquiv.trans successor).symm.trans (startIso.app point).toEquiv =
      successor.symm := by
    ext n
    exact (startIso.app point).toEquiv.apply_symm_apply _
  rw [hcomp]
  exact conjugate_symm evenPackage successor

theorem transportedPackage_zero :
    transportedPackage.reindex (endpointSub terminal false) =
      suppliedPackage.reindex (endpointSub terminal false) :=
  IntervalTransport.forward_zero (package successorLine).toNative.filling
    (package successorLine).toNative.lawful (𝟙 terminal) _

theorem final_initial : finalPackage.initial = 1 := by
  rw [finalPackage_eq]
  exact odd_initial

theorem final_step (n : Int) : finalPackage.step n = n + 2 := by
  rw [finalPackage_eq]
  exact odd_step n

theorem final_invariant (n : Int) : finalPackage.invariant n ↔ n % 2 = 1 := by
  rw [finalPackage_eq]
  exact odd_invariant n

end Examples.CubicalStatePackageUa

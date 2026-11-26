import SquareKit.Internal.Cubical.SelectedInverseSubstitution
import Examples.CubicalGlueEquivalence

/-! Recover actual Boolean Glue face data through the selected native inverse. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalSelectedInverse
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open CubicalGlueEquivalence

variable {Γ : Context.{0}} (φ : Cofibration Γ)

abbrev glued := Glue.family φ (constantFamily Γ Bool)
  (reindex (constantFamily Γ Bool) (restrictInclusion φ)) (faceFlip φ).hom

abbrev forget := Glue.unglue φ (constantFamily Γ Bool)
  (reindex (constantFamily Γ Bool) (restrictInclusion φ)) (faceFlip φ).hom

/-- The map comes from the actual unglue fiber centers, not an independently
chosen inverse of the Boolean presentation. -/
noncomputable def recover : constantFamily Γ Bool ⟶ glued φ :=
  (equivalence φ).selectedInverse

noncomputable def recoverRight := (equivalence φ).selectedRight
noncomputable def recoverLeft := (equivalence φ).selectedLeft

noncomputable def recoverEquivalence : HomotopyEquivalence (recover φ) :=
  (equivalence φ).selectedInverseEquivalence
    (Glue.filling φ _ _ _ (HomotopyEquivalence.ofIso (faceFlip φ))
      (boolFilling.reindex (restrictInclusion φ)) (boolFilling_lawful.reindex _)
      boolFilling boolFilling_lawful)
    (Glue.filling_lawful φ _ _ _ (HomotopyEquivalence.ofIso (faceFlip φ))
      (boolFilling.reindex (restrictInclusion φ)) (boolFilling_lawful.reindex _)
      boolFilling boolFilling_lawful)
    boolFilling boolFilling_lawful

/-- Substitution recomputes the complete inverse-fiber witness from the
reindexed unglue witness and chosen Glue filler. -/
theorem recoverEquivalence_reindex {Δ : Context.{0}} (σ : Δ ⟶ Γ) :
    let F := Glue.filling φ _ _ _ (HomotopyEquivalence.ofIso (faceFlip φ))
      (boolFilling.reindex (restrictInclusion φ)) (boolFilling_lawful.reindex _)
      boolFilling boolFilling_lawful
    let hF := Glue.filling_lawful φ _ _ _ (HomotopyEquivalence.ofIso (faceFlip φ))
      (boolFilling.reindex (restrictInclusion φ)) (boolFilling_lawful.reindex _)
      boolFilling boolFilling_lawful
    HEq ((recoverEquivalence φ).reindex σ)
      (((equivalence φ).reindex σ).selectedInverseEquivalence (F.reindex σ) (hF.reindex _)
        (boolFilling.reindex σ) (boolFilling_lawful.reindex _)) := by
  exact (equivalence φ).selectedInverseEquivalence_reindex _ _
    boolFilling boolFilling_lawful σ

/-- Discreteness turns the retained right recovery path into ambient equality. -/
theorem recovered_ambient (x : Γ.Elements) (b : Bool) :
    (forget φ).app x ((recover φ).app x b) = b := by
  have h := constantFamily_path_endpoints (recoverRight φ)
  exact congrArg (fun t => t.val ((total (constantFamily Γ Bool)).elementsMk x.obj ⟨x.val,b⟩)) h

/-- Every face observation is the opposite Boolean, including faces exposed
only after restricting the generalized point. -/
theorem recovered_face (x y : Γ.Elements) (k : x ⟶ y) (hy : φ.Full y) (b : Bool) :
    ((Glue.familyIso φ _ _ (faceFlip φ).hom).hom.app x ((recover φ).app x b)).face k hy = !b := by
  let z := (Glue.familyIso φ _ _ (faceFlip φ).hom).hom.app x ((recover φ).app x b)
  have h := z.compatible k hy
  have ha := recovered_ambient φ x b
  change Bool.not (z.face k hy) = z.ambient at h
  change z.ambient = b at ha
  change z.face k hy = Bool.not b
  have hn := h.trans ha
  cases hz : z.face k hy <;> cases b <;> simp_all <;> rfl

/-- Actual face data is recovered, not merely its ambient image. -/
theorem recovered_true_face (x y : Γ.Elements) (k : x ⟶ y) (hy : φ.Full y) :
    ((Glue.familyIso φ _ _ (faceFlip φ).hom).hom.app x ((recover φ).app x true)).face k hy = false :=
  recovered_face φ x y k hy true

/-- The ambient and all face readouts jointly recover the entire glued element. -/
theorem recovered_whole (x : Γ.Elements) (s : (glued φ).obj x) :
    (recover φ).app x ((forget φ).app x s) = s := by
  apply ((Glue.familyIso φ _ _ (faceFlip φ).hom).app x).toEquiv.injective
  apply Glue.CompatibleElement.ext
  · exact recovered_ambient φ x ((forget φ).app x s)
  · intro y k hy
    apply (recovered_face φ x y k hy ((forget φ).app x s)).trans
    let z := (Glue.familyIso φ _ _ (faceFlip φ).hom).hom.app x s
    have h := z.compatible k hy
    change Bool.not (z.face k hy) = z.ambient at h
    change Bool.not z.ambient = z.face k hy
    cases hz : z.face k hy <;> cases ha : z.ambient <;> simp_all

/-- On an ordinary isomorphism the selected map is its supplied inverse. -/
theorem selected_ofIso {A B : Family Γ} (e : A ≅ B) :
    (HomotopyEquivalence.ofIso e).selectedInverse = e.inv := rfl

def zeroPoint : (total (interval terminal.{0})).Elements :=
  (total (interval terminal)).elementsMk (Opposite.op ⟨0⟩)
    ⟨PUnit.unit, (endpoint terminal false).val (terminal.elementsMk (Opposite.op ⟨0⟩) PUnit.unit)⟩

def onePoint : (total (interval terminal.{0})).Elements :=
  (total (interval terminal)).elementsMk (Opposite.op ⟨0⟩)
    ⟨PUnit.unit, (endpoint terminal true).val (terminal.elementsMk (Opposite.op ⟨0⟩) PUnit.unit)⟩

theorem zero_on_face : (intervalFace terminal false).Full zeroPoint :=
  (Cofibration.full_endpoint _ _ _).mpr rfl

theorem one_off_face : ¬ (intervalFace terminal false).Full onePoint := by
  intro h
  exact intervalFace_disjoint onePoint h ((Cofibration.full_endpoint _ _ _).mpr rfl)

/-- The face is inhabited and proper; its true ambient point recovers false
face data through the general native inverse construction. -/
theorem proper_face_recovers_false :
    ((Glue.familyIso (intervalFace terminal false) _ _
      (faceFlip (intervalFace terminal false)).hom).hom.app zeroPoint
      ((recover (intervalFace terminal false)).app zeroPoint true)).face
        (𝟙 zeroPoint) zero_on_face = false :=
  recovered_true_face (intervalFace terminal false) zeroPoint zeroPoint (𝟙 _) zero_on_face

end Examples.CubicalSelectedInverse

namespace Examples.CubicalSelectedInverse
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf

/-- Native contractibility need not make the carrier a singleton set. -/
def intervalContractible (Γ : Context.{0}) : HomotopyContractible (interval Γ) where
  center := endpoint Γ false
  contraction := pathLam ((generic (interval Γ)).reindex (scaleInterval Γ))
    (by
      apply Term.ext
      intro x
      exact congrArg ULift.up (Cube.meet_zero x.val.2.down))
    (by
      apply Term.ext
      intro x
      exact congrArg ULift.up (Cube.meet_one x.val.2.down))

def discard {Γ : Context.{0}} (A : Family Γ) : A ⟶ constantFamily Γ Unit where
  app _ := TypeCat.ofHom (fun _ => ())
  naturality _ _ _ := rfl

/-- The Unit path component carries no additional data, so a discard fiber
recovers its entire source element. -/
def discardFiberIso {Γ : Context.{0}} (A : Family Γ) :
    homotopyFiber (Functor.whiskerLeft (projection (constantFamily Γ Unit)).mapElements
      (discard A)) (generic (constantFamily Γ Unit)) ≅
      reindex A (projection (constantFamily Γ Unit)) where
  hom := { app := fun _ => TypeCat.ofHom Sigma.fst, naturality := fun _ _ _ => rfl }
  inv := {
    app := fun _ => TypeCat.ofHom (fun a => ⟨a,⟨{
      val := fun {_} _ _ => ()
      naturality := fun _ _ _ => rfl }, fun {_} _ => ⟨rfl, Unit.ext _ _⟩⟩⟩)
    naturality := fun _ _ _ => rfl }
  hom_inv_id := by
    ext x a
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Subtype.ext
    apply PiElement.ext
    intro y f i
    exact Unit.ext _ _
  inv_hom_id := rfl

def discardEquivalence {Γ : Context.{0}} {A : Family Γ}
    (c : HomotopyContractible A) : HomotopyEquivalence (discard A) where
  fibers := (c.reindex (projection (constantFamily Γ Unit))).transport (discardFiberIso A).symm

/-- This genuine native equivalence is not a presheaf isomorphism. No filling
of the representable interval is asserted by this rejection case. -/
theorem interval_discard_not_iso : ¬ IsIso (discard (interval terminal.{0})) := by
  intro h
  let e := asIso (discard (interval terminal.{0}))
  let x : terminal.{0}.Elements := terminal.elementsMk (Opposite.op ⟨0⟩) PUnit.unit
  have he : (endpoint terminal false).val x = (endpoint terminal true).val x :=
    (e.app x).toEquiv.injective (Unit.ext _ _)
  have hz := congrArg ULift.down he
  have bad := PartialDimension.sound (fun _ => none) (Quotient.exact hz 0)
  cases bad

def intervalDiscardEquivalence := discardEquivalence (intervalContractible terminal)

/-- Requiring an isomorphism in order to select a native inverse would reject
this supplied genuine contractible-fiber witness. -/
def intervalSelectedInverse := intervalDiscardEquivalence.selectedInverse
def intervalSelectedLeft := intervalDiscardEquivalence.selectedLeft
def intervalSelectedRight := intervalDiscardEquivalence.selectedRight

end Examples.CubicalSelectedInverse

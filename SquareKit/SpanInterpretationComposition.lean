import SquareKit.SpanInterpretation
import SquareKit.Internal.PseudofunctorCoherence

/-! Identity and composition in the interpretation variable, retaining the chosen
apex comparisons and the complete slice-action transformations. -/
noncomputable section
namespace SquareKit.SpanInterpretation
open CategoryTheory Limits SpanAction Span.SpanBicat Bicategory
open scoped Pseudofunctor.StrongTrans
universe u v
variable {C D E K : Type u} [Category.{v} C] [Category.{v} D]
  [Category.{v} E] [Category.{v} K]
variable [HasPullbacks C] [HasPullbacks D] [HasPullbacks E] [HasPullbacks K]
variable (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ K)
variable [PreservesLimitsOfShape WalkingCospan F] [PreservesLimitsOfShape WalkingCospan G]
  [PreservesLimitsOfShape WalkingCospan H]

/-- The actual canonical apex comparison gives equality of the complete induced data. -/
theorem pseudofunctor_comp :
    pseudofunctor (F ⋙ G) = (pseudofunctor F).comp (pseudofunctor G) := by
  refine PseudofunctorCoherence.ext (F := pseudofunctor (F ⋙ G))
    (G := (pseudofunctor F).comp (pseudofunctor G)) rfl ?_ ?_
  · apply heq_of_eq
    funext X
    apply Iso.ext
    apply Span.hom_ext
    change 𝟙 _ = G.map (𝟙 _) ≫ 𝟙 _
    simp
  · apply heq_of_eq
    funext X Y Z S T
    apply Iso.ext
    apply Span.hom_ext
    exact apex_composition F G S T

/-- The identity interpretation includes the identity chosen pullback comparison. -/
theorem pseudofunctor_id : pseudofunctor (𝟭 C) = Pseudofunctor.id (Bases C) := by
  refine PseudofunctorCoherence.ext (F := pseudofunctor (𝟭 C))
    (G := Pseudofunctor.id (Bases C)) rfl ?_ ?_
  · apply heq_of_eq
    funext X
    apply Iso.ext
    apply Span.hom_ext
    rfl
  · apply heq_of_eq
    funext X Y Z S T
    apply Iso.ext
    apply Span.hom_ext
    change pullbackComparison (𝟭 C) S.r T.l = 𝟙 _
    exact MixedBaseChange.identity T.l (Over.mk S.r)

/-- Comparison between the two interpretation pseudofunctors, with identity components. -/
def compositionComparison : pseudofunctor (F ⋙ G) ⟶
    (pseudofunctor F).comp (pseudofunctor G) :=
  PseudofunctorCoherence.retarget (Pseudofunctor.StrongTrans.id _)
    (pseudofunctor_comp F G) rfl

/-- Identity comparison as an actual strong transformation. -/
def identityComparison : pseudofunctor (𝟭 C) ⟶ Pseudofunctor.id (Bases C) :=
  PseudofunctorCoherence.retarget (Pseudofunctor.StrongTrans.id _) pseudofunctor_id rfl

/-- Reassociation and the actual composition comparison align the slice-action targets. -/
theorem action_target_comp :
    (pseudofunctor F).comp ((pseudofunctor G).comp (SpanAction.pseudofunctor (C := E))) =
      (pseudofunctor (F ⋙ G)).comp (SpanAction.pseudofunctor (C := E)) := by
  rw [← PseudofunctorCoherence.comp_assoc, ← pseudofunctor_comp]

/-- Compose supplied slice-action transformations by the existing bicategorical operations. -/
def composeTransformations
    (η : SpanAction.pseudofunctor (C := C) ⟶
      (pseudofunctor F).comp (SpanAction.pseudofunctor (C := D)))
    (θ : SpanAction.pseudofunctor (C := D) ⟶
      (pseudofunctor G).comp (SpanAction.pseudofunctor (C := E))) :
    SpanAction.pseudofunctor (C := C) ⟶
      (pseudofunctor (F ⋙ G)).comp (SpanAction.pseudofunctor (C := E)) :=
  PseudofunctorCoherence.retarget
    (η ≫ PseudofunctorCoherence.precomp (pseudofunctor F) θ) (action_target_comp F G) rfl

/-- The successive transformation is built by actual precomposition and vertical composition. -/
def successiveTransformation : SpanAction.pseudofunctor (C := C) ⟶
    (pseudofunctor (F ⋙ G)).comp (SpanAction.pseudofunctor (C := E)) :=
  composeTransformations F G (transformation F) (transformation G)

/-- The complete postcomposition functors are retained after target normalization. -/
theorem successiveTransformation_app (X : Bases C) :
    (successiveTransformation F G).app X =
      ((Over.post (X := X.of) F) ⋙ Over.post G).toCatHom :=
  by rfl

set_option backward.isDefEq.respectTransparency false in
/-- Lift the whole successive comparison equation to an invertible modification. -/
def compositionModification : PseudofunctorCoherence.ModificationIso
    (transformation (F ⋙ G)) (successiveTransformation F G) :=
  Pseudofunctor.StrongTrans.isoMk
    (fun X => Cat.Hom.isoMk (Over.postComp (X := X.of) F G)) (by
      intro X Y S
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext V
      change Over X.of at V
      apply Over.OverMorphism.ext
      change 𝟙 _ ≫ (𝟙 _ ≫ G.map ((actionIso F S).hom.app V).left ≫
        𝟙 _ ≫ ((actionIso G (span F S)).hom.app ((Over.post F).obj V)).left ≫ 𝟙 _) =
        ((actionIso (F ⋙ G) S).hom.app V).left ≫
          ((action (span (F ⋙ G) S)).map (𝟙 ((Over.post (F ⋙ G)).obj V))).left
      simp only [Category.id_comp, Category.comp_id]
      have hi : ((action (span (F ⋙ G) S)).map (𝟙 ((Over.post (F ⋙ G)).obj V))).left = 𝟙 _ :=
        congrArg CommaMorphism.left ((action (span (F ⋙ G) S)).map_id _)
      rw [hi]
      exact (action_composition F G S V).symm.trans (Category.comp_id _).symm)

/-- Reading the modification naturality square recovers the complete native equation. -/
theorem compositionModification_naturality {X Y : Bases C} (S : X ⟶ Y) (V : Over X.of) :
    ((actionIso (F ⋙ G) S).hom.app V).left =
      G.map ((actionIso F S).hom.app V).left ≫
        ((actionIso G (span F S)).hom.app ((Over.post F).obj V)).left := by
  have h := congrArg (fun η => (η.toNatTrans.app V).left)
    ((compositionModification F G).hom.as.naturality S)
  change 𝟙 _ ≫ (𝟙 _ ≫ G.map ((actionIso F S).hom.app V).left ≫
    𝟙 _ ≫ ((actionIso G (span F S)).hom.app ((Over.post F).obj V)).left ≫ 𝟙 _) =
    ((actionIso (F ⋙ G) S).hom.app V).left ≫
      ((action (span (F ⋙ G) S)).map (𝟙 ((Over.post (F ⋙ G)).obj V))).left at h
  simp only [Category.id_comp, Category.comp_id] at h
  have hi : ((action (span (F ⋙ G) S)).map (𝟙 ((Over.post (F ⋙ G)).obj V))).left = 𝟙 _ :=
    congrArg CommaMorphism.left ((action (span (F ⋙ G) S)).map_id _)
  rw [hi] at h
  exact (Category.comp_id _).symm.trans h.symm

/-- The identity interpretation has the original action as its normalized target. -/
theorem action_target_id :
    (pseudofunctor (𝟭 C)).comp (SpanAction.pseudofunctor (C := C)) =
      SpanAction.pseudofunctor (C := C) := by
  rw [pseudofunctor_id, PseudofunctorCoherence.id_comp]

/-- The identity transformation placed at the identity interpretation's target. -/
def identityAlong : SpanAction.pseudofunctor (C := C) ⟶
    (pseudofunctor (𝟭 C)).comp (SpanAction.pseudofunctor (C := C)) :=
  PseudofunctorCoherence.retarget (Pseudofunctor.StrongTrans.id _)
    action_target_id.symm rfl

/-- Identity postcomposition retains every slice object and arrow. -/
def postIdentityIso (X : C) : Over.post (X := X) (𝟭 C) ≅ 𝟭 (Over X) :=
  NatIso.ofComponents (fun V => Over.isoMk (Iso.refl V.left)) (by
    intro V W k
    apply Over.OverMorphism.ext
    change k.left ≫ 𝟙 _ = 𝟙 _ ≫ k.left
    simp)

set_option backward.isDefEq.respectTransparency false in
/-- The native identity equation gives an invertible modification to the identity action. -/
def identityModification : PseudofunctorCoherence.ModificationIso
    (transformation (𝟭 C)) (identityAlong (C := C)) :=
  Pseudofunctor.StrongTrans.isoMk (fun X => Cat.Hom.isoMk (postIdentityIso X.of)) (by
    intro X Y S
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext V
    change Over X.of at V
    apply Over.OverMorphism.ext
    change 𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _) = ((actionIso (𝟭 C) S).hom.app V).left ≫
      ((action S).map (𝟙 V)).left
    have hi : ((action S).map (𝟙 V)).left = 𝟙 _ :=
      congrArg CommaMorphism.left ((action S).map_id V)
    rw [hi, action_identity]
    simp)

/-- Whisker and compose existing invertible modifications, then normalize the target. -/
def composeModifications
    {η η' : SpanAction.pseudofunctor (C := C) ⟶
      (pseudofunctor F).comp (SpanAction.pseudofunctor (C := D))}
    {θ θ' : SpanAction.pseudofunctor (C := D) ⟶
      (pseudofunctor G).comp (SpanAction.pseudofunctor (C := E))}
    (i : PseudofunctorCoherence.ModificationIso η η')
    (j : PseudofunctorCoherence.ModificationIso θ θ') :
    PseudofunctorCoherence.ModificationIso (composeTransformations F G η θ)
      (composeTransformations F G η' θ') :=
  PseudofunctorCoherence.retargetIso (action_target_comp F G) rfl
    (whiskerRightIso i (PseudofunctorCoherence.precomp (pseudofunctor F) θ) ≪≫
      whiskerLeftIso η' (PseudofunctorCoherence.precompIso (pseudofunctor F) j))

/-- The left parenthesization of three actual interpretation transformations. -/
def tripleLeft := composeTransformations (F ⋙ G) H
  (successiveTransformation F G) (transformation H)

/-- The right parenthesization has the same target, by ordinary functor associativity. -/
def tripleRight := composeTransformations F (G ⋙ H)
  (transformation F) (successiveTransformation G H)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical functor associator, independently of the composition modifications. -/
def compositionAssociator : PseudofunctorCoherence.ModificationIso
    (tripleLeft F G H) (tripleRight F G H) :=
  Pseudofunctor.StrongTrans.isoMk (fun X => Cat.Hom.isoMk
    (Functor.associator (Over.post (X := X.of) F) (Over.post G) (Over.post H))) (by
      intro X Y S
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext V
      change Over X.of at V
      apply Over.OverMorphism.ext
      let f := ((actionIso F S).hom.app V).left
      let g := ((actionIso G (span F S)).hom.app ((Over.post F).obj V)).left
      let h := ((actionIso H (span G (span F S))).hom.app
        ((Over.post G).obj ((Over.post F).obj V))).left
      change 𝟙 _ ≫ (𝟙 _ ≫ H.map (G.map f) ≫ 𝟙 _ ≫
          (𝟙 _ ≫ H.map g ≫ 𝟙 _ ≫ h ≫ 𝟙 _) ≫ 𝟙 _) =
        (𝟙 _ ≫ H.map (𝟙 _ ≫ G.map f ≫ 𝟙 _ ≫ g ≫ 𝟙 _) ≫ 𝟙 _ ≫ h ≫ 𝟙 _) ≫
          ((action (span (F ⋙ G ⋙ H) S)).map (𝟙 ((Over.post (F ⋙ G ⋙ H)).obj V))).left
      simp only [Category.id_comp, Category.comp_id]
      have hi : ((action (span (F ⋙ G ⋙ H) S)).map
          (𝟙 ((Over.post (F ⋙ G ⋙ H)).obj V))).left = 𝟙 _ :=
        congrArg CommaMorphism.left ((action (span (F ⋙ G ⋙ H) S)).map_id _)
      rw [hi]
      have hm : H.map (G.map f ≫ g) ≫ h = H.map (G.map f) ≫ H.map g ≫ h :=
        (congrArg (fun k => k ≫ h) (H.map_comp (G.map f) g)).trans (Category.assoc _ _ _)
      exact hm.symm.trans (Category.comp_id _).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary functor left unitor, with the identity interpretation target aligned. -/
def compositionLeftUnitor : PseudofunctorCoherence.ModificationIso
    (composeTransformations (𝟭 C) F identityAlong (transformation F)) (transformation F) :=
  Pseudofunctor.StrongTrans.isoMk
    (fun X => Cat.Hom.isoMk (Functor.leftUnitor (Over.post (X := X.of) F))) (by
      intro X Y S
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext V
      change Over X.of at V
      apply Over.OverMorphism.ext
      let f := ((actionIso F S).hom.app V).left
      change 𝟙 _ ≫ f = (𝟙 _ ≫ F.map (𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _ ≫ f ≫ 𝟙 _) ≫
        ((action (span F S)).map (𝟙 ((Over.post F).obj V))).left
      simp only [Category.id_comp, Category.comp_id, F.map_id]
      have hi : ((action (span F S)).map (𝟙 ((Over.post F).obj V))).left = 𝟙 _ :=
        congrArg CommaMorphism.left ((action (span F S)).map_id _)
      rw [hi]
      exact (Category.comp_id _).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary functor right unitor, with the identity interpretation target aligned. -/
def compositionRightUnitor : PseudofunctorCoherence.ModificationIso
    (composeTransformations F (𝟭 D) (transformation F) identityAlong) (transformation F) :=
  Pseudofunctor.StrongTrans.isoMk
    (fun X => Cat.Hom.isoMk (Functor.rightUnitor (Over.post (X := X.of) F))) (by
      intro X Y S
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext V
      change Over X.of at V
      apply Over.OverMorphism.ext
      let f := ((actionIso F S).hom.app V).left
      change 𝟙 _ ≫ f = (𝟙 _ ≫ f ≫ 𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _) ≫
        ((action (span F S)).map (𝟙 ((Over.post F).obj V))).left
      simp only [Category.id_comp, Category.comp_id]
      have hi : ((action (span F S)).map (𝟙 ((Over.post F).obj V))).left = 𝟙 _ :=
        congrArg CommaMorphism.left ((action (span F S)).map_id _)
      rw [hi]
      exact (Category.comp_id _).symm)

/-- First compare F and G, then H, and use the independently constructed associator. -/
def tripleComparisonLeft : PseudofunctorCoherence.ModificationIso
    (transformation (F ⋙ G ⋙ H)) (tripleRight F G H) :=
  compositionModification (F ⋙ G) H ≪≫
    composeModifications (F ⋙ G) H (compositionModification F G) (PseudofunctorCoherence.modificationRefl (transformation H)) ≪≫
    compositionAssociator F G H

/-- First compare G and H, then F. -/
def tripleComparisonRight : PseudofunctorCoherence.ModificationIso
    (transformation (F ⋙ G ⋙ H)) (tripleRight F G H) :=
  compositionModification F (G ⋙ H) ≪≫
    composeModifications F (G ⋙ H) (PseudofunctorCoherence.modificationRefl (transformation F)) (compositionModification G H)

set_option backward.isDefEq.respectTransparency false in
/-- The complete invertible modifications commute under three interpretations. -/
theorem composition_associativity : tripleComparisonLeft F G H = tripleComparisonRight F G H := by
  apply Iso.ext
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro X
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext V
  change Over X.of at V
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ (H.map (𝟙 _) ≫ 𝟙 _) ≫ 𝟙 _ =
    𝟙 _ ≫ (H.map (G.map (𝟙 _)) ≫ 𝟙 _)
  simp only [G.map_id, H.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The left identity diagram compares the native identity modification and functor unitor. -/
theorem composition_left_unit :
    compositionModification (𝟭 C) F ≪≫
      composeModifications (𝟭 C) F identityModification (PseudofunctorCoherence.modificationRefl (transformation F)) ≪≫
      compositionLeftUnitor F = PseudofunctorCoherence.modificationRefl (transformation F) := by
  apply Iso.ext
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro X
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext V
  change Over X.of at V
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ (F.map (𝟙 _) ≫ 𝟙 _) ≫ 𝟙 _ = 𝟙 _
  simp only [F.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The right identity diagram retains the entire postcomposition component. -/
theorem composition_right_unit :
    compositionModification F (𝟭 D) ≪≫
      composeModifications F (𝟭 D) (PseudofunctorCoherence.modificationRefl (transformation F)) identityModification ≪≫
      compositionRightUnitor F = PseudofunctorCoherence.modificationRefl (transformation F) := by
  apply Iso.ext
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro X
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext V
  change Over X.of at V
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _ = 𝟙 _
  simp only [Category.id_comp]

/-- The induced span target agrees after either grouping, including all chosen compositors. -/
theorem pseudofunctor_triple :
    ((pseudofunctor F).comp (pseudofunctor G)).comp (pseudofunctor H) =
      (pseudofunctor F).comp ((pseudofunctor G).comp (pseudofunctor H)) :=
  PseudofunctorCoherence.comp_assoc _ _ _

end SquareKit.SpanInterpretation

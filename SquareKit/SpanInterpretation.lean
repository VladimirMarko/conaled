import SquareKit.SpanAction
import SquareKit.MixedBaseChange
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-! Pullback-preserving interpretations act coherently on spans and their slice actions.
The comparisons retain both the original value and the selected apex witness. -/
noncomputable section
namespace SquareKit.SpanInterpretation
open CategoryTheory Limits SpanAction Span.SpanBicat
open scoped CategoryTheory.Bicategory
universe u v
variable {C : Type u} {D : Type u} [Category.{v} C] [Category.{v} D]
variable [HasPullbacks C] [HasPullbacks D]
variable (F : C ⥤ D)

/-- Apply the interpretation to both legs and the complete apex. -/
abbrev span {X Y : C} (S : Spans X Y) : (⟨F.obj X⟩ : Bases D) ⟶ (⟨F.obj Y⟩ : Bases D) where
  apex := F.obj S.apex
  l := F.map S.l
  r := F.map S.r
  wl := trivial
  wr := trivial

/-- Arbitrary apex maps, without an invertibility hypothesis. -/
def map {X Y : C} {S T : Spans X Y} (k : S ⟶ T) : span F S ⟶ span F T where
  hom := F.map k.hom
  hom_l := by simp [span, ← F.map_comp]
  hom_r := by simp [span, ← F.map_comp]

variable [PreservesLimitsOfShape WalkingCospan F]
/-- The chosen pullback comparison supplies the compositor apex. -/
def compositionIso {X Y Z : C} (S : Spans X Y) (T : Spans Y Z) :
    span F (Span.comp S T) ≅ Span.comp (span F S) (span F T) :=
  Span.mkIso (PreservesPullback.iso F S.r T.l)
    (by
      change (PreservesPullback.iso F S.r T.l).hom ≫ _ ≫ _ = _
      rw [← Category.assoc, PreservesPullback.iso_hom_fst, ← F.map_comp]
      rfl)
    (by
      change (PreservesPullback.iso F S.r T.l).hom ≫ _ ≫ _ = _
      rw [← Category.assoc, PreservesPullback.iso_hom_snd, ← F.map_comp]
      rfl)

def unitIso (X : C) : span F (Span.id X) ≅ Span.id (F.obj X) :=
  Span.mkIso (Iso.refl _) (by simp [span]) (by simp [span])

set_option backward.isDefEq.respectTransparency false in
/-- Coherence proved in the forward direction before introducing inverses. -/
def oplax : Bases C ⥤ᵒᵖᴸ Bases D where
  obj X := ⟨F.obj X.of⟩
  map S := span F S
  map₂ k := map F k
  map₂_id S := by apply Span.hom_ext; exact F.map_id _
  map₂_comp k h := by apply Span.hom_ext; exact F.map_comp _ _
  mapId X := (unitIso F X.of).hom
  mapComp S T := (compositionIso F S T).hom
  mapComp_naturality_right S T U k := by
    apply Span.hom_ext
    simp only [hom₂_comp_hom]
    apply pullback.hom_ext
    · simp only [Category.assoc]
      erw [source_whiskerLeft_fst (span F S) (map F k)]
      dsimp [map, compositionIso]
      rw [pullbackComparison_comp_fst, ← F.map_comp, source_whiskerLeft_fst, pullbackComparison_comp_fst]
    · simp only [Category.assoc]
      erw [source_whiskerLeft_snd (span F S) (map F k)]
      dsimp [map, compositionIso]
      simp only [pullbackComparison_comp_snd, pullbackComparison_comp_snd_assoc,
        ← F.map_comp, source_whiskerLeft_snd]
  mapComp_naturality_left k T := by
    apply Span.hom_ext
    simp only [hom₂_comp_hom]
    apply pullback.hom_ext
    · simp only [Category.assoc]
      erw [source_whiskerRight_fst (map F k) (span F T)]
      dsimp [map, compositionIso]
      simp only [pullbackComparison_comp_fst, pullbackComparison_comp_fst_assoc,
        ← F.map_comp, source_whiskerRight_fst]
    · simp only [Category.assoc]
      erw [source_whiskerRight_snd (map F k) (span F T)]
      dsimp [map, compositionIso]
      rw [pullbackComparison_comp_snd, ← F.map_comp, source_whiskerRight_snd, pullbackComparison_comp_snd]
  map₂_associator S T U := by
    apply Span.hom_ext
    simp only [hom₂_comp_hom]
    apply pullback.hom_ext
    · simp only [Category.assoc]
      erw [source_whiskerLeft_fst (span F S) (compositionIso F T U).hom,
        source_associator_fst (span F S) (span F T) (span F U),
        source_whiskerRight_fst_assoc (compositionIso F S T).hom (span F U)]
      dsimp [map, compositionIso]
      simp only [pullbackComparison_comp_fst, pullbackComparison_comp_fst_assoc,
        ← F.map_comp, source_associator_fst]
    · apply pullback.hom_ext
      · simp only [Category.assoc]
        erw [source_whiskerLeft_snd_assoc (span F S) (compositionIso F T U).hom,
          source_associator_snd_fst (span F S) (span F T) (span F U),
          source_whiskerRight_fst_assoc (compositionIso F S T).hom (span F U)]
        dsimp [map, compositionIso]
        simp only [pullbackComparison_comp_fst, pullbackComparison_comp_snd,
          pullbackComparison_comp_fst_assoc, pullbackComparison_comp_snd_assoc,
          ← F.map_comp, source_associator_snd_fst]
      · simp only [Category.assoc]
        erw [source_whiskerLeft_snd_assoc (span F S) (compositionIso F T U).hom,
          source_associator_snd_snd (span F S) (span F T) (span F U),
          source_whiskerRight_snd (compositionIso F S T).hom (span F U)]
        dsimp [map, compositionIso]
        simp only [pullbackComparison_comp_snd, pullbackComparison_comp_snd_assoc,
          ← F.map_comp, source_associator_snd_snd]
  map₂_leftUnitor S := by
    apply Span.hom_ext
    simp only [hom₂_comp_hom, leftUnitor_hom_hom, πᵣ]
    erw [source_whiskerRight_snd (unitIso F _).hom (span F S)]
    exact (pullbackComparison_comp_snd F _ _).symm
  map₂_rightUnitor S := by
    apply Span.hom_ext
    simp only [hom₂_comp_hom, rightUnitor_hom_hom, πₗ]
    erw [source_whiskerLeft_fst (span F S) (unitIso F _).hom]
    exact (pullbackComparison_comp_fst F _ _).symm
set_option backward.isDefEq.respectTransparency false in
/-- Interpret spans using only pullback preservation. -/
def pseudofunctor : Bases C ⥤ᵖ Bases D :=
  Pseudofunctor.mkOfOplax (oplax F)
    { mapIdIso X := unitIso F X.of
      mapCompIso S T := compositionIso F S T }

/-- Interpret the pullback payload and apex, then retain the right-leg map. -/
def actionIso {X Y : C} (S : Spans X Y) :
    action S ⋙ Over.post F ≅ Over.post F ⋙ action (span F S) :=
  NatIso.ofComponents (fun V => Over.isoMk (PreservesPullback.iso F V.hom S.l) (by
    change pullbackComparison F V.hom S.l ≫ pullback.snd _ _ ≫ F.map S.r = _
    rw [← Category.assoc, pullbackComparison_comp_snd, ← F.map_comp]
    rfl)) (by
      intro V W k
      apply Over.OverMorphism.ext
      have h := congrArg CommaMorphism.left ((MixedBaseChange.comparison F S.l).naturality k)
      exact h)

theorem unit_value (X : C) (V : Over X) :
    ((SpanAction.unitIso X).hom.app V).left = pullback.fst V.hom (𝟙 X) := by
  dsimp [SpanAction.unitIso, Functor.isoWhiskerLeft, Over.mapId, Over.pullbackId]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The object components are postcomposition functors, not assumed equivalences. -/
def transformation : Pseudofunctor.StrongTrans (SpanAction.pseudofunctor (C := C))
    ((pseudofunctor F).comp (SpanAction.pseudofunctor (C := D))) where
  app X := (Over.post (X := X.of) F).toCatHom
  naturality S := Cat.Hom.isoMk (actionIso F S)
  naturality_naturality {a b} {S T} k := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext V
    change Over a.of at V
    apply Over.OverMorphism.ext
    change F.map ((actionMap k).app V).left ≫ ((actionIso F T).hom.app V).left =
      ((actionIso F S).hom.app V).left ≫
        ((actionMap (map F k)).app ((Over.post F).obj V)).left
    dsimp [Over.Hom.left, Over.homMk, Over.isoMk, CostructuredArrow.homMk,
      CostructuredArrow.isoMk, Comma.isoMk, actionIso, actionMap, map]
    apply pullback.hom_ext <;> simp only [Category.assoc, pullbackComparison_comp_fst,
      pullbackComparison_comp_snd, pullback.lift_fst, pullback.lift_snd,
      pullbackComparison_comp_snd_assoc, ← F.map_comp]
  naturality_id X := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext V
    change Over X.of at V
    apply Over.OverMorphism.ext
    change ((actionIso F (Span.id X.of)).hom.app V).left ≫
      ((actionMap (unitIso F X.of).hom).app ((Over.post F).obj V)).left ≫
      ((SpanAction.unitIso (F.obj X.of)).hom.app ((Over.post F).obj V)).left =
        F.map ((SpanAction.unitIso X.of).hom.app V).left ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.comp_id]
    rw [unit_value, unit_value]
    dsimp [Over.Hom.left, Over.homMk, Over.isoMk, CostructuredArrow.homMk,
      CostructuredArrow.isoMk, Comma.isoMk, actionIso, actionMap, unitIso]
    simp only [pullback.lift_fst, pullbackComparison_comp_fst]
  naturality_comp {a b c} S T := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext V
    change Over a.of at V
    apply Over.OverMorphism.ext
    change ((actionIso F (Span.comp S T)).hom.app V).left ≫
      ((actionMap (compositionIso F S T).hom).app ((Over.post F).obj V)).left ≫
      (compositionHom (span F S) (span F T) ((Over.post F).obj V)).left =
      F.map (compositionHom S T V).left ≫ 𝟙 _ ≫
        ((actionIso F T).hom.app ((action S).obj V)).left ≫ 𝟙 _ ≫
        ((action (span F T)).map ((actionIso F S).hom.app V)).left ≫ 𝟙 _
    simp only [Category.comp_id, Category.id_comp]
    dsimp [Over.Hom.left, Over.homMk, Over.isoMk, CostructuredArrow.homMk,
      CostructuredArrow.isoMk, Comma.isoMk, actionIso, actionMap, compositionIso, compositionHom, action, Over.pullback, Over.map]
    apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp only [Category.assoc, pullbackComparison_comp_fst, pullbackComparison_comp_snd,
      pullbackComparison_comp_fst_assoc, pullbackComparison_comp_snd_assoc,
      pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, ← F.map_comp]
    · simp only [Category.assoc, pullbackComparison_comp_snd,
      pullbackComparison_comp_snd_assoc, pullback.lift_snd, pullback.lift_snd_assoc, ← F.map_comp]
@[reassoc (attr := simp)] theorem action_value {X Y : C} (S : Spans X Y) (V : Over X) :
    ((actionIso F S).hom.app V).left ≫ pullback.fst (F.map V.hom) (F.map S.l) =
      F.map (pullback.fst V.hom S.l) := pullbackComparison_comp_fst _ _ _
@[reassoc (attr := simp)] theorem action_apex {X Y : C} (S : Spans X Y) (V : Over X) :
    ((actionIso F S).hom.app V).left ≫ pullback.snd (F.map V.hom) (F.map S.l) =
      F.map (pullback.snd V.hom S.l) := pullbackComparison_comp_snd _ _ _

theorem action_mixed {X Y : C} (S : Spans X Y) (V : Over X) :
    ((actionIso F S).hom.app V).left = ((MixedBaseChange.comparison F S.l).app V).left := rfl

theorem span_identity {X Y : C} (S : Spans X Y) : span (𝟭 C) S = S := by cases S; rfl

theorem action_identity {X Y : C} (S : Spans X Y) (V : Over X) :
    ((actionIso (𝟭 C) S).hom.app V).left = 𝟙 _ := MixedBaseChange.identity S.l V

variable {E : Type u} [Category.{v} E] [HasPullbacks E]
variable (G : D ⥤ E) [PreservesLimitsOfShape WalkingCospan G]

omit [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
  [PreservesLimitsOfShape WalkingCospan G] in
theorem span_composition {X Y : C} (S : Spans X Y) :
    span (F ⋙ G) S = span G (span F S) := rfl

theorem apex_composition {X Y Z : C} (S : Spans X Y) (T : Spans Y Z) :
    (compositionIso (F ⋙ G) S T).hom.hom =
      G.map (compositionIso F S T).hom.hom ≫
        (compositionIso G (span F S) (span F T)).hom.hom :=
  pullbackComparison_comp F G S.r T.l

theorem action_composition {X Y : C} (S : Spans X Y) (V : Over X) :
    ((actionIso (F ⋙ G) S).hom.app V).left =
      G.map ((actionIso F S).hom.app V).left ≫
        ((actionIso G (span F S)).hom.app ((Over.post F).obj V)).left :=
  MixedBaseChange.composition F G S.l V

set_option backward.isDefEq.respectTransparency false in
theorem composition_transport {X Y Z : Bases C} (S : X ⟶ Y) (T : Y ⟶ Z) (V : Over X.of) :
    ((actionIso F (Span.comp S T)).hom.app V).left ≫
      ((actionMap (compositionIso F S T).hom).app ((Over.post F).obj V)).left ≫
      ((SpanAction.compositionIso (span F S) (span F T)).hom.app ((Over.post F).obj V)).left =
      F.map ((SpanAction.compositionIso S T).hom.app V).left ≫
        ((actionIso F T).hom.app ((action S).obj V)).left ≫
        ((action (span F T)).map ((actionIso F S).hom.app V)).left := by
  have h := congrArg (fun η => (η.toNatTrans.app V).left) ((transformation F).naturality_comp S T)
  change ((actionIso F (Span.comp S T)).hom.app V).left ≫
      ((actionMap (compositionIso F S T).hom).app ((Over.post F).obj V)).left ≫
      ((SpanAction.compositionIso (span F S) (span F T)).hom.app ((Over.post F).obj V)).left =
      F.map ((SpanAction.compositionIso S T).hom.app V).left ≫ 𝟙 _ ≫
        ((actionIso F T).hom.app ((action S).obj V)).left ≫ 𝟙 _ ≫
        ((action (span F T)).map ((actionIso F S).hom.app V)).left ≫ 𝟙 _ at h
  simpa only [Category.id_comp, Category.comp_id] using h

theorem beckChevalley_transport {X Y Z : Bases C} (S : X ⟶ Y) (T : Y ⟶ Z) (V : Over X.of) :
    ((actionIso F (Span.comp S T)).hom.app V).left ≫
      ((actionMap (compositionIso F S T).hom).app ((Over.post F).obj V)).left ≫
      ((SpanAction.beckChevalley (span F S) (span F T)).hom.app ((Over.post F).obj V)).left =
      F.map ((SpanAction.beckChevalley S T).hom.app V).left ≫
        ((actionIso F T).hom.app ((action S).obj V)).left ≫
        ((action (span F T)).map ((actionIso F S).hom.app V)).left := by
  rw [← SpanAction.compositionIso_eq_beckChevalley, ← SpanAction.compositionIso_eq_beckChevalley]
  exact composition_transport F S T V
end SquareKit.SpanInterpretation

import SquareKit.IndexedSumBaseChange
import SquareKit.DependentBaseChangeIdentity
import Mathlib.CategoryTheory.Bicategory.Span.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-! Pull–push on all-leg spans, with complete selected projections and derived coherence. -/
noncomputable section
namespace SquareKit.SpanAction
open CategoryTheory Limits Span.SpanBicat
universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
/-- Both legs admit every morphism; only pullbacks are required. -/
abbrev Spans (X Y : C) := Span (⊤ : MorphismProperty C) ⊤ X Y
/-- The existing Mathlib bicategory of spans with unrestricted legs. -/
abbrev Bases (C : Type u) [Category.{v} C] := Span.SpanBicat C ⊤ ⊤
variable {X Y Z : C}
/-- Pull back along the left leg and push forward along the right leg. -/
abbrev action (S : Spans X Y) : Over X ⥤ Over Y := Over.pullback S.l ⋙ Over.map S.r

/-- An apex map preserves the payload and applies its specified map to the witness. -/
def actionMap {S T : Spans X Y} (k : S ⟶ T) : action S ⟶ action T where
  app V := Over.homMk (pullback.lift (pullback.fst V.hom S.l)
    (pullback.snd V.hom S.l ≫ k.hom) (by simp [pullback.condition])) (by
      simp [action, Category.assoc])
  naturality V W f := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp [action, Over.pullback, Category.assoc]

@[reassoc (attr := simp)] theorem actionMap_value {S T : Spans X Y} (k : S ⟶ T) (V : Over X) :
    ((actionMap k).app V).left ≫ pullback.fst V.hom T.l = pullback.fst V.hom S.l := by
  simp [actionMap]
@[reassoc (attr := simp)] theorem actionMap_apex {S T : Spans X Y} (k : S ⟶ T) (V : Over X) :
    ((actionMap k).app V).left ≫ pullback.snd V.hom T.l = pullback.snd V.hom S.l ≫ k.hom := by
  simp [actionMap]

/-- Covariant action on spans and arbitrary, possibly noninvertible, apex maps. -/
def homFunctor (X Y : C) : Spans X Y ⥤ (Over X ⥤ Over Y) where
  obj := action
  map := actionMap
  map_id S := by
    apply NatTrans.ext
    funext V
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp
  map_comp k h := by
    apply NatTrans.ext
    funext V
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp [Category.assoc]

-- Explicit component: reassociate the chosen pullbacks, retaining all coordinates.
/-- Reassociate the selected payload and the two compatible apex witnesses. -/
def compositionHom (S : Spans X Y) (T : Spans Y Z) (V : Over X) :
    (action (Span.comp S T)).obj V ⟶ (action S ⋙ action T).obj V :=
  Over.homMk (pullback.lift
    (pullback.lift (pullback.fst V.hom (pullback.fst S.r T.l ≫ S.l))
      (pullback.snd V.hom (pullback.fst S.r T.l ≫ S.l) ≫ pullback.fst S.r T.l)
      (by simp [pullback.condition, Category.assoc]))
    (pullback.snd V.hom (pullback.fst S.r T.l ≫ S.l) ≫ pullback.snd S.r T.l)
    (by simp [Category.assoc, pullback.condition])) (by simp [action, Category.assoc])

/-- Recover the composite apex without forgetting either witness. -/
def compositionInv (S : Spans X Y) (T : Spans Y Z) (V : Over X) :
    (action S ⋙ action T).obj V ⟶ (action (Span.comp S T)).obj V :=
  Over.homMk (pullback.lift
    (pullback.fst (pullback.snd V.hom S.l ≫ S.r) T.l ≫ pullback.fst V.hom S.l)
    (pullback.lift
      (pullback.fst (pullback.snd V.hom S.l ≫ S.r) T.l ≫ pullback.snd V.hom S.l)
      (pullback.snd (pullback.snd V.hom S.l ≫ S.r) T.l)
      (by simp [Category.assoc, ← pullback.condition]))
    (by simp [Category.assoc, ← pullback.condition])) (by simp [action])

/-- The invertible comparison from composite action to sequential action. -/
def compositionIso (S : Spans X Y) (T : Spans Y Z) :
    action (Span.comp S T) ≅ action S ⋙ action T :=
  NatIso.ofComponents (fun V => {
    hom := compositionHom S T V
    inv := compositionInv S T V
    hom_inv_id := by
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · simp [compositionHom, compositionInv, Category.assoc]
      · apply pullback.hom_ext <;> simp [compositionHom, compositionInv, Category.assoc]
    inv_hom_id := by
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · apply pullback.hom_ext <;> simp [compositionHom, compositionInv, Category.assoc]
      · simp [compositionHom, compositionInv, Category.assoc] }) (by
        intro V W k
        apply Over.OverMorphism.ext
        apply pullback.hom_ext
        · apply pullback.hom_ext <;> simp [compositionHom, action, Over.pullback, Category.assoc]
        · simp [compositionHom, action, Over.pullback, Category.assoc])

/-- The compositor preserves the whole input value. -/
@[reassoc (attr := simp)] theorem composition_value (S : Spans X Y) (T : Spans Y Z)
    (V : Over X) :
    ((compositionIso S T).hom.app V).left ≫
      pullback.fst (pullback.snd V.hom S.l ≫ S.r) T.l ≫ pullback.fst V.hom S.l =
      pullback.fst V.hom (pullback.fst S.r T.l ≫ S.l) := by
  simp [compositionIso, compositionHom]
/-- The first apex witness survives composition. -/
@[reassoc (attr := simp)] theorem composition_first (S : Spans X Y) (T : Spans Y Z)
    (V : Over X) :
    ((compositionIso S T).hom.app V).left ≫
      pullback.fst (pullback.snd V.hom S.l ≫ S.r) T.l ≫ pullback.snd V.hom S.l =
      pullback.snd V.hom (pullback.fst S.r T.l ≫ S.l) ≫ pullback.fst S.r T.l := by
  simp [compositionIso, compositionHom]
/-- The second apex witness survives composition. -/
@[reassoc (attr := simp)] theorem composition_second (S : Spans X Y) (T : Spans Y Z)
    (V : Over X) :
    ((compositionIso S T).hom.app V).left ≫
      pullback.snd (pullback.snd V.hom S.l ≫ S.r) T.l =
      pullback.snd V.hom (pullback.fst S.r T.l ≫ S.l) ≫ pullback.snd S.r T.l := by
  simp [compositionIso, compositionHom]


@[reassoc (attr := simp)] theorem pullbackComp_value {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D) (V : Over D) :
    ((Over.pullbackComp f g).hom.app V).left ≫
      pullback.fst (pullback.snd V.hom g) f ≫ pullback.fst V.hom g =
      pullback.fst V.hom (f ≫ g) := by
  simp [Over.pullbackComp, conjugateIsoEquiv, conjugateEquiv, mateEquiv,
    Over.mapPullbackAdj_counit_app, Over.mapPullbackAdj_unit_app,
    Over.mapComp, Over.pullback, Category.assoc]

@[reassoc (attr := simp)] theorem pullbackComp_apex {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D) (V : Over D) :
    ((Over.pullbackComp f g).hom.app V).left ≫
      pullback.snd (pullback.snd V.hom g) f = pullback.snd V.hom (f ≫ g) := Over.w _

/-- The composition comparison assembled from the actual Beck–Chevalley cell. -/
def beckChevalley (S : Spans X Y) (T : Spans Y Z) :
    action (Span.comp S T) ≅ action S ⋙ action T :=
  Functor.isoWhiskerRight (Over.pullbackComp (pullback.fst S.r T.l) S.l)
      (Over.map (pullback.snd S.r T.l ≫ T.r)) ≪≫
    Functor.isoWhiskerLeft _ (Over.mapComp (pullback.snd S.r T.l) T.r) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _) _ ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (Over.pullback S.l)
      (DependentBaseChange.leftComparison (IsPullback.of_hasPullback S.r T.l))) _ ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _).symm _ ≪≫
    Functor.associator _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem compositionIso_eq_beckChevalley (S : Spans X Y) (T : Spans Y Z) :
    compositionIso S T = beckChevalley S T := by
  apply Iso.ext
  apply NatTrans.ext
  funext V
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp [compositionIso, compositionHom, beckChevalley, Over.pullback, Category.assoc]
      erw [DependentBaseChange.leftComparison_fst_assoc
        (IsPullback.of_hasPullback S.r T.l) ((Over.pullback S.l).obj V)]
      exact (pullbackComp_value _ _ V).symm
    · simp [compositionIso, compositionHom, beckChevalley, Over.pullback, Category.assoc]
      erw [DependentBaseChange.leftComparison_fst_assoc
        (IsPullback.of_hasPullback S.r T.l) ((Over.pullback S.l).obj V)]
      erw [pullback.condition]
      simp
  · simp [compositionIso, compositionHom, beckChevalley, Over.pullback, Category.assoc]
    erw [DependentBaseChange.leftComparison_snd
      (IsPullback.of_hasPullback S.r T.l) ((Over.pullback S.l).obj V)]
    simp


/-- Normalize both identity legs using the canonical slice isomorphisms. -/
def unitIso (X : C) : action (Span.id X) ≅ 𝟭 (Over X) :=
  Functor.isoWhiskerLeft (Over.pullback (𝟙 X)) (Over.mapId X) ≪≫
    Functor.rightUnitor _ ≪≫ Over.pullbackId

open Bicategory Span.SpanBicat

@[simp] theorem source_comp_l {X Y Z : Bases C} (S : X ⟶ Y) (T : Y ⟶ Z) :
    (S ≫ T).l = pullback.fst S.r T.l ≫ S.l := rfl
@[simp] theorem source_comp_r {X Y Z : Bases C} (S : X ⟶ Y) (T : Y ⟶ Z) :
    (S ≫ T).r = pullback.snd S.r T.l ≫ T.r := rfl

@[reassoc (attr := simp)] theorem source_whiskerLeft_fst {X Y Z : Bases C}
    (S : X ⟶ Y) {T U : Y ⟶ Z} (k : T ⟶ U) :
    (S ◁ k).hom ≫ pullback.fst S.r U.l = pullback.fst S.r T.l :=
  whiskerLeft_hom_πₗ S k
@[reassoc (attr := simp)] theorem source_whiskerLeft_snd {X Y Z : Bases C}
    (S : X ⟶ Y) {T U : Y ⟶ Z} (k : T ⟶ U) :
    (S ◁ k).hom ≫ pullback.snd S.r U.l = pullback.snd S.r T.l ≫ k.hom :=
  whiskerLeft_hom_πᵣ S k
@[reassoc (attr := simp)] theorem source_whiskerRight_fst {X Y Z : Bases C}
    {S T : X ⟶ Y} (k : S ⟶ T) (U : Y ⟶ Z) :
    (k ▷ U).hom ≫ pullback.fst T.r U.l = pullback.fst S.r U.l ≫ k.hom :=
  whiskerRight_hom_πₗ k U
@[reassoc (attr := simp)] theorem source_whiskerRight_snd {X Y Z : Bases C}
    {S T : X ⟶ Y} (k : S ⟶ T) (U : Y ⟶ Z) :
    (k ▷ U).hom ≫ pullback.snd T.r U.l = pullback.snd S.r U.l :=
  whiskerRight_hom_πᵣ k U
@[reassoc (attr := simp)] theorem source_associator_fst {W X Y Z : Bases C}
    (S : W ⟶ X) (T : X ⟶ Y) (U : Y ⟶ Z) :
    (α_ S T U).hom.hom ≫ pullback.fst S.r (pullback.fst T.r U.l ≫ T.l) =
      pullback.fst (pullback.snd S.r T.l ≫ T.r) U.l ≫ pullback.fst S.r T.l :=
  associator_hom_hom_πₗ S T U
@[reassoc (attr := simp)] theorem source_associator_snd_fst {W X Y Z : Bases C}
    (S : W ⟶ X) (T : X ⟶ Y) (U : Y ⟶ Z) :
    (α_ S T U).hom.hom ≫ pullback.snd S.r (pullback.fst T.r U.l ≫ T.l) ≫
      pullback.fst T.r U.l =
      pullback.fst (pullback.snd S.r T.l ≫ T.r) U.l ≫ pullback.snd S.r T.l :=
  associator_hom_hom_πᵣ_πₗ S T U
@[reassoc (attr := simp)] theorem source_associator_snd_snd {W X Y Z : Bases C}
    (S : W ⟶ X) (T : X ⟶ Y) (U : Y ⟶ Z) :
    (α_ S T U).hom.hom ≫ pullback.snd S.r (pullback.fst T.r U.l ≫ T.l) ≫
      pullback.snd T.r U.l = pullback.snd (pullback.snd S.r T.l ≫ T.r) U.l :=
  associator_hom_hom_πᵣ_πᵣ S T U

set_option backward.isDefEq.respectTransparency false in
/-- The slice action with derived whiskering, associator and unit compatibility. -/
def pseudofunctor : Bases C ⥤ᵖ Cat.{v, max u v} where
  obj X := Cat.of (Over X.of)
  map S := (action S).toCatHom
  map₂ k := (actionMap k).toCatHom₂
  map₂_id S := congrArg NatTrans.toCatHom₂ ((homFunctor _ _).map_id S)
  map₂_comp k h := congrArg NatTrans.toCatHom₂ ((homFunctor _ _).map_comp k h)
  mapId X := Cat.Hom.isoMk (unitIso X.of)
  mapComp S T := Cat.Hom.isoMk (compositionIso S T)
  map₂_whisker_left S T U k := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext V
    apply Over.OverMorphism.ext
    dsimp [action, compositionIso, compositionHom, compositionInv, actionMap, unitIso,
      Over.mapId, Functor.isoWhiskerLeft, Span.SpanBicat.instCategoryStruct, Span.comp]
    apply pullback.hom_ext
    · simp [Category.assoc]
    · apply pullback.hom_ext <;>
        simp [Category.assoc]
  map₂_whisker_right k T := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext V
    apply Over.OverMorphism.ext
    dsimp [action, compositionIso, compositionHom, compositionInv, actionMap, unitIso,
      Over.mapId, Functor.isoWhiskerLeft, Span.SpanBicat.instCategoryStruct, Span.comp]
    apply pullback.hom_ext
    · simp [Category.assoc]
    · apply pullback.hom_ext <;>
        simp [Category.assoc]
  map₂_associator S T U := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext V
    apply Over.OverMorphism.ext
    dsimp [action, compositionIso, compositionHom, compositionInv, actionMap, unitIso,
      Over.mapId, Functor.isoWhiskerLeft, Span.SpanBicat.instCategoryStruct, Span.comp]
    apply pullback.hom_ext
    · simp [Category.assoc]
    · apply pullback.hom_ext
      · simp [Category.assoc]
      · apply pullback.hom_ext <;>
          simp [Category.assoc]
  map₂_left_unitor S := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext V
    apply Over.OverMorphism.ext
    dsimp [action, compositionIso, compositionHom, compositionInv, actionMap, unitIso,
      Over.mapId, Functor.isoWhiskerLeft, Span.SpanBicat.instCategoryStruct, Span.comp]
    apply pullback.hom_ext <;>
      simp [πᵣ]
  map₂_right_unitor S := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext V
    apply Over.OverMorphism.ext
    dsimp [action, compositionIso, compositionHom, compositionInv, actionMap, unitIso,
      Over.mapId, Functor.isoWhiskerLeft, Span.SpanBicat.instCategoryStruct, Span.comp]
    apply pullback.hom_ext <;>
      simp [πₗ]
end SquareKit.SpanAction

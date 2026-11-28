import SquareKit.PseudofunctorMapping

/-! Inverse pseudofunctors derived from local equivalence and chosen object preimages, with a counit equivalence. -/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
namespace SquareKit.BicategoryConjugation
open CategoryTheory Bicategory
universe u v w
variable {B : Type u} [Bicategory.{w,v} B]
variable (q : B → B) (e : ∀ b, Bicategory.Equivalence (q b) b)
abbrev map {a b : B} (f : a ⟶ b) : q a ⟶ q b := (e a).hom ≫ f ≫ (e b).inv
def map₂ {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : map q e f ⟶ map q e g :=
  (e a).hom ◁ (η ▷ (e b).inv)
def mapId (a : B) : map q e (𝟙 a) ≅ 𝟙 (q a) :=
  whiskerLeftIso (e a).hom (λ_ (e a).inv) ≪≫ (e a).unit.symm
def mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    map q e (f ≫ g) ≅ map q e f ≫ map q e g :=
  Iso.refl _ ≪⊗≫ whiskerLeftIso ((e a).hom ≫ f)
    (whiskerRightIso (e b).counit.symm (g ≫ (e c).inv)) ≪⊗≫ Iso.refl _
def conjugation : Pseudofunctor B B where
  obj := q
  map := map q e
  map₂ := map₂ q e
  map₂_id := by intros; dsimp [map₂, map]; simp
  map₂_comp := by intros; dsimp [map₂, map]; simp
  mapId := mapId q e
  mapComp := mapComp q e
  map₂_whisker_left := by
    intro a b c f g h η
    apply (cancel_mono (mapComp q e f h).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    calc
      _ = 𝟙 _ ⊗≫ (e a).hom ◁ f ◁
          (𝟙 b ◁ (η ▷ (e c).inv) ≫ (e b).counit.inv ▷ (h ≫ (e c).inv))
          ⊗≫ 𝟙 _ := by
        dsimp [map₂, mapComp, map, bicategoricalIsoComp]
        bicategory
      _ = 𝟙 _ ⊗≫ (e a).hom ◁ f ◁
          ((e b).counit.inv ▷ (g ≫ (e c).inv) ≫
            ((e b).inv ≫ (e b).hom) ◁ (η ▷ (e c).inv)) ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]
      _ = _ := by
        dsimp [map₂, mapComp, map, bicategoricalIsoComp]
        bicategory
  map₂_whisker_right := by
    intro a b c f g η h
    apply (cancel_mono (mapComp q e g h).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    calc
      _ = 𝟙 _ ⊗≫ (e a).hom ◁
          (η ▷ 𝟙 b ≫ g ◁ (e b).counit.inv) ▷ (h ≫ (e c).inv) ⊗≫ 𝟙 _ := by
        dsimp [map₂, mapComp, map, bicategoricalIsoComp]
        bicategory
      _ = 𝟙 _ ⊗≫ (e a).hom ◁
          (f ◁ (e b).counit.inv ≫ η ▷ ((e b).inv ≫ (e b).hom)) ▷
            (h ≫ (e c).inv) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]
      _ = _ := by
        dsimp [map₂, mapComp, map, bicategoricalIsoComp]
        bicategory
  map₂_associator := by
    intro a b c d f g h
    apply (cancel_mono ((mapComp q e f (g ≫ h)).hom ≫
      map q e f ◁ (mapComp q e g h).hom)).mp
    simp only [Category.assoc, Iso.inv_hom_id_assoc,
      whiskerLeft_inv_hom, Category.comp_id]
    calc
      _ = 𝟙 _ ⊗≫ (e a).hom ◁ f ◁
          ((e b).counit.inv ▷ (g ≫ 𝟙 c) ≫
            ((e b).inv ≫ (e b).hom) ◁ (g ◁ (e c).counit.inv)) ▷
              (h ≫ (e d).inv) ⊗≫ 𝟙 _ := by
        dsimp [map₂, mapComp, map, bicategoricalIsoComp]
        bicategory
      _ = 𝟙 _ ⊗≫ (e a).hom ◁ f ◁
          (𝟙 b ◁ (g ◁ (e c).counit.inv) ≫
            (e b).counit.inv ▷ (g ≫ (e c).inv ≫ (e c).hom)) ▷
              (h ≫ (e d).inv) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]
      _ = _ := by
        dsimp [map₂, mapComp, map, bicategoricalIsoComp]
        bicategory
  map₂_left_unitor := by
    intro a b f
    symm
    calc
      _ = 𝟙 _ ⊗≫ (leftZigzagIso (e a).unit (e a).counit).inv ▷
          (f ≫ (e b).inv) ⊗≫ 𝟙 _ := by
        dsimp [map₂, mapComp, mapId, map, bicategoricalIsoComp, leftZigzagIso]
        bicategory
      _ = _ := by
        rw [(e a).left_triangle]
        dsimp [map₂]
        bicategory
  map₂_right_unitor := by
    intro a b f
    symm
    calc
      _ = 𝟙 _ ⊗≫ (e a).hom ◁ f ◁
          (rightZigzagIso (e b).unit (e b).counit).inv ⊗≫ 𝟙 _ := by
        dsimp [map₂, mapComp, mapId, map, bicategoricalIsoComp, rightZigzagIso]
        bicategory
      _ = _ := by
        rw [(e b).right_triangle]
        dsimp [map₂]
        bicategory
end SquareKit.BicategoryConjugation

namespace SquareKit.IsoWhisker
open CategoryTheory Bicategory
universe u v w
variable {B : Type u} [Bicategory.{w,v} B]
variable {a b c d : B}
theorem middle {f : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    (j : g' ≅ g) (k : h' ≅ h) :
    f ◁ j.inv ▷ h' ≫ f ◁ g' ◁ k.hom ≫ f ◁ j.hom ▷ h = f ◁ g ◁ k.hom := by
  rw [← whiskerLeft_comp, ← whiskerLeft_comp]
  congr 1
  rw [← whisker_exchange_assoc]
  simp

theorem assoc_transport {f : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    {t : a ⟶ c} {s : b ⟶ d} (j : g' ≅ g) (k : h' ≅ h)
    (m : t ≅ f ≫ g) (n : s ≅ g ≫ h) {z : a ⟶ d} (r : f ≫ s ⟶ z) :
    m.hom ▷ h ≫ (α_ f g h).hom ≫ f ◁ n.inv ≫ r =
      t ◁ k.inv ≫ m.hom ▷ h' ≫ (α_ f g h').hom ≫
        f ◁ j.inv ▷ h' ≫ f ◁ g' ◁ k.hom ≫ f ◁ j.hom ▷ h ≫ f ◁ n.inv ≫ r := by
  rw [← Category.assoc (f ◁ j.inv ▷ h') (f ◁ g' ◁ k.hom)]
  rw [← Category.assoc ((f ◁ j.inv ▷ h') ≫ f ◁ g' ◁ k.hom) (f ◁ j.hom ▷ h)]
  rw [Category.assoc (f ◁ j.inv ▷ h') (f ◁ g' ◁ k.hom), middle j k]
  rw [whisker_exchange_assoc]
  rw [associator_naturality_right_assoc]
  simp
end SquareKit.IsoWhisker

noncomputable section
namespace SquareKit.PseudofunctorInverse
open CategoryTheory Bicategory SquareKit.BicategoryConjugation
universe u v w u' v' w'
variable {A : Type u} [Bicategory.{w,v} A] {B : Type u'} [Bicategory.{w',v'} B]
variable (F : Pseudofunctor A B)
variable [∀ a b, (F.toPrelaxFunctor.mapFunctor a b).IsEquivalence]
variable (q : B → A) (e : ∀ b, Bicategory.Equivalence (F.obj (q b)) b)
abbrev objectConjugation : Pseudofunctor B B := conjugation (fun b => F.obj (q b)) e
abbrev homFunctor (a b : B) : (a ⟶ b) ⥤ (q a ⟶ q b) :=
  (objectConjugation F q e).toPrelaxFunctor.mapFunctor a b ⋙
    (F.toPrelaxFunctor.mapFunctor (q a) (q b)).inv
abbrev pre : PrelaxFunctor B A := PrelaxFunctor.mkOfHomFunctors q (homFunctor F q e)
abbrev comparison {a b : B} (f : a ⟶ b) :
    F.map ((pre F q e).map f) ≅ (objectConjugation F q e).map f :=
  (F.toPrelaxFunctor.mapFunctor (q a) (q b)).objObjPreimageIso _
@[simp] theorem map₂_image {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    F.map₂ ((pre F q e).map₂ η) =
      (comparison F q e f).hom ≫ (objectConjugation F q e).map₂ η ≫ (comparison F q e g).inv := by
  exact (F.toPrelaxFunctor.mapFunctor (q a) (q b)).fun_inv_map _ _ _
def liftId (a : B) : (pre F q e).map (𝟙 a) ≅ 𝟙 (q a) :=
  (F.toPrelaxFunctor.mapFunctor (q a) (q a)).preimageIso
    (comparison F q e (𝟙 a) ≪≫ (objectConjugation F q e).mapId a ≪≫ (F.mapId (q a)).symm)
def liftComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (pre F q e).map (f ≫ g) ≅ (pre F q e).map f ≫ (pre F q e).map g :=
  (F.toPrelaxFunctor.mapFunctor (q a) (q c)).preimageIso
    (comparison F q e (f ≫ g) ≪≫ (objectConjugation F q e).mapComp f g ≪≫
      whiskerRightIso (comparison F q e f).symm ((objectConjugation F q e).map g) ≪≫
      whiskerLeftIso (F.map ((pre F q e).map f)) (comparison F q e g).symm ≪≫
      (F.mapComp ((pre F q e).map f) ((pre F q e).map g)).symm)
@[simp] theorem map₂_preimage {a b : A} {f g : a ⟶ b}
    (η : F.map f ⟶ F.map g) :
    F.map₂ ((F.toPrelaxFunctor.mapFunctor a b).preimage η) = η :=
  (F.toPrelaxFunctor.mapFunctor a b).map_preimage η
def inverse : Pseudofunctor B A where
  toPrelaxFunctor := pre F q e
  mapId := liftId F q e
  mapComp := liftComp F q e
  map₂_whisker_left := by
    intro a b c f g h η
    apply (F.toPrelaxFunctor.mapFunctor (q a) (q c)).map_injective
    change F.map₂ _ = F.map₂ _
    simp only [map₂_image, liftComp, Functor.preimageIso_hom, Functor.preimageIso_inv, PrelaxFunctor.map₂_comp, Pseudofunctor.map₂_whisker_left, map₂_preimage, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, whiskerLeftIso_hom, whiskerLeftIso_inv, whiskerRightIso_hom, whiskerRightIso_inv, Category.assoc]
    simp [← whisker_exchange_assoc]
  map₂_whisker_right := by
    intro a b c f g η h
    apply (F.toPrelaxFunctor.mapFunctor (q a) (q c)).map_injective
    change F.map₂ _ = F.map₂ _
    simp only [map₂_image, liftComp, Functor.preimageIso_hom, Functor.preimageIso_inv, PrelaxFunctor.map₂_comp, Pseudofunctor.map₂_whisker_right, map₂_preimage, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, whiskerLeftIso_hom, whiskerLeftIso_inv, whiskerRightIso_hom, whiskerRightIso_inv, Category.assoc]
    simp [← whisker_exchange_assoc]
  map₂_associator := by
    intro a b c d f g h
    apply (F.toPrelaxFunctor.mapFunctor (q a) (q d)).map_injective
    change F.map₂ _ = F.map₂ _
    simp only [map₂_image, liftComp, Functor.preimageIso_hom, Functor.preimageIso_inv,
      PrelaxFunctor.map₂_comp, Pseudofunctor.map₂_whisker_left,
      Pseudofunctor.map₂_whisker_right, Pseudofunctor.map₂_associator,
      map₂_preimage, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      whiskerLeftIso_hom, whiskerLeftIso_inv, whiskerRightIso_hom,
      whiskerRightIso_inv, Category.assoc]
    simp [← whisker_exchange_assoc]
    rw [associator_naturality_left_assoc]
    simp only [Iso.inv_hom_id_assoc, ← whisker_exchange_assoc, inv_hom_whiskerRight_assoc]
    exact SquareKit.IsoWhisker.assoc_transport (comparison F q e g) (comparison F q e h)
      ((objectConjugation F q e).mapComp f g) ((objectConjugation F q e).mapComp g h)
      (((objectConjugation F q e).mapComp f (g ≫ h)).inv ≫ (comparison F q e (f ≫ g ≫ h)).inv)
  map₂_left_unitor := by
    intro a b f
    apply (F.toPrelaxFunctor.mapFunctor (q a) (q b)).map_injective
    change F.map₂ _ = F.map₂ _
    simp only [map₂_image, liftComp, liftId, Functor.preimageIso_hom, PrelaxFunctor.map₂_comp, Pseudofunctor.map₂_whisker_right, Pseudofunctor.map₂_left_unitor, map₂_preimage, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom, Category.assoc]
    simp [← whisker_exchange_assoc]
    rw [whisker_exchange_assoc]
    exact congrArg (fun z => ((objectConjugation F q e).mapId a).hom ▷ (objectConjugation F q e).map f ≫ z)
      (leftUnitor_naturality (comparison F q e f).inv).symm
  map₂_right_unitor := by
    intro a b f
    apply (F.toPrelaxFunctor.mapFunctor (q a) (q b)).map_injective
    change F.map₂ _ = F.map₂ _
    simp only [map₂_image, liftComp, liftId, Functor.preimageIso_hom, PrelaxFunctor.map₂_comp, Pseudofunctor.map₂_whisker_left, Pseudofunctor.map₂_right_unitor, map₂_preimage, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom, Category.assoc]
    simp [← whisker_exchange_assoc]
end SquareKit.PseudofunctorInverse

namespace SquareKit.BicategoryConjugation
open CategoryTheory Bicategory
open scoped Pseudofunctor.StrongTrans
universe u v w
variable {B : Type u} [Bicategory.{w,v} B]
variable (q : B → B) (e : ∀ b, Bicategory.Equivalence (q b) b)
def toIdentityNat {a b : B} (f : a ⟶ b) :
    (conjugation q e).map f ≫ (e b).hom ≅ (e a).hom ≫ f := by
  change ((e a).hom ≫ f ≫ (e b).inv) ≫ (e b).hom ≅ (e a).hom ≫ f
  exact Iso.refl _ ≪⊗≫ whiskerLeftIso ((e a).hom ≫ f) (e b).counit ≪⊗≫ Iso.refl _
def toIdentity : (conjugation q e) ⟶ Pseudofunctor.id B where
  app a := (e a).hom
  naturality := toIdentityNat q e
  naturality_naturality := by
    intro a b f g η
    dsimp [conjugation, toIdentityNat, map₂, Pseudofunctor.id, bicategoricalIsoComp]
    calc
      _ = 𝟙 _ ⊗≫ (e a).hom ◁
          (η ▷ ((e b).inv ≫ (e b).hom) ≫ g ◁ (e b).counit.hom) ⊗≫ 𝟙 _ := by
        bicategory
      _ = 𝟙 _ ⊗≫ (e a).hom ◁
          (f ◁ (e b).counit.hom ≫ η ▷ 𝟙 b) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]
      _ = _ := by bicategory
  naturality_id := by
    intro a
    dsimp [conjugation, toIdentityNat, mapId, map, Pseudofunctor.id, bicategoricalIsoComp]
    bicategory
    simp
    rw [← (e a).left_triangle_hom]
    simp [leftZigzag, bicategoricalComp]
  naturality_comp := by
    intro a b c f g
    dsimp only [conjugation, Pseudofunctor.id, PrelaxFunctor.id, PrelaxFunctorStruct.id, Prefunctor.id]
    symm
    calc
      _ = 𝟙 _ ⊗≫ (e a).hom ◁ f ◁
          ((e b).counit.inv ▷ (g ≫ (e c).inv ≫ (e c).hom) ≫
            ((e b).inv ≫ (e b).hom) ◁ (g ◁ (e c).counit.hom) ≫
              (e b).counit.hom ▷ (g ≫ 𝟙 c)) ⊗≫ 𝟙 _ := by
        dsimp [conjugation, toIdentityNat, mapComp, map, Pseudofunctor.id, bicategoricalIsoComp]
        bicategory
      _ = 𝟙 _ ⊗≫ (e a).hom ◁ f ◁ (𝟙 b ◁ (g ◁ (e c).counit.hom)) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange_assoc]
        simp
      _ = _ := by
        dsimp [conjugation, toIdentityNat, mapComp, map, Pseudofunctor.id, bicategoricalIsoComp]
        bicategory
def fromIdentityNat {a b : B} (f : a ⟶ b) :
    f ≫ (e b).inv ≅ (e a).inv ≫ (conjugation q e).map f := by
  change f ≫ (e b).inv ≅ (e a).inv ≫ (e a).hom ≫ f ≫ (e b).inv
  exact Iso.refl _ ≪⊗≫ whiskerRightIso (e a).counit.symm (f ≫ (e b).inv) ≪⊗≫ Iso.refl _
def fromIdentity : Pseudofunctor.id B ⟶ conjugation q e where
  app a := (e a).inv
  naturality := fromIdentityNat q e
  naturality_naturality := by
    intro a b f g η
    dsimp [conjugation, fromIdentityNat, map₂, Pseudofunctor.id, bicategoricalIsoComp]
    calc
      _ = 𝟙 _ ⊗≫ (𝟙 a ◁ (η ▷ (e b).inv) ≫ (e a).counit.inv ▷ (g ≫ (e b).inv)) ⊗≫ 𝟙 _ := by bicategory
      _ = 𝟙 _ ⊗≫ ((e a).counit.inv ▷ (f ≫ (e b).inv) ≫
          ((e a).inv ≫ (e a).hom) ◁ (η ▷ (e b).inv)) ⊗≫ 𝟙 _ := by rw [whisker_exchange]
      _ = _ := by bicategory
  naturality_id := by
    intro a
    dsimp [conjugation, fromIdentityNat, mapId, map, Pseudofunctor.id, bicategoricalIsoComp]
    calc
      _ = 𝟙 _ ⊗≫ (rightZigzagIso (e a).unit (e a).counit).inv ⊗≫ 𝟙 _ := by
        dsimp [rightZigzagIso, bicategoricalIsoComp]
        bicategory
      _ = _ := by
        rw [(e a).right_triangle]
        dsimp
        bicategory
  naturality_comp := by
    intro a b c f g
    dsimp [conjugation, fromIdentityNat, mapComp, map, Pseudofunctor.id, bicategoricalIsoComp]
    calc
      _ = 𝟙 _ ⊗≫
          ((e a).counit.inv ▷ (f ≫ 𝟙 b ≫ g ≫ (e c).inv) ≫
            ((e a).inv ≫ (e a).hom) ◁ (f ◁ ((e b).counit.inv ▷ (g ≫ (e c).inv)))) ⊗≫ 𝟙 _ := by
        bicategory
      _ = 𝟙 _ ⊗≫
          (𝟙 a ◁ (f ◁ ((e b).counit.inv ▷ (g ≫ (e c).inv))) ≫
            (e a).counit.inv ▷ (f ≫ ((e b).inv ≫ (e b).hom) ≫ g ≫ (e c).inv)) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]
      _ = _ := by bicategory
def counitComparison : fromIdentity q e ≫ toIdentity q e ≅ 𝟙 (Pseudofunctor.id B) :=
  Pseudofunctor.StrongTrans.isoMk (fun a => (e a).counit) (by
    intro a b f
    dsimp [fromIdentity, toIdentity, fromIdentityNat, toIdentityNat,
      Pseudofunctor.id, bicategoricalIsoComp]
    symm
    calc
      _ = 𝟙 _ ⊗≫ ((e a).counit.inv ▷ (f ≫ (e b).inv ≫ (e b).hom) ≫
        ((e a).inv ≫ (e a).hom) ◁ (f ◁ (e b).counit.hom) ≫
          (e a).counit.hom ▷ (f ≫ 𝟙 b)) ⊗≫ 𝟙 _ := by bicategory
      _ = 𝟙 _ ⊗≫ (𝟙 a ◁ (f ◁ (e b).counit.hom)) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange_assoc]
        simp
      _ = _ := by bicategory)
theorem counitInv_eq (a : B) :
    (e a).hom ◁ (e a).counit.inv =
      (leftZigzagIso (e a).unit (e a).counit).inv ≫
        (e a).unit.hom ▷ (e a).hom ≫ (α_ (e a).hom (e a).inv (e a).hom).hom := by
  dsimp [leftZigzagIso, bicategoricalIsoComp]
  simp

def unitComparison : 𝟙 (conjugation q e) ≅ toIdentity q e ≫ fromIdentity q e :=
  Pseudofunctor.StrongTrans.isoMk (fun a => (e a).unit) (by
    intro a b f
    dsimp [fromIdentity, toIdentity, fromIdentityNat, toIdentityNat,
      conjugation, bicategoricalIsoComp]
    calc
      _ = 𝟙 _ ⊗≫ (e a).hom ◁ f ◁ (rightZigzagIso (e b).unit (e b).counit).hom ⊗≫
          ((e a).hom ◁ (e a).counit.inv) ▷ (f ≫ (e b).inv) ⊗≫ 𝟙 _ := by
        dsimp [rightZigzagIso, bicategoricalIsoComp]
        bicategory
      _ = _ := by
        rw [(e b).right_triangle, counitInv_eq q e a, (e a).left_triangle]
        dsimp
        bicategory)
def equivalence : Bicategory.Equivalence (conjugation q e) (Pseudofunctor.id B) :=
  Bicategory.Equivalence.mkOfAdjointifyCounit (unitComparison q e) (counitComparison q e)
end SquareKit.BicategoryConjugation

noncomputable section
namespace SquareKit.PseudofunctorInverse
open CategoryTheory Bicategory
open scoped Pseudofunctor.StrongTrans
universe u v w u' v' w'
variable {A : Type u} [Bicategory.{w,v} A] {B : Type u'} [Bicategory.{w',v'} B]
variable (F : Pseudofunctor A B)
variable [∀ a b, (F.toPrelaxFunctor.mapFunctor a b).IsEquivalence]
variable (q : B → A) (e : ∀ b, Bicategory.Equivalence (F.obj (q b)) b)
omit [∀ a b, (F.toPrelaxFunctor.mapFunctor a b).IsEquivalence] in
@[simp] theorem objectConjugation_obj (b : B) : (objectConjugation F q e).obj b = F.obj (q b) := rfl
def recovery : (inverse F q e).comp F ⟶ objectConjugation F q e where
  app a := 𝟙 (F.obj (q a))
  naturality f := ρ_ _ ≪≫ comparison F q e f ≪≫ (λ_ _).symm
  naturality_naturality := by
    intro a b f g η
    change F.map₂ ((pre F q e).map₂ η) ▷ 𝟙 _ ≫ _ = _
    rw [map₂_image]
    dsimp only [inverse]
    simp [objectConjugation_obj]
  naturality_id := by
    intro a
    dsimp [Pseudofunctor.comp, inverse, liftId]
    simp
  naturality_comp := by
    intro a b c f g
    dsimp [Pseudofunctor.comp, inverse, liftComp]
    simp
def recoveryInv : objectConjugation F q e ⟶ (inverse F q e).comp F where
  app a := 𝟙 (F.obj (q a))
  naturality f := ρ_ _ ≪≫ (comparison F q e f).symm ≪≫ (λ_ _).symm
  naturality_naturality := by
    intro a b f g η
    change (objectConjugation F q e).map₂ η ▷ 𝟙 _ ≫ _ =
      _ ≫ 𝟙 (F.obj (q a)) ◁ F.map₂ ((pre F q e).map₂ η)
    rw [map₂_image]
    dsimp only [inverse]
    simp
  naturality_id := by
    intro a
    dsimp [Pseudofunctor.comp, inverse, liftId]
    simp
  naturality_comp := by
    intro a b c f g
    dsimp [Pseudofunctor.comp, inverse, liftComp]
    simp [← whisker_exchange]
def recoveryUnit : 𝟙 ((inverse F q e).comp F) ≅ recovery F q e ≫ recoveryInv F q e :=
  Pseudofunctor.StrongTrans.isoMk (fun _ => (λ_ _).symm) (by
    intro a b f
    dsimp [recovery, recoveryInv, inverse]
    simp
    bicategory_coherence)
def recoveryCounit : recoveryInv F q e ≫ recovery F q e ≅ 𝟙 (objectConjugation F q e) :=
  Pseudofunctor.StrongTrans.isoMk (fun _ => λ_ _) (by
    intro a b f
    dsimp [recovery, recoveryInv, inverse]
    simp)
def recoveryEquivalence : Bicategory.Equivalence ((inverse F q e).comp F) (objectConjugation F q e) :=
  Bicategory.Equivalence.mkOfAdjointifyCounit (recoveryUnit F q e) (recoveryCounit F q e)
def counitEquivalence :
    Bicategory.Equivalence ((inverse F q e).comp F) (Pseudofunctor.id B) :=
  let r := recoveryEquivalence F q e
  let c := SquareKit.BicategoryConjugation.equivalence (fun b => F.obj (q b)) e
  Bicategory.Equivalence.mkOfAdjointifyCounit
    (f := r.hom ≫ c.hom) (g := c.inv ≫ r.inv)
    (r.unit ≪⊗≫ whiskerLeftIso r.hom (whiskerRightIso c.unit r.inv) ≪⊗≫ Iso.refl _)
    (Iso.refl _ ≪⊗≫ whiskerLeftIso c.inv (whiskerRightIso r.counit c.hom) ≪⊗≫ c.counit)
end SquareKit.PseudofunctorInverse

end

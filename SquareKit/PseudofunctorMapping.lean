import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
import Mathlib.CategoryTheory.Bicategory.Product
import Mathlib.Tactic.CategoryTheory.BicategoryCoherence
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

/-! Weak pseudofunctor operations and biequivalence calculus. Products, precomposition, postcomposition and hom-category lifting retain their comparison cells. -/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
namespace SquareKit.PseudofunctorMapping
open CategoryTheory Bicategory
open CategoryTheory.Prod
open scoped Pseudofunctor.StrongTrans
universe u v w u' v' w' u'' v'' w''
variable {X : Type u} [Bicategory.{v,w} X]
  {B : Type u'} [Bicategory.{v',w'} B]
  {C : Type u''} [Bicategory.{v'',w''} C]

def pair (F : Pseudofunctor X B) (G : Pseudofunctor X C) :
    Pseudofunctor X (B × C) where
  obj x := (F.obj x, G.obj x)
  map f := F.map f ×ₘ G.map f
  map₂ α := F.map₂ α ×ₘ G.map₂ α
  mapId x := Iso.prod (F.mapId x) (G.mapId x)
  mapComp f g := Iso.prod (F.mapComp f g) (G.mapComp f g)
  map₂_id f := Prod.ext (F.map₂_id f) (G.map₂_id f)
  map₂_comp α β := Prod.ext (F.map₂_comp α β) (G.map₂_comp α β)
  map₂_whisker_left := by intro a b c f g h α; exact Prod.ext (F.map₂_whisker_left f α) (G.map₂_whisker_left f α)
  map₂_whisker_right α f := Prod.ext (F.map₂_whisker_right α f) (G.map₂_whisker_right α f)
  map₂_associator f g h := Prod.ext (F.map₂_associator f g h) (G.map₂_associator f g h)
  map₂_left_unitor f := Prod.ext (F.map₂_left_unitor f) (G.map₂_left_unitor f)
  map₂_right_unitor f := Prod.ext (F.map₂_right_unitor f) (G.map₂_right_unitor f)

variable {F F' : Pseudofunctor X B} {G G' : Pseudofunctor X C}

def pairTrans (α : F ⟶ F') (β : G ⟶ G') : pair F G ⟶ pair F' G' where
  app x := α.app x ×ₘ β.app x
  naturality f := Iso.prod (α.naturality f) (β.naturality f)
  naturality_naturality η := Prod.ext (α.naturality_naturality η) (β.naturality_naturality η)
  naturality_id x := Prod.ext (α.naturality_id x) (β.naturality_id x)
  naturality_comp f g := Prod.ext (α.naturality_comp f g) (β.naturality_comp f g)

def leftTrans (α : pair F G ⟶ pair F' G') : F ⟶ F' where
  app x := (α.app x).1
  naturality f := {
    hom := (α.naturality f).hom.1
    inv := (α.naturality f).inv.1
    hom_inv_id := congrArg Prod.fst (α.naturality f).hom_inv_id
    inv_hom_id := congrArg Prod.fst (α.naturality f).inv_hom_id }
  naturality_naturality η := congrArg Prod.fst (α.naturality_naturality η)
  naturality_id x := congrArg Prod.fst (α.naturality_id x)
  naturality_comp f g := congrArg Prod.fst (α.naturality_comp f g)

def rightTrans (α : pair F G ⟶ pair F' G') : G ⟶ G' where
  app x := (α.app x).2
  naturality f := {
    hom := (α.naturality f).hom.2
    inv := (α.naturality f).inv.2
    hom_inv_id := congrArg Prod.snd (α.naturality f).hom_inv_id
    inv_hom_id := congrArg Prod.snd (α.naturality f).inv_hom_id }
  naturality_naturality η := congrArg Prod.snd (α.naturality_naturality η)
  naturality_id x := congrArg Prod.snd (α.naturality_id x)
  naturality_comp f g := congrArg Prod.snd (α.naturality_comp f g)

def pairMod {α α' : F ⟶ F'} {β β' : G ⟶ G'} (m : α ⟶ α') (n : β ⟶ β') :
    pairTrans α β ⟶ pairTrans α' β' where
  as.app x := m.as.app x ×ₘ n.as.app x
  as.naturality f := Prod.ext (m.as.naturality f) (n.as.naturality f)

def leftMod {α α' : pair F G ⟶ pair F' G'} (m : α ⟶ α') :
    leftTrans α ⟶ leftTrans α' where
  as.app x := (m.as.app x).1
  as.naturality f := congrArg Prod.fst (m.as.naturality f)

def rightMod {α α' : pair F G ⟶ pair F' G'} (m : α ⟶ α') :
    rightTrans α ⟶ rightTrans α' where
  as.app x := (m.as.app x).2
  as.naturality f := congrArg Prod.snd (m.as.naturality f)

@[simp] theorem left_pairTrans (α : F ⟶ F') (β : G ⟶ G') :
    leftTrans (pairTrans α β) = α := rfl
@[simp] theorem right_pairTrans (α : F ⟶ F') (β : G ⟶ G') :
    rightTrans (pairTrans α β) = β := rfl
@[simp] theorem pair_splitTrans (α : pair F G ⟶ pair F' G') :
    pairTrans (leftTrans α) (rightTrans α) = α := rfl
@[simp] theorem left_pairMod {α α' : F ⟶ F'} {β β' : G ⟶ G'}
    (m : α ⟶ α') (n : β ⟶ β') : leftMod (pairMod m n) = m := rfl
@[simp] theorem right_pairMod {α α' : F ⟶ F'} {β β' : G ⟶ G'}
    (m : α ⟶ α') (n : β ⟶ β') : rightMod (pairMod m n) = n := rfl
@[simp] theorem pair_splitMod {α α' : pair F G ⟶ pair F' G'} (m : α ⟶ α') :
    pairMod (leftMod m) (rightMod m) = m := rfl

/-- Full equivalence at the hom-category level of weak mapping bicategories. -/
def homEquivalence (F F' : Pseudofunctor X B) (G G' : Pseudofunctor X C) :
    ((F ⟶ F') × (G ⟶ G')) ≌ (pair F G ⟶ pair F' G') where
  functor := {
    obj α := pairTrans α.1 α.2
    map m := pairMod m.1 m.2 }
  inverse := {
    obj α := (leftTrans α, rightTrans α)
    map m := leftMod m ×ₘ rightMod m }
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)


/-- Pairing retains arbitrary weak composition comparisons. -/
theorem pair_comparison_left (F : Pseudofunctor X B) (G : Pseudofunctor X C)
    {x y z : X} (f : x ⟶ y) (g : y ⟶ z) :
    ((pair F G).mapComp f g).hom.1 = (F.mapComp f g).hom := rfl

def preTrans (R : Pseudofunctor X B) {F G : Pseudofunctor B C} (α : F ⟶ G) :
    R.comp F ⟶ R.comp G where
  app x := α.app (R.obj x)
  naturality f := α.naturality (R.map f)
  naturality_naturality η := α.naturality_naturality (R.map₂ η)
  naturality_id x := by
    dsimp [Pseudofunctor.comp]
    simp only [Bicategory.whiskerLeft_comp]
    rw [← α.naturality_naturality_assoc (R.mapId x).hom]
    rw [α.naturality_id]
    simp
  naturality_comp f g := by
    dsimp [Pseudofunctor.comp]
    simp only [Bicategory.whiskerLeft_comp]
    rw [← α.naturality_naturality_assoc (R.mapComp f g).hom]
    rw [α.naturality_comp]
    simp


def preMod (R : Pseudofunctor X B) {F G : Pseudofunctor B C}
    {α β : F ⟶ G} (m : α ⟶ β) : preTrans R α ⟶ preTrans R β where
  as.app x := m.as.app (R.obj x)
  as.naturality f := m.as.naturality (R.map f)



def pre (R : Pseudofunctor X B) :
    Pseudofunctor (Pseudofunctor B C) (Pseudofunctor X C) where
  obj F := R.comp F
  map a := preTrans R a
  map₂ m := preMod R m
  mapId F := Pseudofunctor.StrongTrans.isoMk (fun _ => Iso.refl _)
  mapComp a b := Pseudofunctor.StrongTrans.isoMk (fun _ => Iso.refl _)
  map₂_id a := rfl
  map₂_comp m n := rfl
  map₂_whisker_left := by
    intro F G H a b c m
    ext x
    simp [preTrans, preMod]
  map₂_whisker_right m a := by ext x; simp [preTrans, preMod]
  map₂_associator a b c := by ext x; simp [preTrans, preMod]
  map₂_left_unitor a := by ext x; simp [preTrans, preMod]
  map₂_right_unitor a := by ext x; simp [preTrans, preMod]


def leftFunctor (H : Pseudofunctor X (B × C)) : Pseudofunctor X B where
  obj x := (H.obj x).1
  map f := (H.map f).1
  map₂ m := (H.map₂ m).1
  mapId x := {
    hom := (H.mapId x).hom.1
    inv := (H.mapId x).inv.1
    hom_inv_id := congrArg Prod.fst (H.mapId x).hom_inv_id
    inv_hom_id := congrArg Prod.fst (H.mapId x).inv_hom_id }
  mapComp f g := {
    hom := (H.mapComp f g).hom.1
    inv := (H.mapComp f g).inv.1
    hom_inv_id := congrArg Prod.fst (H.mapComp f g).hom_inv_id
    inv_hom_id := congrArg Prod.fst (H.mapComp f g).inv_hom_id }
  map₂_id f := congrArg Prod.fst (H.map₂_id f)
  map₂_comp m n := congrArg Prod.fst (H.map₂_comp m n)
  map₂_whisker_left := by intro a b c f g h m; exact congrArg Prod.fst (H.map₂_whisker_left f m)
  map₂_whisker_right m f := congrArg Prod.fst (H.map₂_whisker_right m f)
  map₂_associator f g h := congrArg Prod.fst (H.map₂_associator f g h)
  map₂_left_unitor f := congrArg Prod.fst (H.map₂_left_unitor f)
  map₂_right_unitor f := congrArg Prod.fst (H.map₂_right_unitor f)

def rightFunctor (H : Pseudofunctor X (B × C)) : Pseudofunctor X C where
  obj x := (H.obj x).2
  map f := (H.map f).2
  map₂ m := (H.map₂ m).2
  mapId x := {
    hom := (H.mapId x).hom.2
    inv := (H.mapId x).inv.2
    hom_inv_id := congrArg Prod.snd (H.mapId x).hom_inv_id
    inv_hom_id := congrArg Prod.snd (H.mapId x).inv_hom_id }
  mapComp f g := {
    hom := (H.mapComp f g).hom.2
    inv := (H.mapComp f g).inv.2
    hom_inv_id := congrArg Prod.snd (H.mapComp f g).hom_inv_id
    inv_hom_id := congrArg Prod.snd (H.mapComp f g).inv_hom_id }
  map₂_id f := congrArg Prod.snd (H.map₂_id f)
  map₂_comp m n := congrArg Prod.snd (H.map₂_comp m n)
  map₂_whisker_left := by intro a b c f g h m; exact congrArg Prod.snd (H.map₂_whisker_left f m)
  map₂_whisker_right m f := congrArg Prod.snd (H.map₂_whisker_right m f)
  map₂_associator f g h := congrArg Prod.snd (H.map₂_associator f g h)
  map₂_left_unitor f := congrArg Prod.snd (H.map₂_left_unitor f)
  map₂_right_unitor f := congrArg Prod.snd (H.map₂_right_unitor f)

theorem pair_splitFunctor (H : Pseudofunctor X (B × C)) :
    pair (leftFunctor H) (rightFunctor H) = H := rfl


def pairPseudofunctor :
    Pseudofunctor (Pseudofunctor X B × Pseudofunctor X C) (Pseudofunctor X (B × C)) where
  obj F := pair F.1 F.2
  map a := pairTrans a.1 a.2
  map₂ m := pairMod m.1 m.2
  mapId F := Pseudofunctor.StrongTrans.isoMk (fun _ => Iso.refl _)
  mapComp a b := Pseudofunctor.StrongTrans.isoMk (fun _ => Iso.refl _)
  map₂_id a := rfl
  map₂_comp m n := rfl
  map₂_whisker_left := by
    intro F G H a b c m
    ext x ; simp [pairTrans, pairMod]
  map₂_whisker_right m a := by ext x ; simp [pairTrans, pairMod]
  map₂_associator a b c := by ext x ; simp [pairTrans, pairMod]
  map₂_left_unitor a := by ext x ; simp [pairTrans, pairMod]
  map₂_right_unitor a := by ext x ; simp [pairTrans, pairMod]

theorem pair_hom_equivalence (F G : Pseudofunctor X B × Pseudofunctor X C) :
    ((pairPseudofunctor (X := X) (B := B) (C := C)).toPrelaxFunctor.mapFunctor F G).IsEquivalence :=
  inferInstanceAs (homEquivalence F.1 G.1 F.2 G.2).functor.IsEquivalence

theorem pair_essentially_surjective (H : Pseudofunctor X (B × C)) :
    ∃ F : Pseudofunctor X B × Pseudofunctor X C,
      Nonempty (Bicategory.Equivalence ((pairPseudofunctor (X := X) (B := B) (C := C)).obj F) H) := by
  refine ⟨(leftFunctor H, rightFunctor H), ?_⟩
  exact ⟨Bicategory.Equivalence.id H⟩

end SquareKit.PseudofunctorMapping
namespace SquareKit.PseudofunctorPostcomposition
open CategoryTheory Bicategory
open scoped Pseudofunctor.StrongTrans
universe u v w u' v' w' u'' v'' w''
variable {B : Type u} [Bicategory.{v,w} B]
  {C : Type u'} [Bicategory.{v',w'} C]
  {D : Type u''} [Bicategory.{v'',w''} D]
def postTrans (S : Pseudofunctor C D) {F G : Pseudofunctor B C} (a : F ⟶ G) :
    F.comp S ⟶ G.comp S where
  app x := S.map (a.app x)
  naturality {x y} f := (S.mapComp (F.map f) (a.app y)).symm ≪≫
    S.map₂Iso (a.naturality f) ≪≫ S.mapComp (a.app x) (G.map f)
  naturality_naturality {x y f g} e := by
    dsimp only [Pseudofunctor.comp, PrelaxFunctor.comp, PrelaxFunctorStruct.comp, PrelaxFunctor.map₂Iso,
      PrelaxFunctor.mapFunctor, Functor.mapIso]
    have h := congrArg (fun z => (S.mapComp (F.map f) (a.app y)).inv ≫ S.map₂ z ≫
      (S.mapComp (a.app x) (G.map g)).hom) (a.naturality_naturality e)
    simpa only [Pseudofunctor.comp, Iso.trans_hom, Iso.symm_hom,
      S.map₂_comp, S.map₂_whisker_left, S.map₂_whisker_right, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using h
  naturality_id x := by
    dsimp [Pseudofunctor.comp]
    rw [a.naturality_id_hom]
    simp [S.map₂_iso_inv, Category.assoc, ← inv_whiskerLeft]
  naturality_comp f g := by
    dsimp [Pseudofunctor.comp]
    rw [a.naturality_comp_hom]
    simp [S.map₂_iso_inv, Category.assoc, ← inv_whiskerLeft]
    simp only [inv_whiskerLeft, IsIso.Iso.inv_inv]

def postMod (S : Pseudofunctor C D) {F G : Pseudofunctor B C}
    {a b : F ⟶ G} (m : a ⟶ b) : postTrans S a ⟶ postTrans S b where
  as.app x := S.map₂ (m.as.app x)
  as.naturality {x y} f := by
    dsimp only [postTrans, Pseudofunctor.comp, PrelaxFunctor.comp,
      PrelaxFunctorStruct.comp, PrelaxFunctor.map₂Iso, PrelaxFunctor.mapFunctor, Functor.mapIso]
    have h := congrArg (fun z => (S.mapComp (F.map f) (a.app y)).inv ≫ S.map₂ z ≫
      (S.mapComp (b.app x) (G.map f)).hom) (m.as.naturality f)
    simpa only [Iso.trans_hom, Iso.symm_hom, Prefunctor.comp, S.map₂_comp, S.map₂_whisker_left, S.map₂_whisker_right, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using h

def postHom (S : Pseudofunctor C D) (F G : Pseudofunctor B C) :
    (F ⟶ G) ⥤ (F.comp S ⟶ G.comp S) where
  obj a := postTrans S a
  map m := postMod S m
  map_id a := by ext x; exact S.map₂_id (a.app x)
  map_comp m n := by ext x; exact S.map₂_comp (m.as.app x) (n.as.app x)

def postId (S : Pseudofunctor C D) (F : Pseudofunctor B C) :
    postTrans S (𝟙 F) ≅ 𝟙 (F.comp S) :=
  Pseudofunctor.StrongTrans.isoMk (fun x => S.mapId (F.obj x)) (by
    intro x y f
    dsimp [postTrans, Pseudofunctor.comp]
    simp [S.map₂_iso_inv, Category.assoc])

def postComp (S : Pseudofunctor C D) {F G H : Pseudofunctor B C}
    (a : F ⟶ G) (b : G ⟶ H) :
    postTrans S (a ≫ b) ≅ postTrans S a ≫ postTrans S b :=
  Pseudofunctor.StrongTrans.isoMk (fun x => S.mapComp (a.app x) (b.app x)) (by
    intro x y f
    dsimp [postTrans, Pseudofunctor.comp]
    simp [S.map₂_iso_inv, Category.assoc, -inv_whiskerLeft]
    simp only [inv_whiskerLeft, IsIso.Iso.inv_inv])

def post (S : Pseudofunctor C D) :
    Pseudofunctor (Pseudofunctor B C) (Pseudofunctor B D) where
  obj F := F.comp S
  map a := postTrans S a
  map₂ m := postMod S m
  mapId F := postId S F
  mapComp a b := postComp S a b
  map₂_id a := by ext x; exact S.map₂_id (a.app x)
  map₂_comp m n := by ext x; exact S.map₂_comp (m.as.app x) (n.as.app x)
  map₂_whisker_left := by
    intro F G H a b c m
    ext x
    exact S.map₂_whisker_left (a.app x) (m.as.app x)
  map₂_whisker_right m a := by ext x; exact S.map₂_whisker_right (m.as.app x) (a.app x)
  map₂_associator a b c := by ext x; exact S.map₂_associator (a.app x) (b.app x) (c.app x)
  map₂_left_unitor a := by ext x; exact S.map₂_left_unitor (a.app x)
  map₂_right_unitor a := by ext x; exact S.map₂_right_unitor (a.app x)

end SquareKit.PseudofunctorPostcomposition
namespace SquareKit.PseudofunctorComposition
open CategoryTheory Bicategory
universe u v w u' v' w' u'' v'' w'' u''' v''' w'''
variable {A : Type u} [Bicategory.{v,w} A]
  {B : Type u'} [Bicategory.{v',w'} B]
  {C : Type u''} [Bicategory.{v'',w''} C]
  {D : Type u'''} [Bicategory.{v''',w'''} D]

theorem comp_assoc (F : Pseudofunctor A B) (G : Pseudofunctor B C)
    (H : Pseudofunctor C D) : (F.comp G).comp H = F.comp (G.comp H) := by
  dsimp only [Pseudofunctor.comp]
  congr 1
  · funext x
    apply Iso.ext
    simp
  · funext x y z f g
    apply Iso.ext
    simp


theorem id_comp (F : Pseudofunctor A B) : (Pseudofunctor.id A).comp F = F := by
  dsimp only [Pseudofunctor.comp, Pseudofunctor.id]
  conv_rhs => rw [show F = {F with mapId := F.mapId, mapComp := F.mapComp} from rfl]
  congr 1
  · funext x
    apply Iso.ext
    simp
  · funext x y z f g
    apply Iso.ext
    simp

theorem comp_id (F : Pseudofunctor A B) : F.comp (Pseudofunctor.id B) = F := by
  dsimp only [Pseudofunctor.comp, Pseudofunctor.id]
  conv_rhs => rw [show F = {F with mapId := F.mapId, mapComp := F.mapComp} from rfl]
  congr 1
  · funext x
    apply Iso.ext
    simp
  · funext x y z f g
    apply Iso.ext
    simp

end SquareKit.PseudofunctorComposition
namespace SquareKit.HigherCategory
open CategoryTheory Bicategory
open scoped Pseudofunctor.StrongTrans
universe u v w u' v' w'

variable {B : Type u} [Bicategory.{w,v} B]
  {C : Type u'} [Bicategory.{w',v'} C]

/-- The equivalence witness must retain this particular forward 1-arrow. -/
def IsEquivalenceArrow {a b : B} (f : a ⟶ b) : Prop :=
  ∃ e : Bicategory.Equivalence a b, e.hom = f

/-- Both levels of invertibility, without supplying chosen inverse operations. -/
def IsBigroupoid (B : Type u) [Bicategory.{w,v} B] : Prop :=
  Bicategory.IsLocallyGroupoid B ∧ ∀ {a b : B} (f : a ⟶ b), IsEquivalenceArrow f

/-- A proposition about the given pseudofunctor, not a substitute forward map. -/
def IsBiequivalence (F : Pseudofunctor B C) : Prop :=
  (∀ c : C, ∃ b : B, Nonempty (Bicategory.Equivalence (F.obj b) c)) ∧
    ∀ a b : B, (F.toPrelaxFunctor.mapFunctor a b).IsEquivalence

end SquareKit.HigherCategory
namespace SquareKit.HomWhiskering
open CategoryTheory Bicategory
universe u v w
variable {B : Type u} [Bicategory.{w,v} B]
def left {a b : B} (f : a ⟶ b) (c : B) : (b ⟶ c) ⥤ (a ⟶ c) where
  obj g := f ≫ g
  map η := f ◁ η
  map_id g := whiskerLeft_id f g
  map_comp η θ := whiskerLeft_comp f η θ
def right (a : B) {b c : B} (f : b ⟶ c) : (a ⟶ b) ⥤ (a ⟶ c) where
  obj g := g ≫ f
  map η := η ▷ f
  map_id g := id_whiskerRight g f
  map_comp η θ := comp_whiskerRight η θ f
noncomputable def leftEquivalence {a b : B} (e : Bicategory.Equivalence a b) (c : B) :
    (b ⟶ c) ≌ (a ⟶ c) := CategoryTheory.Equivalence.mk
  (left e.hom c) (left e.inv c)
  (NatIso.ofComponents (fun g => (λ_ g).symm ≪≫
    whiskerRightIso e.counit.symm g ≪≫ α_ e.inv e.hom g) (by
      intro f g η
      dsimp [left]
      simp only [Category.assoc]
      rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
        associator_naturality_right]))
  (NatIso.ofComponents (fun g => (α_ e.hom e.inv g).symm ≪≫
    whiskerRightIso e.unit.symm g ≪≫ λ_ g) (by
      intro f g η
      dsimp [left]
      simp only [Category.assoc]
      rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
        leftUnitor_naturality]))
noncomputable def rightEquivalence (a : B) {b c : B} (e : Bicategory.Equivalence b c) :
    (a ⟶ b) ≌ (a ⟶ c) := CategoryTheory.Equivalence.mk
  (right a e.hom) (right a e.inv)
  (NatIso.ofComponents (fun g => (ρ_ g).symm ≪≫
    whiskerLeftIso g e.unit ≪≫ (α_ g e.hom e.inv).symm) (by
      intro f g η
      dsimp [right]
      simp only [Category.assoc]
      rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
        associator_inv_naturality_left]))
  (NatIso.ofComponents (fun g => α_ g e.inv e.hom ≪≫
    whiskerLeftIso g e.counit ≪≫ ρ_ g) (by
      intro f g η
      dsimp [right]
      simp only [Category.assoc]
      rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
        rightUnitor_naturality]))
instance left_isEquivalence {a b : B} (e : Bicategory.Equivalence a b) (c : B) :
    (left e.hom c).IsEquivalence := (leftEquivalence e c).isEquivalence_functor
instance right_isEquivalence (a : B) {b c : B} (e : Bicategory.Equivalence b c) :
    (right a e.hom).IsEquivalence := (rightEquivalence a e).isEquivalence_functor
end SquareKit.HomWhiskering
namespace SquareKit.Biequivalence
open CategoryTheory Bicategory SquareKit.HigherCategory
open scoped Pseudofunctor.StrongTrans
universe u v w u' v' w' u'' v'' w''
variable {A : Type u} [Bicategory.{w,v} A]
  {B : Type u'} [Bicategory.{w',v'} B]
  {C : Type u''} [Bicategory.{w'',v''} C]
noncomputable def equivalenceSymm {x y : C} (e : Bicategory.Equivalence x y) :
    Bicategory.Equivalence y x :=
  Bicategory.Equivalence.mkOfAdjointifyCounit e.counit.symm e.unit.symm

noncomputable def equivalenceComp {x y z : C} (e : Bicategory.Equivalence x y)
    (d : Bicategory.Equivalence y z) : Bicategory.Equivalence x z :=
  Bicategory.Equivalence.mkOfAdjointifyCounit
    (f := e.hom ≫ d.hom) (g := d.inv ≫ e.inv)
    (e.unit ≪⊗≫ whiskerLeftIso e.hom (whiskerRightIso d.unit e.inv) ≪⊗≫ Iso.refl _)
    (Iso.refl _ ≪⊗≫ whiskerLeftIso d.inv (whiskerRightIso e.counit d.hom) ≪⊗≫ d.counit)


def mapEquivalence (F : Pseudofunctor A B) {a b : A}
    (e : Bicategory.Equivalence a b) : Bicategory.Equivalence (F.obj a) (F.obj b) where
  hom := F.map e.hom
  inv := F.map e.inv
  unit := (F.mapId a).symm ≪≫ F.map₂Iso e.unit ≪≫ F.mapComp e.hom e.inv
  counit := (F.mapComp e.inv e.hom).symm ≪≫ F.map₂Iso e.counit ≪≫ F.mapId b
  left_triangle := by
    apply Iso.ext
    exact (F.mapAdjunction e.adj).left_triangle

theorem comp (F : Pseudofunctor A B) (G : Pseudofunctor B C)
    (hF : IsBiequivalence F) (hG : IsBiequivalence G) : IsBiequivalence (F.comp G) := by
  constructor
  · intro c
    obtain ⟨b, ⟨e⟩⟩ := hG.1 c
    obtain ⟨a, ⟨d⟩⟩ := hF.1 b
    exact ⟨a, ⟨equivalenceComp (mapEquivalence G d) e⟩⟩
  · intro a b
    let := hF.2 a b
    let := hG.2 (F.obj a) (F.obj b)
    change ((F.toPrelaxFunctor.mapFunctor a b) ⋙
      (G.toPrelaxFunctor.mapFunctor (F.obj a) (F.obj b))).IsEquivalence
    infer_instance

def reflectObjectEquivalence (F : Pseudofunctor A B)
    (hF : ∀ a b, (F.toPrelaxFunctor.mapFunctor a b).IsEquivalence)
    {a b : A} (e : Bicategory.Equivalence (F.obj a) (F.obj b)) :
    Bicategory.Equivalence a b := by
  letI := hF a b
  letI := hF b a
  letI := hF a a
  letI := hF b b
  let Fab := F.toPrelaxFunctor.mapFunctor a b
  let Fba := F.toPrelaxFunctor.mapFunctor b a
  let f := Fab.objPreimage e.hom
  let g := Fba.objPreimage e.inv
  let ef : F.map f ≅ e.hom := Fab.objObjPreimageIso e.hom
  let eg : F.map g ≅ e.inv := Fba.objObjPreimageIso e.inv
  let η : F.map (𝟙 a) ≅ F.map (f ≫ g) :=
    F.mapId a ≪≫ e.unit ≪≫ whiskerRightIso ef.symm e.inv ≪≫
      whiskerLeftIso (F.map f) eg.symm ≪≫ (F.mapComp f g).symm
  let ε : F.map (g ≫ f) ≅ F.map (𝟙 b) :=
    F.mapComp g f ≪≫ whiskerRightIso eg (F.map f) ≪≫
      whiskerLeftIso e.inv ef ≪≫ e.counit ≪≫ (F.mapId b).symm
  exact Bicategory.Equivalence.mkOfAdjointifyCounit
    ((F.toPrelaxFunctor.mapFunctor a a).preimageIso η)
    ((F.toPrelaxFunctor.mapFunctor b b).preimageIso ε)

theorem of_comp_right (F : Pseudofunctor A B) (G : Pseudofunctor B C)
    (hFG : IsBiequivalence (F.comp G)) (hG : IsBiequivalence G) : IsBiequivalence F := by
  constructor
  · intro b
    obtain ⟨a, ⟨e⟩⟩ := hFG.1 (G.obj b)
    exact ⟨a, ⟨reflectObjectEquivalence G hG.2 e⟩⟩
  · intro a b
    let := hG.2 (F.obj a) (F.obj b)
    let : ((F.toPrelaxFunctor.mapFunctor a b) ⋙
      (G.toPrelaxFunctor.mapFunctor (F.obj a) (F.obj b))).IsEquivalence := hFG.2 a b
    exact Functor.isEquivalence_of_comp_right
      (F.toPrelaxFunctor.mapFunctor a b)
      (G.toPrelaxFunctor.mapFunctor (F.obj a) (F.obj b))

theorem id : IsBiequivalence (Pseudofunctor.id A) := by
  constructor
  · intro a
    exact ⟨a, ⟨Bicategory.Equivalence.id a⟩⟩
  · intro a b
    change (𝟭 (a ⟶ b)).IsEquivalence
    infer_instance
end SquareKit.Biequivalence
namespace SquareKit.PostCompositionLift
open CategoryTheory Bicategory SquareKit.PseudofunctorPostcomposition
open scoped Pseudofunctor.StrongTrans
universe u v w u' v' w' u'' v'' w''
variable {B : Type u} [Bicategory.{w,v} B] {C : Type u'} [Bicategory.{w',v'} C]
  {D : Type u''} [Bicategory.{w'',v''} D]
variable (S : Pseudofunctor C D)
variable [∀ a b, (S.toPrelaxFunctor.mapFunctor a b).IsEquivalence]
variable {F G : Pseudofunctor B C}
@[simp] theorem map₂_preimage {a b : C} {f g : a ⟶ b} (η : S.map f ⟶ S.map g) :
    S.map₂ ((S.toPrelaxFunctor.mapFunctor a b).preimage η) = η :=
  (S.toPrelaxFunctor.mapFunctor a b).map_preimage η

def liftModification {a b : F ⟶ G} (m : postTrans S a ⟶ postTrans S b) : a ⟶ b where
  as.app x := (S.toPrelaxFunctor.mapFunctor (F.obj x) (G.obj x)).preimage (m.as.app x)
  as.naturality {x y} f := by
    apply (S.toPrelaxFunctor.mapFunctor (F.obj x) (G.obj y)).map_injective
    change S.map₂ _ = S.map₂ _
    have h := congrArg (fun z => (S.mapComp (F.map f) (a.app y)).hom ≫ z ≫
      (S.mapComp (b.app x) (G.map f)).inv) (m.as.naturality f)
    dsimp [postTrans, Pseudofunctor.comp] at h
    simpa [map₂_preimage] using h

theorem post_liftModification {a b : F ⟶ G} (m : postTrans S a ⟶ postTrans S b) :
    postMod S (liftModification S m) = m := by
  ext x
  exact map₂_preimage S (m.as.app x)
instance postHom_faithful : (postHom S F G).Faithful where
  map_injective {a b} m n h := by
    ext x
    apply (S.toPrelaxFunctor.mapFunctor (F.obj x) (G.obj x)).map_injective
    exact congrArg (fun k => k.as.app x) h
instance postHom_full : (postHom S F G).Full where
  map_surjective m := ⟨liftModification S m, post_liftModification S m⟩

variable (a : F.comp S ⟶ G.comp S)
abbrev liftApp (x : B) : F.obj x ⟶ G.obj x :=
  (S.toPrelaxFunctor.mapFunctor (F.obj x) (G.obj x)).objPreimage (a.app x)
abbrev appIso (x : B) : S.map (liftApp S a x) ≅ a.app x :=
  (S.toPrelaxFunctor.mapFunctor (F.obj x) (G.obj x)).objObjPreimageIso (a.app x)
def liftNaturality {x y : B} (f : x ⟶ y) :
    F.map f ≫ liftApp S a y ≅ liftApp S a x ≫ G.map f :=
  (S.toPrelaxFunctor.mapFunctor (F.obj x) (G.obj y)).preimageIso
    (S.mapComp (F.map f) (liftApp S a y) ≪≫
      whiskerLeftIso (S.map (F.map f)) (appIso S a y) ≪≫ a.naturality f ≪≫
      whiskerRightIso (appIso S a x).symm (S.map (G.map f)) ≪≫
      (S.mapComp (liftApp S a x) (G.map f)).symm)
def liftTransformation : F ⟶ G where
  app := liftApp S a
  naturality := liftNaturality S a
  naturality_naturality := by
    intro x y f g η
    apply (S.toPrelaxFunctor.mapFunctor (F.obj x) (G.obj y)).map_injective
    change S.map₂ _ = S.map₂ _
    simp [liftNaturality, map₂_preimage]
    rw [← whisker_exchange_assoc, ← whisker_exchange_assoc]
    have h := a.naturality_naturality η
    dsimp [Pseudofunctor.comp] at h
    simpa only [Category.assoc] using congrArg (fun k =>
      S.map (F.map f) ◁ (appIso S a y).hom ≫ k ≫
        (appIso S a x).inv ▷ S.map (G.map g) ≫
          (S.mapComp (liftApp S a x) (G.map g)).inv) h
  naturality_id := by
    intro x
    apply (S.toPrelaxFunctor.mapFunctor (F.obj x) (G.obj x)).map_injective
    change S.map₂ _ = S.map₂ _
    simp [liftNaturality, map₂_preimage, S.map₂_iso_inv]
    rw [a.naturality_id_hom]
    dsimp [Pseudofunctor.comp]
    simp [Category.assoc, ← whisker_exchange_assoc]
    simp only [← whiskerLeft_comp_assoc, ← S.map₂_comp, Iso.inv_hom_id,
      S.map₂_id, whiskerLeft_id, Category.id_comp]
    simp only [whisker_exchange_assoc]
    simp [Category.assoc]
  naturality_comp := by
    intro x y z f g
    apply (S.toPrelaxFunctor.mapFunctor (F.obj x) (G.obj z)).map_injective
    change S.map₂ _ = S.map₂ _
    simp [liftNaturality, map₂_preimage, S.map₂_iso_inv]
    rw [a.naturality_comp_hom]
    dsimp [Pseudofunctor.comp]
    simp [Category.assoc, ← whisker_exchange_assoc]
    simp only [← whiskerLeft_comp_assoc, ← S.map₂_comp, Iso.inv_hom_id,
      S.map₂_id, whiskerLeft_id, Category.id_comp]
    simp only [whisker_exchange_assoc]
    simp [Category.assoc]
def liftComparison : postTrans S (liftTransformation S a) ≅ a :=
  Pseudofunctor.StrongTrans.isoMk (appIso S a) (by
    intro x y f
    dsimp [postTrans, liftTransformation, liftNaturality, Pseudofunctor.comp]
    simp [map₂_preimage])
instance postHom_essSurj : (postHom S F G).EssSurj where
  mem_essImage a := ⟨liftTransformation S a, ⟨liftComparison S a⟩⟩
instance postHom_isEquivalence : (postHom S F G).IsEquivalence := {}
end SquareKit.PostCompositionLift

end

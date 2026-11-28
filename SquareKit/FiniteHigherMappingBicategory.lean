import SquareKit.FiniteHigherMapping
import SquareKit.BicategoryIsoComma

/-! Bicategory laws and component evaluation for full finite-diagram maps. -/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
namespace SquareKit.FiniteHigherCell.Edge
open CategoryTheory Bicategory
open SquareKit.BicategoryIsoComma
universe u v w u' v' w' u'' v'' w''
variable {X : Type u} [Bicategory.{w,v} X] {Y : Type u'} [Bicategory.{w',v'} Y]
  {Z : Type u''} [Bicategory.{w'',v''} Z]
variable (L : Pseudofunctor X Z) (R : Pseudofunctor Y Z)

theorem square_compat_iff {C : Type*} [Category C]
    {a b c d : C} (q : a ≅ b) (r : c ≅ d) (u : b ⟶ d) (v : a ⟶ c) :
    q.hom ≫ u = v ≫ r.hom ↔ u ≫ r.inv = q.inv ≫ v := by
  rw [r.comp_inv_eq, Category.assoc, q.eq_inv_comp]

def mkArrow {x y : SquareKit.BicategoryIsoComma.Obj L R} (l : x.left ⟶ y.left) (r : x.right ⟶ y.right)
    (q : x.overlap.hom ≫ R.map r ≅ L.map l ≫ y.overlap.hom) : SquareKit.BicategoryIsoComma.Arrow x y :=
  ⟨l, r, q.symm⟩

variable {L R}
theorem convert_cell {x y : SquareKit.BicategoryIsoComma.Obj L R} {f g : SquareKit.BicategoryIsoComma.Arrow x y} (m : SquareKit.BicategoryIsoComma.Cell f g) :
    f.square.inv ≫ (L.map₂ m.left ▷ y.overlap.hom) =
      (x.overlap.hom ◁ R.map₂ m.right) ≫ g.square.inv :=
  (square_compat_iff f.square.symm g.square.symm _ _).mpr m.compatibility

theorem whisker_left {x y z : SquareKit.BicategoryIsoComma.Obj L R} (f : SquareKit.BicategoryIsoComma.Arrow x y) {g h : SquareKit.BicategoryIsoComma.Arrow y z} (m : SquareKit.BicategoryIsoComma.Cell g h) :
    (composeSquare L R f.square.symm g.square.symm).hom ≫
        (L.map₂ (f.left ◁ m.left) ▷ z.overlap.hom) =
      (x.overlap.hom ◁ R.map₂ (f.right ◁ m.right)) ≫
        (composeSquare L R f.square.symm h.square.symm).hom := by
  have h := convert_cell (cellWhiskerLeft f m)
  simpa [composeSquare, SquareKit.BicategoryIsoComma.arrowComp, SquareKit.BicategoryIsoComma.cellWhiskerLeft, SquareKit.BicategoryIsoComma.cellWhiskerRight, SquareKit.BicategoryIsoComma.arrowAssociator, SquareKit.BicategoryIsoComma.cellIso, Category.assoc] using h

theorem whisker_right {x y z : SquareKit.BicategoryIsoComma.Obj L R} {f g : SquareKit.BicategoryIsoComma.Arrow x y} (m : SquareKit.BicategoryIsoComma.Cell f g) (h : SquareKit.BicategoryIsoComma.Arrow y z) :
    (composeSquare L R f.square.symm h.square.symm).hom ≫
        (L.map₂ (m.left ▷ h.left) ▷ z.overlap.hom) =
      (x.overlap.hom ◁ R.map₂ (m.right ▷ h.right)) ≫
        (composeSquare L R g.square.symm h.square.symm).hom := by
  have h := convert_cell (cellWhiskerRight m h)
  simpa [composeSquare, SquareKit.BicategoryIsoComma.arrowComp, SquareKit.BicategoryIsoComma.cellWhiskerLeft, SquareKit.BicategoryIsoComma.cellWhiskerRight, SquareKit.BicategoryIsoComma.arrowAssociator, SquareKit.BicategoryIsoComma.cellIso, Category.assoc] using h

theorem left_unitor {x y : SquareKit.BicategoryIsoComma.Obj L R} (f : SquareKit.BicategoryIsoComma.Arrow x y) :
    (composeSquare L R (identitySquare L R x.overlap.hom) f.square.symm).hom ≫
        (L.map₂ (λ_ f.left).hom ▷ y.overlap.hom) =
      (x.overlap.hom ◁ R.map₂ (λ_ f.right).hom) ≫ f.square.inv := by
  have h := convert_cell (SquareKit.BicategoryIsoComma.arrowLeftUnitor f).hom
  simpa [composeSquare, identitySquare, SquareKit.BicategoryIsoComma.arrowComp,
    SquareKit.BicategoryIsoComma.arrowId, SquareKit.BicategoryIsoComma.arrowLeftUnitor, SquareKit.BicategoryIsoComma.arrowRightUnitor, SquareKit.BicategoryIsoComma.cellIso, Category.assoc] using h

theorem right_unitor {x y : SquareKit.BicategoryIsoComma.Obj L R} (f : SquareKit.BicategoryIsoComma.Arrow x y) :
    (composeSquare L R f.square.symm (identitySquare L R y.overlap.hom)).hom ≫
        (L.map₂ (ρ_ f.left).hom ▷ y.overlap.hom) =
      (x.overlap.hom ◁ R.map₂ (ρ_ f.right).hom) ≫ f.square.inv := by
  have h := convert_cell (SquareKit.BicategoryIsoComma.arrowRightUnitor f).hom
  simpa [composeSquare, identitySquare, SquareKit.BicategoryIsoComma.arrowComp,
    SquareKit.BicategoryIsoComma.arrowId, SquareKit.BicategoryIsoComma.arrowLeftUnitor, SquareKit.BicategoryIsoComma.arrowRightUnitor, SquareKit.BicategoryIsoComma.cellIso, Category.assoc] using h

theorem associator {x y z t : SquareKit.BicategoryIsoComma.Obj L R} (f : SquareKit.BicategoryIsoComma.Arrow x y) (g : SquareKit.BicategoryIsoComma.Arrow y z) (h : SquareKit.BicategoryIsoComma.Arrow z t) :
    (composeSquare L R (composeSquare L R f.square.symm g.square.symm) h.square.symm).hom ≫
        (L.map₂ (α_ f.left g.left h.left).hom ▷ t.overlap.hom) =
      (x.overlap.hom ◁ R.map₂ (α_ f.right g.right h.right).hom) ≫
        (composeSquare L R f.square.symm (composeSquare L R g.square.symm h.square.symm)).hom := by
  have h := convert_cell (SquareKit.BicategoryIsoComma.arrowAssociator f g h).hom
  simpa [composeSquare, SquareKit.BicategoryIsoComma.arrowComp, SquareKit.BicategoryIsoComma.cellWhiskerLeft, SquareKit.BicategoryIsoComma.cellWhiskerRight, SquareKit.BicategoryIsoComma.arrowAssociator, SquareKit.BicategoryIsoComma.cellIso, Category.assoc] using h

theorem inverse {x y : SquareKit.BicategoryIsoComma.Obj L R} {f g : SquareKit.BicategoryIsoComma.Arrow x y}
    (l : f.left ≅ g.left) (r : f.right ≅ g.right)
    (h : f.square.inv ≫ (L.map₂ l.hom ▷ y.overlap.hom) =
      (x.overlap.hom ◁ R.map₂ r.hom) ≫ g.square.inv) :
    g.square.inv ≫ (L.map₂ l.inv ▷ y.overlap.hom) =
      (x.overlap.hom ◁ R.map₂ r.inv) ≫ f.square.inv := by
  exact convert_cell (SquareKit.BicategoryIsoComma.cellIso l r
    ((square_compat_iff f.square.symm g.square.symm _ _).mp h)).inv
end SquareKit.FiniteHigherCell.Edge

namespace SquareKit.FiniteHigherCell
open CategoryTheory Bicategory SquareKit.HigherCategory SquareKit.FiniteHigherMap
open SquareKit.PseudofunctorMapping SquareKit.PseudofunctorPostcomposition SquareKit.PseudofunctorComposition
open scoped Pseudofunctor.StrongTrans
universe u v w u' v' w'
variable {F : FullDiagram.{u,v,w}} {T : FullDiagram.{u',v',w'}}
variable {H K J I : Map (F := F) (T := T)}

def topLeftObj (H : Map (F := F) (T := T)) :
    SquareKit.BicategoryIsoComma.Obj (pre F.rL) (post T.rL) := ⟨H.left, H.top, H.topLeft⟩
def topLeftArrow (a : Arrow H K) :
    SquareKit.BicategoryIsoComma.Arrow (topLeftObj H) (topLeftObj K) :=
  ⟨a.left, a.top, a.topLeft.symm⟩
def topLeftCell {a b : Arrow H K} (m : Cell a b) :
    SquareKit.BicategoryIsoComma.Cell (topLeftArrow a) (topLeftArrow b) :=
  ⟨m.left, m.top, (Edge.square_compat_iff a.topLeft b.topLeft _ _).mp m.topLeft⟩

def topRightObj (H : Map (F := F) (T := T)) :
    SquareKit.BicategoryIsoComma.Obj (pre F.rR) (post T.rR) := ⟨H.right, H.top, H.topRight⟩
def topRightArrow (a : Arrow H K) :
    SquareKit.BicategoryIsoComma.Arrow (topRightObj H) (topRightObj K) :=
  ⟨a.right, a.top, a.topRight.symm⟩
def topRightCell {a b : Arrow H K} (m : Cell a b) :
    SquareKit.BicategoryIsoComma.Cell (topRightArrow a) (topRightArrow b) :=
  ⟨m.right, m.top, (Edge.square_compat_iff a.topRight b.topRight _ _).mp m.topRight⟩

def topEmptyObj (H : Map (F := F) (T := T)) :
    SquareKit.BicategoryIsoComma.Obj (pre F.r0) (post T.r0) := ⟨H.empty, H.top, H.topEmpty⟩
def topEmptyArrow (a : Arrow H K) :
    SquareKit.BicategoryIsoComma.Arrow (topEmptyObj H) (topEmptyObj K) :=
  ⟨a.empty, a.top, a.topEmpty.symm⟩
def topEmptyCell {a b : Arrow H K} (m : Cell a b) :
    SquareKit.BicategoryIsoComma.Cell (topEmptyArrow a) (topEmptyArrow b) :=
  ⟨m.empty, m.top, (Edge.square_compat_iff a.topEmpty b.topEmpty _ _).mp m.topEmpty⟩

def leftEmptyObj (H : Map (F := F) (T := T)) :
    SquareKit.BicategoryIsoComma.Obj (pre F.sL) (post T.sL) := ⟨H.empty, H.left, H.leftEmpty⟩
def leftEmptyArrow (a : Arrow H K) :
    SquareKit.BicategoryIsoComma.Arrow (leftEmptyObj H) (leftEmptyObj K) :=
  ⟨a.empty, a.left, a.leftEmpty.symm⟩
def leftEmptyCell {a b : Arrow H K} (m : Cell a b) :
    SquareKit.BicategoryIsoComma.Cell (leftEmptyArrow a) (leftEmptyArrow b) :=
  ⟨m.empty, m.left, (Edge.square_compat_iff a.leftEmpty b.leftEmpty _ _).mp m.leftEmpty⟩

def rightEmptyObj (H : Map (F := F) (T := T)) :
    SquareKit.BicategoryIsoComma.Obj (pre F.sR) (post T.sR) := ⟨H.empty, H.right, H.rightEmpty⟩
def rightEmptyArrow (a : Arrow H K) :
    SquareKit.BicategoryIsoComma.Arrow (rightEmptyObj H) (rightEmptyObj K) :=
  ⟨a.empty, a.right, a.rightEmpty.symm⟩
def rightEmptyCell {a b : Arrow H K} (m : Cell a b) :
    SquareKit.BicategoryIsoComma.Cell (rightEmptyArrow a) (rightEmptyArrow b) :=
  ⟨m.empty, m.right, (Edge.square_compat_iff a.rightEmpty b.rightEmpty _ _).mp m.rightEmpty⟩

def cellWhiskerLeft (a : Arrow H K) {b c : Arrow K J} (m : Cell b c) :
    Cell (arrowComp a b) (arrowComp a c) where
  top := a.top ◁ m.top
  left := a.left ◁ m.left
  right := a.right ◁ m.right
  empty := a.empty ◁ m.empty
  topLeft := Edge.whisker_left (topLeftArrow a) (topLeftCell m)
  topRight := Edge.whisker_left (topRightArrow a) (topRightCell m)
  topEmpty := Edge.whisker_left (topEmptyArrow a) (topEmptyCell m)
  leftEmpty := Edge.whisker_left (leftEmptyArrow a) (leftEmptyCell m)
  rightEmpty := Edge.whisker_left (rightEmptyArrow a) (rightEmptyCell m)

def cellWhiskerRight {a b : Arrow H K} (m : Cell a b) (c : Arrow K J) :
    Cell (arrowComp a c) (arrowComp b c) where
  top := m.top ▷ c.top
  left := m.left ▷ c.left
  right := m.right ▷ c.right
  empty := m.empty ▷ c.empty
  topLeft := Edge.whisker_right (topLeftCell m) (topLeftArrow c)
  topRight := Edge.whisker_right (topRightCell m) (topRightArrow c)
  topEmpty := Edge.whisker_right (topEmptyCell m) (topEmptyArrow c)
  leftEmpty := Edge.whisker_right (leftEmptyCell m) (leftEmptyArrow c)
  rightEmpty := Edge.whisker_right (rightEmptyCell m) (rightEmptyArrow c)

def cellIso {a b : Arrow H K} (t : a.top ≅ b.top) (l : a.left ≅ b.left)
    (r : a.right ≅ b.right) (e : a.empty ≅ b.empty)
    (htopLeft : a.topLeft.hom ≫ (preMod F.rL l.hom ▷ K.topLeft.hom) =
      (H.topLeft.hom ◁ postMod T.rL t.hom) ≫ b.topLeft.hom)
    (htopRight : a.topRight.hom ≫ (preMod F.rR r.hom ▷ K.topRight.hom) =
      (H.topRight.hom ◁ postMod T.rR t.hom) ≫ b.topRight.hom)
    (htopEmpty : a.topEmpty.hom ≫ (preMod F.r0 e.hom ▷ K.topEmpty.hom) =
      (H.topEmpty.hom ◁ postMod T.r0 t.hom) ≫ b.topEmpty.hom)
    (hleftEmpty : a.leftEmpty.hom ≫ (preMod F.sL e.hom ▷ K.leftEmpty.hom) =
      (H.leftEmpty.hom ◁ postMod T.sL l.hom) ≫ b.leftEmpty.hom)
    (hrightEmpty : a.rightEmpty.hom ≫ (preMod F.sR e.hom ▷ K.rightEmpty.hom) =
      (H.rightEmpty.hom ◁ postMod T.sR r.hom) ≫ b.rightEmpty.hom)
    : a ≅ b where
  hom := ⟨t.hom, l.hom, r.hom, e.hom, htopLeft, htopRight, htopEmpty, hleftEmpty, hrightEmpty⟩
  inv := {
    top := t.inv
    left := l.inv
    right := r.inv
    empty := e.inv
    topLeft := Edge.inverse (f := topLeftArrow a) (g := topLeftArrow b) l t htopLeft
    topRight := Edge.inverse (f := topRightArrow a) (g := topRightArrow b) r t htopRight
    topEmpty := Edge.inverse (f := topEmptyArrow a) (g := topEmptyArrow b) e t htopEmpty
    leftEmpty := Edge.inverse (f := leftEmptyArrow a) (g := leftEmptyArrow b) e l hleftEmpty
    rightEmpty := Edge.inverse (f := rightEmptyArrow a) (g := rightEmptyArrow b) e r hrightEmpty
  }
  hom_inv_id := Cell.ext t.hom_inv_id l.hom_inv_id r.hom_inv_id e.hom_inv_id
  inv_hom_id := Cell.ext t.inv_hom_id l.inv_hom_id r.inv_hom_id e.inv_hom_id

def arrowLeftUnitor (a : Arrow H K) : arrowComp (arrowId H) a ≅ a :=
  cellIso (λ_ a.top) (λ_ a.left) (λ_ a.right) (λ_ a.empty)
    (Edge.left_unitor (topLeftArrow a))
    (Edge.left_unitor (topRightArrow a))
    (Edge.left_unitor (topEmptyArrow a))
    (Edge.left_unitor (leftEmptyArrow a))
    (Edge.left_unitor (rightEmptyArrow a))

def arrowRightUnitor (a : Arrow H K) : arrowComp a (arrowId K) ≅ a :=
  cellIso (ρ_ a.top) (ρ_ a.left) (ρ_ a.right) (ρ_ a.empty)
    (Edge.right_unitor (topLeftArrow a))
    (Edge.right_unitor (topRightArrow a))
    (Edge.right_unitor (topEmptyArrow a))
    (Edge.right_unitor (leftEmptyArrow a))
    (Edge.right_unitor (rightEmptyArrow a))

def arrowAssociator (a : Arrow H K) (b : Arrow K J) (c : Arrow J I) :
    arrowComp (arrowComp a b) c ≅ arrowComp a (arrowComp b c) :=
  cellIso (α_ a.top b.top c.top) (α_ a.left b.left c.left)
    (α_ a.right b.right c.right) (α_ a.empty b.empty c.empty)
    (Edge.associator (topLeftArrow a) (topLeftArrow b) (topLeftArrow c))
    (Edge.associator (topRightArrow a) (topRightArrow b) (topRightArrow c))
    (Edge.associator (topEmptyArrow a) (topEmptyArrow b) (topEmptyArrow c))
    (Edge.associator (leftEmptyArrow a) (leftEmptyArrow b) (leftEmptyArrow c))
    (Edge.associator (rightEmptyArrow a) (rightEmptyArrow b) (rightEmptyArrow c))

instance categoryStruct : CategoryStruct (Map (F := F) (T := T)) where
  Hom := Arrow
  id := arrowId
  comp := arrowComp

instance bicategory : Bicategory (Map (F := F) (T := T)) where
  homCategory := homCategory
  whiskerLeft := cellWhiskerLeft
  whiskerRight := cellWhiskerRight
  associator := arrowAssociator
  leftUnitor := arrowLeftUnitor
  rightUnitor := arrowRightUnitor
  whiskerLeft_id _ _ := Cell.ext (whiskerLeft_id _ _) (whiskerLeft_id _ _) (whiskerLeft_id _ _) (whiskerLeft_id _ _)
  whiskerLeft_comp := by intros; exact Cell.ext (whiskerLeft_comp _ _ _) (whiskerLeft_comp _ _ _) (whiskerLeft_comp _ _ _) (whiskerLeft_comp _ _ _)
  id_whiskerLeft _ := Cell.ext (id_whiskerLeft _) (id_whiskerLeft _) (id_whiskerLeft _) (id_whiskerLeft _)
  comp_whiskerLeft := by intros; exact Cell.ext (comp_whiskerLeft _ _ _) (comp_whiskerLeft _ _ _) (comp_whiskerLeft _ _ _) (comp_whiskerLeft _ _ _)
  id_whiskerRight _ _ := Cell.ext (id_whiskerRight _ _) (id_whiskerRight _ _) (id_whiskerRight _ _) (id_whiskerRight _ _)
  comp_whiskerRight _ _ _ := Cell.ext (comp_whiskerRight _ _ _) (comp_whiskerRight _ _ _) (comp_whiskerRight _ _ _) (comp_whiskerRight _ _ _)
  whiskerRight_id _ := Cell.ext (whiskerRight_id _) (whiskerRight_id _) (whiskerRight_id _) (whiskerRight_id _)
  whiskerRight_comp _ _ _ := Cell.ext (whiskerRight_comp _ _ _) (whiskerRight_comp _ _ _) (whiskerRight_comp _ _ _) (whiskerRight_comp _ _ _)
  whisker_assoc := by intros; exact Cell.ext (whisker_assoc _ _ _) (whisker_assoc _ _ _) (whisker_assoc _ _ _) (whisker_assoc _ _ _)
  whisker_exchange _ _ := Cell.ext (whisker_exchange _ _) (whisker_exchange _ _) (whisker_exchange _ _) (whisker_exchange _ _)
  pentagon _ _ _ _ := Cell.ext (pentagon _ _ _ _) (pentagon _ _ _ _) (pentagon _ _ _ _) (pentagon _ _ _ _)
  triangle _ _ := Cell.ext (triangle _ _) (triangle _ _) (triangle _ _) (triangle _ _)

end SquareKit.FiniteHigherCell

namespace SquareKit.FiniteHigherCell
open CategoryTheory Bicategory SquareKit.HigherCategory SquareKit.FiniteHigherMap
open scoped Pseudofunctor.StrongTrans
universe u v w u' v' w'
variable (F : FullDiagram.{u,v,w}) (T : FullDiagram.{u',v',w'})

def evaluateTop : Pseudofunctor (Map (F := F) (T := T)) (Pseudofunctor F.top T.top) where
  obj H := H.top
  map a := a.top
  map₂ m := m.top
  mapId H := Iso.refl _
  mapComp a b := Iso.refl _
  map₂_id _ := rfl
  map₂_comp _ _ := rfl
  map₂_whisker_left := by
    intro a b c f g h η
    change f.top ◁ η.top = 𝟙 _ ≫ f.top ◁ η.top ≫ 𝟙 _
    simp
  map₂_whisker_right := by
    intro a b c f g η h
    change η.top ▷ h.top = 𝟙 _ ≫ η.top ▷ h.top ≫ 𝟙 _
    simp
  map₂_associator := by
    intro a b c d f g h
    change (α_ f.top g.top h.top).hom = 𝟙 _ ≫ 𝟙 _ ▷ h.top ≫
      (α_ f.top g.top h.top).hom ≫ f.top ◁ 𝟙 _ ≫ 𝟙 _
    simp
  map₂_left_unitor := by
    intro a b f
    change (λ_ f.top).hom = 𝟙 _ ≫ 𝟙 _ ▷ f.top ≫ (λ_ f.top).hom
    simp
  map₂_right_unitor := by
    intro a b f
    change (ρ_ f.top).hom = 𝟙 _ ≫ f.top ◁ 𝟙 _ ≫ (ρ_ f.top).hom
    simp

def evaluateLeft : Pseudofunctor (Map (F := F) (T := T)) (Pseudofunctor F.left T.left) where
  obj H := H.left
  map a := a.left
  map₂ m := m.left
  mapId H := Iso.refl _
  mapComp a b := Iso.refl _
  map₂_id _ := rfl
  map₂_comp _ _ := rfl
  map₂_whisker_left := by
    intro a b c f g h η
    change f.left ◁ η.left = 𝟙 _ ≫ f.left ◁ η.left ≫ 𝟙 _
    simp
  map₂_whisker_right := by
    intro a b c f g η h
    change η.left ▷ h.left = 𝟙 _ ≫ η.left ▷ h.left ≫ 𝟙 _
    simp
  map₂_associator := by
    intro a b c d f g h
    change (α_ f.left g.left h.left).hom = 𝟙 _ ≫ 𝟙 _ ▷ h.left ≫
      (α_ f.left g.left h.left).hom ≫ f.left ◁ 𝟙 _ ≫ 𝟙 _
    simp
  map₂_left_unitor := by
    intro a b f
    change (λ_ f.left).hom = 𝟙 _ ≫ 𝟙 _ ▷ f.left ≫ (λ_ f.left).hom
    simp
  map₂_right_unitor := by
    intro a b f
    change (ρ_ f.left).hom = 𝟙 _ ≫ f.left ◁ 𝟙 _ ≫ (ρ_ f.left).hom
    simp

def evaluateRight : Pseudofunctor (Map (F := F) (T := T)) (Pseudofunctor F.right T.right) where
  obj H := H.right
  map a := a.right
  map₂ m := m.right
  mapId H := Iso.refl _
  mapComp a b := Iso.refl _
  map₂_id _ := rfl
  map₂_comp _ _ := rfl
  map₂_whisker_left := by
    intro a b c f g h η
    change f.right ◁ η.right = 𝟙 _ ≫ f.right ◁ η.right ≫ 𝟙 _
    simp
  map₂_whisker_right := by
    intro a b c f g η h
    change η.right ▷ h.right = 𝟙 _ ≫ η.right ▷ h.right ≫ 𝟙 _
    simp
  map₂_associator := by
    intro a b c d f g h
    change (α_ f.right g.right h.right).hom = 𝟙 _ ≫ 𝟙 _ ▷ h.right ≫
      (α_ f.right g.right h.right).hom ≫ f.right ◁ 𝟙 _ ≫ 𝟙 _
    simp
  map₂_left_unitor := by
    intro a b f
    change (λ_ f.right).hom = 𝟙 _ ≫ 𝟙 _ ▷ f.right ≫ (λ_ f.right).hom
    simp
  map₂_right_unitor := by
    intro a b f
    change (ρ_ f.right).hom = 𝟙 _ ≫ f.right ◁ 𝟙 _ ≫ (ρ_ f.right).hom
    simp

def evaluateEmpty : Pseudofunctor (Map (F := F) (T := T)) (Pseudofunctor F.empty T.empty) where
  obj H := H.empty
  map a := a.empty
  map₂ m := m.empty
  mapId H := Iso.refl _
  mapComp a b := Iso.refl _
  map₂_id _ := rfl
  map₂_comp _ _ := rfl
  map₂_whisker_left := by
    intro a b c f g h η
    change f.empty ◁ η.empty = 𝟙 _ ≫ f.empty ◁ η.empty ≫ 𝟙 _
    simp
  map₂_whisker_right := by
    intro a b c f g η h
    change η.empty ▷ h.empty = 𝟙 _ ≫ η.empty ▷ h.empty ≫ 𝟙 _
    simp
  map₂_associator := by
    intro a b c d f g h
    change (α_ f.empty g.empty h.empty).hom = 𝟙 _ ≫ 𝟙 _ ▷ h.empty ≫
      (α_ f.empty g.empty h.empty).hom ≫ f.empty ◁ 𝟙 _ ≫ 𝟙 _
    simp
  map₂_left_unitor := by
    intro a b f
    change (λ_ f.empty).hom = 𝟙 _ ≫ 𝟙 _ ▷ f.empty ≫ (λ_ f.empty).hom
    simp
  map₂_right_unitor := by
    intro a b f
    change (ρ_ f.empty).hom = 𝟙 _ ≫ f.empty ◁ 𝟙 _ ≫ (ρ_ f.empty).hom
    simp
end SquareKit.FiniteHigherCell

noncomputable section

end

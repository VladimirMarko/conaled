import SquareKit.FiniteHigherDiagram

/-! Transformations and modifications of finite weak diagrams, including both chain compatibility equations. -/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
namespace SquareKit.FiniteHigherCell
open CategoryTheory Bicategory SquareKit.HigherCategory SquareKit.FiniteHigherMap
open SquareKit.PseudofunctorMapping SquareKit.PseudofunctorPostcomposition SquareKit.PseudofunctorComposition
open scoped Pseudofunctor.StrongTrans
universe u v w u' v' w'
variable {F : FullDiagram.{u,v,w}} {T : FullDiagram.{u',v',w'}}

structure ArrowCore (H K : Map (F := F) (T := T)) where
  top : H.top ⟶ K.top
  left : H.left ⟶ K.left
  right : H.right ⟶ K.right
  empty : H.empty ⟶ K.empty
  topLeft : H.topLeft.hom ≫ postTrans T.rL top ≅ preTrans F.rL left ≫ K.topLeft.hom
  topRight : H.topRight.hom ≫ postTrans T.rR top ≅ preTrans F.rR right ≫ K.topRight.hom
  topEmpty : H.topEmpty.hom ≫ postTrans T.r0 top ≅ preTrans F.r0 empty ≫ K.topEmpty.hom
  leftEmpty : H.leftEmpty.hom ≫ postTrans T.sL left ≅ preTrans F.sL empty ≫ K.leftEmpty.hom
  rightEmpty : H.rightEmpty.hom ≫ postTrans T.sR right ≅ preTrans F.sR empty ≫ K.rightEmpty.hom

variable {A : Type u} [Bicategory.{w,v} A] {B : Type u'} [Bicategory.{w',v'} B]
@[simp] theorem eqToHom_app {P Q : Pseudofunctor A B} (e : P = Q) (x : A) :
    (eqToHom e).app x = eqToHom (congrArg (fun R : Pseudofunctor A B => R.obj x) e) := by
  cases e
  rfl


def appIso {P Q : Pseudofunctor A B} {a b : P ⟶ Q} (e : a ≅ b) (x : A) : a.app x ≅ b.app x where
  hom := e.hom.as.app x
  inv := e.inv.as.app x
  hom_inv_id := by have h := congrArg (fun m => m.as.app x) e.hom_inv_id; exact h
  inv_hom_id := by have h := congrArg (fun m => m.as.app x) e.inv_hom_id; exact h

def leftPastedAppIso (H : Map (F := F) (T := T)) (x : F.top) :
    (leftPasted H.toMapCore).app x ≅
      H.leftEmpty.hom.app (F.rL.obj x) ≫ T.sL.map (H.topLeft.hom.app x) ≫
        T.cL.hom.app (H.top.obj x) := by
  dsimp only [leftPasted, Pseudofunctor.StrongTrans.comp_app, preTrans, postTrans]
  simp only [eqToHom_app]
  exact (λ_ _) ≪≫ whiskerLeftIso _ ((λ_ _) ≪≫ whiskerLeftIso _ (λ_ _))

def leftChi (H : Map (F := F) (T := T)) (x : F.top) :
    H.empty.map (F.cL.hom.app x) ≫ H.topEmpty.hom.app x ≅
      H.leftEmpty.hom.app (F.rL.obj x) ≫ T.sL.map (H.topLeft.hom.app x) ≫
        T.cL.hom.app (H.top.obj x) :=
  appIso H.leftCoherence x ≪≫ leftPastedAppIso H x


def rightPastedAppIso (H : Map (F := F) (T := T)) (x : F.top) :
    (rightPasted H.toMapCore).app x ≅
      H.rightEmpty.hom.app (F.rR.obj x) ≫ T.sR.map (H.topRight.hom.app x) ≫
        T.cR.hom.app (H.top.obj x) := by
  dsimp only [rightPasted, Pseudofunctor.StrongTrans.comp_app, preTrans, postTrans]
  simp only [eqToHom_app]
  exact (λ_ _) ≪≫ whiskerLeftIso _ ((λ_ _) ≪≫ whiskerLeftIso _ (λ_ _))

def rightChi (H : Map (F := F) (T := T)) (x : F.top) :
    H.empty.map (F.cR.hom.app x) ≫ H.topEmpty.hom.app x ≅
      H.rightEmpty.hom.app (F.rR.obj x) ≫ T.sR.map (H.topRight.hom.app x) ≫
        T.cR.hom.app (H.top.obj x) :=
  appIso H.rightCoherence x ≪≫ rightPastedAppIso H x

/-- Paste adjacent squares, retaining all associators. -/
def pasteSquare {a₀ a₁ a₂ b₀ b₁ b₂ : B}
    {h₁ : a₀ ⟶ a₁} {h₂ : a₁ ⟶ a₂} {k₁ : b₀ ⟶ b₁} {k₂ : b₁ ⟶ b₂}
    {u : a₀ ⟶ b₀} {v : a₁ ⟶ b₁} {w : a₂ ⟶ b₂}
    (q₁ : h₁ ≫ v ≅ u ≫ k₁) (q₂ : h₂ ≫ w ≅ v ≫ k₂) :
    (h₁ ≫ h₂) ≫ w ≅ u ≫ (k₁ ≫ k₂) :=
  (α_ _ _ _) ≪≫ whiskerLeftIso _ q₂ ≪≫ (α_ _ _ _).symm ≪≫
    whiskerRightIso q₁ _ ≪≫ (α_ _ _ _)

variable {H K : Map (F := F) (T := T)}

def leftDirectSquare (a : ArrowCore H K) (x : F.top) :
    (H.empty.map (F.cL.hom.app x) ≫ H.topEmpty.hom.app x) ≫ T.r0.map (a.top.app x) ≅
      a.empty.app ((F.rL.comp F.sL).obj x) ≫
        (K.empty.map (F.cL.hom.app x) ≫ K.topEmpty.hom.app x) :=
  pasteSquare (a.empty.naturality (F.cL.hom.app x)) (appIso a.topEmpty x)

def leftPastedSquare (a : ArrowCore H K) (x : F.top) :
    (H.leftEmpty.hom.app (F.rL.obj x) ≫ T.sL.map (H.topLeft.hom.app x) ≫
      T.cL.hom.app (H.top.obj x)) ≫ T.r0.map (a.top.app x) ≅
      a.empty.app ((F.rL.comp F.sL).obj x) ≫
        (K.leftEmpty.hom.app (F.rL.obj x) ≫ T.sL.map (K.topLeft.hom.app x) ≫
          T.cL.hom.app (K.top.obj x)) :=
  pasteSquare (appIso a.leftEmpty (F.rL.obj x))
    (pasteSquare ((T.sL.mapComp _ _).symm ≪≫ T.sL.map₂Iso (appIso a.topLeft x) ≪≫
      T.sL.mapComp _ _) (T.cL.hom.naturality (a.top.app x)).symm)

def rightDirectSquare (a : ArrowCore H K) (x : F.top) :
    (H.empty.map (F.cR.hom.app x) ≫ H.topEmpty.hom.app x) ≫ T.r0.map (a.top.app x) ≅
      a.empty.app ((F.rR.comp F.sR).obj x) ≫
        (K.empty.map (F.cR.hom.app x) ≫ K.topEmpty.hom.app x) :=
  pasteSquare (a.empty.naturality (F.cR.hom.app x)) (appIso a.topEmpty x)

def rightPastedSquare (a : ArrowCore H K) (x : F.top) :
    (H.rightEmpty.hom.app (F.rR.obj x) ≫ T.sR.map (H.topRight.hom.app x) ≫
      T.cR.hom.app (H.top.obj x)) ≫ T.r0.map (a.top.app x) ≅
      a.empty.app ((F.rR.comp F.sR).obj x) ≫
        (K.rightEmpty.hom.app (F.rR.obj x) ≫ T.sR.map (K.topRight.hom.app x) ≫
          T.cR.hom.app (K.top.obj x)) :=
  pasteSquare (appIso a.rightEmpty (F.rR.obj x))
    (pasteSquare ((T.sR.mapComp _ _).symm ≪≫ T.sR.map₂Iso (appIso a.topRight x) ≪≫
      T.sR.mapComp _ _) (T.cR.hom.naturality (a.top.app x)).symm)

structure Arrow (H K : Map (F := F) (T := T)) extends ArrowCore H K where
  leftCoherence (x : F.top) :
    (leftChi H x).hom ▷ T.r0.map (top.app x) ≫ (leftPastedSquare toArrowCore x).hom =
      (leftDirectSquare toArrowCore x).hom ≫
        empty.app ((F.rL.comp F.sL).obj x) ◁ (leftChi K x).hom
  rightCoherence (x : F.top) :
    (rightChi H x).hom ▷ T.r0.map (top.app x) ≫ (rightPastedSquare toArrowCore x).hom =
      (rightDirectSquare toArrowCore x).hom ≫
        empty.app ((F.rR.comp F.sR).obj x) ◁ (rightChi K x).hom


structure Cell {H K : Map (F := F) (T := T)} (a b : Arrow H K) where
  top : a.top ⟶ b.top
  left : a.left ⟶ b.left
  right : a.right ⟶ b.right
  empty : a.empty ⟶ b.empty
  topLeft : a.topLeft.hom ≫ (preMod F.rL left ▷ K.topLeft.hom) =
    (H.topLeft.hom ◁ postMod T.rL top) ≫ b.topLeft.hom
  topRight : a.topRight.hom ≫ (preMod F.rR right ▷ K.topRight.hom) =
    (H.topRight.hom ◁ postMod T.rR top) ≫ b.topRight.hom
  topEmpty : a.topEmpty.hom ≫ (preMod F.r0 empty ▷ K.topEmpty.hom) =
    (H.topEmpty.hom ◁ postMod T.r0 top) ≫ b.topEmpty.hom
  leftEmpty : a.leftEmpty.hom ≫ (preMod F.sL empty ▷ K.leftEmpty.hom) =
    (H.leftEmpty.hom ◁ postMod T.sL left) ≫ b.leftEmpty.hom
  rightEmpty : a.rightEmpty.hom ≫ (preMod F.sR empty ▷ K.rightEmpty.hom) =
    (H.rightEmpty.hom ◁ postMod T.sR right) ≫ b.rightEmpty.hom

@[ext] theorem Cell.ext {a b : Arrow H K} {m n : Cell a b}
    (ht : m.top = n.top) (hl : m.left = n.left) (hr : m.right = n.right)
    (he : m.empty = n.empty) : m = n := by
  cases m; cases n; cases ht; cases hl; cases hr; cases he; rfl

def cellId (a : Arrow H K) : Cell a a where
  top := 𝟙 a.top
  left := 𝟙 a.left
  right := 𝟙 a.right
  empty := 𝟙 a.empty
  topLeft := by change a.topLeft.hom ≫ ((pre F.rL).map₂ (𝟙 a.left) ▷ _) =
      (_ ◁ (post T.rL).map₂ (𝟙 a.top)) ≫ _; simp; exact Category.comp_id _
  topRight := by change a.topRight.hom ≫ ((pre F.rR).map₂ (𝟙 a.right) ▷ _) =
      (_ ◁ (post T.rR).map₂ (𝟙 a.top)) ≫ _; simp; exact Category.comp_id _
  topEmpty := by change a.topEmpty.hom ≫ ((pre F.r0).map₂ (𝟙 a.empty) ▷ _) =
      (_ ◁ (post T.r0).map₂ (𝟙 a.top)) ≫ _; simp; exact Category.comp_id _
  leftEmpty := by change a.leftEmpty.hom ≫ ((pre F.sL).map₂ (𝟙 a.empty) ▷ _) =
      (_ ◁ (post T.sL).map₂ (𝟙 a.left)) ≫ _; simp; exact Category.comp_id _
  rightEmpty := by change a.rightEmpty.hom ≫ ((pre F.sR).map₂ (𝟙 a.empty) ▷ _) =
      (_ ◁ (post T.sR).map₂ (𝟙 a.right)) ≫ _; simp; exact Category.comp_id _

section
variable {C : Type*} [Category C]
theorem square_comp {a b c d e f : C} {q₁ : a ⟶ b} {q₂ : c ⟶ d} {q₃ : e ⟶ f}
    {x₁ : b ⟶ d} {x₂ : d ⟶ f} {y₁ : a ⟶ c} {y₂ : c ⟶ e}
    (h₁ : q₁ ≫ x₁ = y₁ ≫ q₂) (h₂ : q₂ ≫ x₂ = y₂ ≫ q₃) :
    q₁ ≫ (x₁ ≫ x₂) = (y₁ ≫ y₂) ≫ q₃ := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]
end

def cellComp {a b c : Arrow H K} (m : Cell a b) (n : Cell b c) : Cell a c where
  top := m.top ≫ n.top
  left := m.left ≫ n.left
  right := m.right ≫ n.right
  empty := m.empty ≫ n.empty
  topLeft := by
    change a.topLeft.hom ≫ ((pre F.rL).map₂ (m.left ≫ n.left) ▷ _) =
      (_ ◁ (post T.rL).map₂ (m.top ≫ n.top)) ≫ _
    simp only [PrelaxFunctor.map₂_comp, comp_whiskerRight, whiskerLeft_comp]
    exact square_comp m.topLeft n.topLeft
  topRight := by
    change a.topRight.hom ≫ ((pre F.rR).map₂ (m.right ≫ n.right) ▷ _) =
      (_ ◁ (post T.rR).map₂ (m.top ≫ n.top)) ≫ _
    simp only [PrelaxFunctor.map₂_comp, comp_whiskerRight, whiskerLeft_comp]
    exact square_comp m.topRight n.topRight
  topEmpty := by
    change a.topEmpty.hom ≫ ((pre F.r0).map₂ (m.empty ≫ n.empty) ▷ _) =
      (_ ◁ (post T.r0).map₂ (m.top ≫ n.top)) ≫ _
    simp only [PrelaxFunctor.map₂_comp, comp_whiskerRight, whiskerLeft_comp]
    exact square_comp m.topEmpty n.topEmpty
  leftEmpty := by
    change a.leftEmpty.hom ≫ ((pre F.sL).map₂ (m.empty ≫ n.empty) ▷ _) =
      (_ ◁ (post T.sL).map₂ (m.left ≫ n.left)) ≫ _
    simp only [PrelaxFunctor.map₂_comp, comp_whiskerRight, whiskerLeft_comp]
    exact square_comp m.leftEmpty n.leftEmpty
  rightEmpty := by
    change a.rightEmpty.hom ≫ ((pre F.sR).map₂ (m.empty ≫ n.empty) ▷ _) =
      (_ ◁ (post T.sR).map₂ (m.right ≫ n.right)) ≫ _
    simp only [PrelaxFunctor.map₂_comp, comp_whiskerRight, whiskerLeft_comp]
    exact square_comp m.rightEmpty n.rightEmpty

instance homCategory (H K : Map (F := F) (T := T)) : Category (Arrow H K) where
  Hom := Cell
  id := cellId
  comp := cellComp
  id_comp _ := Cell.ext (Category.id_comp _) (Category.id_comp _) (Category.id_comp _) (Category.id_comp _)
  comp_id _ := Cell.ext (Category.comp_id _) (Category.comp_id _) (Category.comp_id _) (Category.comp_id _)
  assoc _ _ _ := Cell.ext (Category.assoc _ _ _) (Category.assoc _ _ _)
    (Category.assoc _ _ _) (Category.assoc _ _ _)


def identitySquare {X Y : Type*} [Bicategory X] [Bicategory Y]
    {Z : Type*} [Bicategory Z] (L : Pseudofunctor X Z) (R : Pseudofunctor Y Z)
    {x : X} {y : Y} (p : L.obj x ⟶ R.obj y) :
    p ≫ R.map (𝟙 y) ≅ L.map (𝟙 x) ≫ p :=
  whiskerLeftIso p (R.mapId y) ≪≫ ρ_ p ≪≫ (λ_ p).symm ≪≫
    whiskerRightIso (L.mapId x).symm p

def arrowCoreId (H : Map (F := F) (T := T)) : ArrowCore H H where
  top := 𝟙 H.top
  left := 𝟙 H.left
  right := 𝟙 H.right
  empty := 𝟙 H.empty
  topLeft := identitySquare (pre F.rL) (post T.rL) H.topLeft.hom
  topRight := identitySquare (pre F.rR) (post T.rR) H.topRight.hom
  topEmpty := identitySquare (pre F.r0) (post T.r0) H.topEmpty.hom
  leftEmpty := identitySquare (pre F.sL) (post T.sL) H.leftEmpty.hom
  rightEmpty := identitySquare (pre F.sR) (post T.sR) H.rightEmpty.hom

def arrowId (H : Map (F := F) (T := T)) : Arrow H H where
  toArrowCore := arrowCoreId H
  leftCoherence x := by
    dsimp [leftDirectSquare, leftPastedSquare, pasteSquare, appIso, arrowCoreId,
      identitySquare, post, postId, pre]
    simp [Category.assoc, preTrans, Pseudofunctor.StrongTrans.naturality_id_inv, Pseudofunctor.comp, PrelaxFunctor.map₂_iso_inv, ← inv_whiskerLeft, ← inv_whiskerRight]
    simp only [← whiskerLeft_comp_assoc, ← comp_whiskerLeft_assoc]
    simp only [← comp_whiskerLeft]
    simp only [← comp_whiskerLeft_assoc]
    rw [← whisker_exchange_assoc]
    simp
  rightCoherence x := by
    dsimp [rightDirectSquare, rightPastedSquare, pasteSquare, appIso, arrowCoreId,
      identitySquare, post, postId, pre]
    simp [Category.assoc, preTrans, Pseudofunctor.StrongTrans.naturality_id_inv, Pseudofunctor.comp, PrelaxFunctor.map₂_iso_inv, ← inv_whiskerLeft, ← inv_whiskerRight]
    simp only [← whiskerLeft_comp_assoc, ← comp_whiskerLeft_assoc]
    simp only [← comp_whiskerLeft]
    simp only [← comp_whiskerLeft_assoc]
    rw [← whisker_exchange_assoc]
    simp

end SquareKit.FiniteHigherCell

namespace SquareKit.FiniteHigherCell
open CategoryTheory Bicategory SquareKit.HigherCategory SquareKit.FiniteHigherMap
open SquareKit.PseudofunctorMapping SquareKit.PseudofunctorPostcomposition SquareKit.PseudofunctorComposition
open scoped Pseudofunctor.StrongTrans
universe u v w u' v' w'
variable {F : FullDiagram.{u,v,w}} {T : FullDiagram.{u',v',w'}}

/-- Compose squares along the component transformations. -/
def composeSquare {X Y : Type*} [Bicategory X] [Bicategory Y]
    {Z : Type*} [Bicategory Z] (L : Pseudofunctor X Z) (R : Pseudofunctor Y Z)
    {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
    {p₀ : L.obj x₀ ⟶ R.obj y₀} {p₁ : L.obj x₁ ⟶ R.obj y₁}
    {p₂ : L.obj x₂ ⟶ R.obj y₂}
    {a : x₀ ⟶ x₁} {b : x₁ ⟶ x₂} {c : y₀ ⟶ y₁} {d : y₁ ⟶ y₂}
    (q₁ : p₀ ≫ R.map c ≅ L.map a ≫ p₁)
    (q₂ : p₁ ≫ R.map d ≅ L.map b ≫ p₂) :
    p₀ ≫ R.map (c ≫ d) ≅ L.map (a ≫ b) ≫ p₂ :=
  whiskerLeftIso p₀ (R.mapComp c d) ≪≫ (α_ _ _ _).symm ≪≫
    whiskerRightIso q₁ _ ≪≫ (α_ _ _ _) ≪≫ whiskerLeftIso _ q₂ ≪≫
    (α_ _ _ _).symm ≪≫ whiskerRightIso (L.mapComp a b).symm p₂

def arrowCoreComp {H K J : Map (F := F) (T := T)}
    (a : ArrowCore H K) (b : ArrowCore K J) : ArrowCore H J where
  top := a.top ≫ b.top
  left := a.left ≫ b.left
  right := a.right ≫ b.right
  empty := a.empty ≫ b.empty
  topLeft := composeSquare (pre F.rL) (post T.rL) a.topLeft b.topLeft
  topRight := composeSquare (pre F.rR) (post T.rR) a.topRight b.topRight
  topEmpty := composeSquare (pre F.r0) (post T.r0) a.topEmpty b.topEmpty
  leftEmpty := composeSquare (pre F.sL) (post T.sL) a.leftEmpty b.leftEmpty
  rightEmpty := composeSquare (pre F.sR) (post T.sR) a.rightEmpty b.rightEmpty

end SquareKit.FiniteHigherCell

namespace SquareKit.FiniteHigherCell
open CategoryTheory Bicategory
universe u v w
variable {B : Type u} [Bicategory.{w,v} B]

def stackSquare {a₀ a₁ b₀ b₁ c₀ c₁ : B}
    {h : a₀ ⟶ a₁} {k : b₀ ⟶ b₁} {l : c₀ ⟶ c₁}
    {u : a₀ ⟶ b₀} {v : a₁ ⟶ b₁} {s : b₀ ⟶ c₀} {t : b₁ ⟶ c₁}
    (q : h ≫ v ≅ u ≫ k) (r : k ≫ t ≅ s ≫ l) :
    h ≫ (v ≫ t) ≅ (u ≫ s) ≫ l :=
  (α_ _ _ _).symm ≪≫ whiskerRightIso q _ ≪≫ α_ _ _ _ ≪≫
    whiskerLeftIso _ r ≪≫ (α_ _ _ _).symm

theorem pasteSquare_stackSquare {a₀ a₁ a₂ b₀ b₁ b₂ c₀ c₁ c₂ : B}
    {h₀ : a₀ ⟶ a₁} {h₁ : a₁ ⟶ a₂}
    {k₀ : b₀ ⟶ b₁} {k₁ : b₁ ⟶ b₂}
    {l₀ : c₀ ⟶ c₁} {l₁ : c₁ ⟶ c₂}
    {u₀ : a₀ ⟶ b₀} {u₁ : a₁ ⟶ b₁} {u₂ : a₂ ⟶ b₂}
    {v₀ : b₀ ⟶ c₀} {v₁ : b₁ ⟶ c₁} {v₂ : b₂ ⟶ c₂}
    (q₀ : h₀ ≫ u₁ ≅ u₀ ≫ k₀) (q₁ : h₁ ≫ u₂ ≅ u₁ ≫ k₁)
    (r₀ : k₀ ≫ v₁ ≅ v₀ ≫ l₀) (r₁ : k₁ ≫ v₂ ≅ v₁ ≫ l₁) :
    stackSquare (pasteSquare q₀ q₁) (pasteSquare r₀ r₁) =
      pasteSquare (stackSquare q₀ r₀) (stackSquare q₁ r₁) := by
  apply Iso.ext
  dsimp [stackSquare, pasteSquare]
  let pastePrefix :=
    (α_ (h₀ ≫ h₁) u₂ v₂).inv ≫ (α_ h₀ h₁ u₂).hom ▷ v₂ ≫
      (α_ h₀ (h₁ ≫ u₂) v₂).hom ≫ h₀ ◁ q₁.hom ▷ v₂ ≫
      h₀ ◁ (α_ u₁ k₁ v₂).hom ≫ (α_ h₀ u₁ (k₁ ≫ v₂)).inv
  let pasteSuffix :=
    (α_ u₀ k₀ (v₁ ≫ l₁)).hom ≫ u₀ ◁ (α_ k₀ v₁ l₁).inv ≫
      u₀ ◁ r₀.hom ▷ l₁ ≫ u₀ ◁ (α_ v₀ l₀ l₁).hom ≫
      (α_ u₀ v₀ (l₀ ≫ l₁)).inv
  calc
    _ = pastePrefix ≫ (q₀.hom ▷ (k₁ ≫ v₂) ≫ (u₀ ≫ k₀) ◁ r₁.hom) ≫ pasteSuffix := by
      dsimp [pastePrefix, pasteSuffix]
      bicategory
    _ = pastePrefix ≫ ((h₀ ≫ u₁) ◁ r₁.hom ≫ q₀.hom ▷ (v₁ ≫ l₁)) ≫ pasteSuffix := by
      rw [← whisker_exchange]
    _ = _ := by
      dsimp [pastePrefix, pasteSuffix]
      bicategory
end SquareKit.FiniteHigherCell

namespace SquareKit.FiniteHigherCell
open CategoryTheory Bicategory
universe u v w
variable {B : Type u} [Bicategory.{w,v} B]

theorem stackSquare_coherence {a₀ a₁ b₀ b₁ c₀ c₁ : B}
    {d₀ p₀ : a₀ ⟶ a₁} {d₁ p₁ : b₀ ⟶ b₁} {d₂ p₂ : c₀ ⟶ c₁}
    {u : a₀ ⟶ b₀} {v : a₁ ⟶ b₁} {s : b₀ ⟶ c₀} {t : b₁ ⟶ c₁}
    (χ₀ : d₀ ⟶ p₀) (χ₁ : d₁ ⟶ p₁) (χ₂ : d₂ ⟶ p₂)
    (qd : d₀ ≫ v ≅ u ≫ d₁) (qp : p₀ ≫ v ≅ u ≫ p₁)
    (rd : d₁ ≫ t ≅ s ≫ d₂) (rp : p₁ ≫ t ≅ s ≫ p₂)
    (h : χ₀ ▷ v ≫ qp.hom = qd.hom ≫ u ◁ χ₁)
    (k : χ₁ ▷ t ≫ rp.hom = rd.hom ≫ s ◁ χ₂) :
    χ₀ ▷ (v ≫ t) ≫ (stackSquare qp rp).hom =
      (stackSquare qd rd).hom ≫ (u ≫ s) ◁ χ₂ := by
  dsimp [stackSquare]
  simp only [comp_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc]
  rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc, h,
    comp_whiskerRight_assoc, associator_naturality_middle_assoc,
    ← whiskerLeft_comp_assoc, k, whiskerLeft_comp_assoc]
end SquareKit.FiniteHigherCell

namespace SquareKit.FiniteHigherCell
open CategoryTheory Bicategory
universe u v w u' v' w'
variable {B : Type u} [Bicategory.{w,v} B] {C : Type u'} [Bicategory.{w',v'} C]

def mapSquare (S : Pseudofunctor B C) {a₀ a₁ b₀ b₁ : B}
    {h : a₀ ⟶ a₁} {k : b₀ ⟶ b₁} {u : a₀ ⟶ b₀} {v : a₁ ⟶ b₁}
    (q : h ≫ v ≅ u ≫ k) : S.map h ≫ S.map v ≅ S.map u ≫ S.map k :=
  (S.mapComp h v).symm ≪≫ S.map₂Iso q ≪≫ S.mapComp u k

theorem mapSquare_stackSquare (S : Pseudofunctor B C) {a₀ a₁ b₀ b₁ c₀ c₁ : B}
    {h : a₀ ⟶ a₁} {k : b₀ ⟶ b₁} {l : c₀ ⟶ c₁}
    {u : a₀ ⟶ b₀} {v : a₁ ⟶ b₁} {s : b₀ ⟶ c₀} {t : b₁ ⟶ c₁}
    (q : h ≫ v ≅ u ≫ k) (r : k ≫ t ≅ s ≫ l) :
    mapSquare S (stackSquare q r) =
      whiskerLeftIso (S.map h) (S.mapComp v t) ≪≫
        stackSquare (mapSquare S q) (mapSquare S r) ≪≫
          whiskerRightIso (S.mapComp u s).symm (S.map l) := by
  apply Iso.ext
  dsimp [mapSquare, stackSquare]
  simp [S.map₂_iso_inv, Category.assoc, -inv_whiskerLeft]
  simp only [inv_whiskerLeft, IsIso.Iso.inv_inv]
end SquareKit.FiniteHigherCell

namespace SquareKit.FiniteHigherCell
open CategoryTheory Bicategory
universe u v w u' v' w'
variable {B : Type u} [Bicategory.{w,v} B] {C : Type u'} [Bicategory.{w',v'} C]

def adjustSquare {a₀ a₁ b₀ b₁ : B} {h : a₀ ⟶ a₁} {k : b₀ ⟶ b₁}
    {u u' : a₀ ⟶ b₀} {v v' : a₁ ⟶ b₁}
    (q : h ≫ v ≅ u ≫ k) (l : u' ≅ u) (r : v' ≅ v) : h ≫ v' ≅ u' ≫ k :=
  whiskerLeftIso h r ≪≫ q ≪≫ whiskerRightIso l.symm k

theorem adjustSquare_trans {a₀ a₁ b₀ b₁ : B} {h : a₀ ⟶ a₁} {k : b₀ ⟶ b₁}
    {u u' u'' : a₀ ⟶ b₀} {v v' v'' : a₁ ⟶ b₁}
    (q : h ≫ v ≅ u ≫ k) (l : u' ≅ u) (r : v' ≅ v)
    (l' : u'' ≅ u') (r' : v'' ≅ v') :
    adjustSquare (adjustSquare q l r) l' r' = adjustSquare q (l' ≪≫ l) (r' ≪≫ r) := by
  apply Iso.ext
  simp [adjustSquare, Category.assoc]

theorem pasteSquare_adjustSquare {a₀ a₁ a₂ b₀ b₁ b₂ : B}
    {h₁ : a₀ ⟶ a₁} {h₂ : a₁ ⟶ a₂} {k₁ : b₀ ⟶ b₁} {k₂ : b₁ ⟶ b₂}
    {u u' : a₀ ⟶ b₀} {v v' : a₁ ⟶ b₁} {w w' : a₂ ⟶ b₂}
    (q₁ : h₁ ≫ v ≅ u ≫ k₁) (q₂ : h₂ ≫ w ≅ v ≫ k₂)
    (l : u' ≅ u) (m : v' ≅ v) (r : w' ≅ w) :
    pasteSquare (adjustSquare q₁ l m) (adjustSquare q₂ m r) =
      adjustSquare (pasteSquare q₁ q₂) l r := by
  apply Iso.ext
  dsimp [adjustSquare, pasteSquare]
  simp [Category.assoc]

theorem mapSquare_adjustSquare (S : Pseudofunctor B C)
    {a₀ a₁ b₀ b₁ : B} {h : a₀ ⟶ a₁} {k : b₀ ⟶ b₁}
    {u u' : a₀ ⟶ b₀} {v v' : a₁ ⟶ b₁}
    (q : h ≫ v ≅ u ≫ k) (l : u' ≅ u) (r : v' ≅ v) :
    mapSquare S (adjustSquare q l r) =
      adjustSquare (mapSquare S q) (S.map₂Iso l) (S.map₂Iso r) := by
  apply Iso.ext
  dsimp [mapSquare, adjustSquare]
  simp [S.map₂_iso_inv, Category.assoc]
end SquareKit.FiniteHigherCell

namespace SquareKit.FiniteHigherCell
open CategoryTheory Bicategory SquareKit.HigherCategory SquareKit.FiniteHigherMap
open SquareKit.PseudofunctorMapping SquareKit.PseudofunctorPostcomposition SquareKit.PseudofunctorComposition
open scoped Pseudofunctor.StrongTrans
universe u v w u' v' w'
variable {F : FullDiagram.{u,v,w}} {T : FullDiagram.{u',v',w'}}
variable {H K J : Map (F := F) (T := T)}

theorem leftEmpty_comp (a : ArrowCore H K) (b : ArrowCore K J) (x : F.left) :
    appIso (arrowCoreComp a b).leftEmpty x =
      adjustSquare (stackSquare (appIso a.leftEmpty x) (appIso b.leftEmpty x))
        (Iso.refl _) (T.sL.mapComp (a.left.app x) (b.left.app x)) := by
  apply Iso.ext
  simp [appIso, arrowCoreComp, composeSquare, pre, post, postComp, adjustSquare,
    stackSquare, preTrans, Category.assoc]

theorem topLeft_comp (a : ArrowCore H K) (b : ArrowCore K J) (x : F.top) :
    appIso (arrowCoreComp a b).topLeft x =
      adjustSquare (stackSquare (appIso a.topLeft x) (appIso b.topLeft x))
        (Iso.refl _) (T.rL.mapComp (a.top.app x) (b.top.app x)) := by
  apply Iso.ext
  simp [appIso, arrowCoreComp, composeSquare, pre, post, postComp, adjustSquare,
    stackSquare, preTrans, Category.assoc]

variable {A : Type u} [Bicategory.{w,v} A] {B : Type u'} [Bicategory.{w',v'} B]
theorem naturality_symm_comp {P Q : Pseudofunctor A B} (c : P ⟶ Q)
    {x y z : A} (f : x ⟶ y) (g : y ⟶ z) :
    (c.naturality (f ≫ g)).symm =
      adjustSquare (stackSquare (c.naturality f).symm (c.naturality g).symm)
        (P.mapComp f g) (Q.mapComp f g) := by
  apply Iso.ext
  simp [adjustSquare, stackSquare, c.naturality_comp_inv]

end SquareKit.FiniteHigherCell

namespace SquareKit.FiniteHigherCell
open CategoryTheory Bicategory SquareKit.HigherCategory SquareKit.FiniteHigherMap
open SquareKit.PseudofunctorMapping SquareKit.PseudofunctorPostcomposition SquareKit.PseudofunctorComposition
open scoped Pseudofunctor.StrongTrans
universe u v w u' v' w'
variable {F : FullDiagram.{u,v,w}} {T : FullDiagram.{u',v',w'}}
variable {H K J : Map (F := F) (T := T)}

theorem leftDirectSquare_comp (a : ArrowCore H K) (b : ArrowCore K J) (x : F.top) :
    leftDirectSquare (arrowCoreComp a b) x =
      whiskerLeftIso (H.empty.map (F.cL.hom.app x) ≫ H.topEmpty.hom.app x)
        (T.r0.mapComp (a.top.app x) (b.top.app x)) ≪≫
      stackSquare (leftDirectSquare a x) (leftDirectSquare b x) := by
  calc
    _ = whiskerLeftIso (H.empty.map (F.cL.hom.app x) ≫ H.topEmpty.hom.app x)
          (T.r0.mapComp (a.top.app x) (b.top.app x)) ≪≫
        pasteSquare (stackSquare (a.empty.naturality (F.cL.hom.app x))
          (b.empty.naturality (F.cL.hom.app x)))
          (stackSquare (appIso a.topEmpty x) (appIso b.topEmpty x)) := by
      apply Iso.ext
      dsimp [leftDirectSquare, arrowCoreComp, composeSquare, appIso, stackSquare, pasteSquare,
        pre, post, postComp]
      simp [Category.assoc, preTrans]
      bicategory
    _ = _ := by
      rw [← pasteSquare_stackSquare]
      rfl
end SquareKit.FiniteHigherCell

namespace SquareKit.FiniteHigherCell
open CategoryTheory Bicategory SquareKit.HigherCategory SquareKit.FiniteHigherMap
open SquareKit.PseudofunctorMapping SquareKit.PseudofunctorPostcomposition SquareKit.PseudofunctorComposition
open scoped Pseudofunctor.StrongTrans
universe u v w u' v' w'
variable {F : FullDiagram.{u,v,w}} {T : FullDiagram.{u',v',w'}}
variable {H K J : Map (F := F) (T := T)}

theorem map₂Iso_refl {A : Type u} [Bicategory.{w,v} A]
    {B : Type u'} [Bicategory.{w',v'} B] (S : Pseudofunctor A B)
    {a b : A} (f : a ⟶ b) : S.map₂Iso (Iso.refl f) = Iso.refl (S.map f) := by
  apply Iso.ext
  exact S.map₂_id f

theorem leftPastedSquare_comp (a : ArrowCore H K) (b : ArrowCore K J) (x : F.top) :
    leftPastedSquare (arrowCoreComp a b) x =
      whiskerLeftIso (H.leftEmpty.hom.app (F.rL.obj x) ≫
        T.sL.map (H.topLeft.hom.app x) ≫ T.cL.hom.app (H.top.obj x))
        (T.r0.mapComp (a.top.app x) (b.top.app x)) ≪≫
      stackSquare (leftPastedSquare a x) (leftPastedSquare b x) := by
  change pasteSquare (appIso (arrowCoreComp a b).leftEmpty (F.rL.obj x))
    (pasteSquare (mapSquare T.sL (appIso (arrowCoreComp a b).topLeft x))
      (T.cL.hom.naturality (a.top.app x ≫ b.top.app x)).symm) = _
  rw [leftEmpty_comp, topLeft_comp, mapSquare_adjustSquare]
  have hm := mapSquare_stackSquare T.sL (appIso a.topLeft x) (appIso b.topLeft x)
  change mapSquare T.sL (stackSquare (appIso a.topLeft x) (appIso b.topLeft x)) =
    adjustSquare (stackSquare (mapSquare T.sL (appIso a.topLeft x))
      (mapSquare T.sL (appIso b.topLeft x)))
      (T.sL.mapComp (a.left.app (F.rL.obj x)) (b.left.app (F.rL.obj x)))
      (T.sL.mapComp (T.rL.map (a.top.app x)) (T.rL.map (b.top.app x))) at hm
  rw [hm, adjustSquare_trans, naturality_symm_comp]
  erw [map₂Iso_refl, Iso.refl_trans]
  change pasteSquare (adjustSquare _ (Iso.refl _) (T.sL.mapComp _ _))
    (pasteSquare (adjustSquare _ (T.sL.mapComp _ _) ((T.rL.comp T.sL).mapComp _ _))
      (adjustSquare _ ((T.rL.comp T.sL).mapComp _ _) (T.r0.mapComp _ _))) = _
  rw [pasteSquare_adjustSquare, pasteSquare_adjustSquare,
    ← pasteSquare_stackSquare, ← pasteSquare_stackSquare]
  apply Iso.ext
  simp [adjustSquare]
  rfl
end SquareKit.FiniteHigherCell

namespace SquareKit.FiniteHigherCell
open CategoryTheory Bicategory SquareKit.HigherCategory SquareKit.FiniteHigherMap
open scoped Pseudofunctor.StrongTrans
universe u v w u' v' w'
variable {F : FullDiagram.{u,v,w}} {T : FullDiagram.{u',v',w'}}

/-- Cancelling the normalization recovers the original chain modification. -/
theorem leftCoherence_ext (H : Map (F := F) (T := T))
    {c d : leftDirect H.toMapCore ≅ leftPasted H.toMapCore}
    (h : ∀ x, appIso c x ≪≫ leftPastedAppIso H x =
      appIso d x ≪≫ leftPastedAppIso H x) : c = d := by
  apply Iso.ext
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro x
  have hx := congrArg Iso.hom (h x)
  exact (cancel_mono (leftPastedAppIso H x).hom).mp hx

theorem rightCoherence_ext (H : Map (F := F) (T := T))
    {c d : rightDirect H.toMapCore ≅ rightPasted H.toMapCore}
    (h : ∀ x, appIso c x ≪≫ rightPastedAppIso H x =
      appIso d x ≪≫ rightPastedAppIso H x) : c = d := by
  apply Iso.ext
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro x
  have hx := congrArg Iso.hom (h x)
  exact (cancel_mono (rightPastedAppIso H x).hom).mp hx

end SquareKit.FiniteHigherCell

namespace SquareKit.FiniteHigherCell
open CategoryTheory Bicategory
universe u v w
variable {B : Type u} [Bicategory.{w,v} B]

theorem stackSquare_coherence_boundary {a₀ a₁ b₀ b₁ c₀ c₁ : B}
    {d₀ p₀ : a₀ ⟶ a₁} {d₁ p₁ : b₀ ⟶ b₁} {d₂ p₂ : c₀ ⟶ c₁}
    {u : a₀ ⟶ b₀} {v : a₁ ⟶ b₁} {s : b₀ ⟶ c₀} {t : b₁ ⟶ c₁}
    {w : a₁ ⟶ c₁} (e : w ≅ v ≫ t)
    (χ₀ : d₀ ⟶ p₀) (χ₁ : d₁ ⟶ p₁) (χ₂ : d₂ ⟶ p₂)
    (qd : d₀ ≫ v ≅ u ≫ d₁) (qp : p₀ ≫ v ≅ u ≫ p₁)
    (rd : d₁ ≫ t ≅ s ≫ d₂) (rp : p₁ ≫ t ≅ s ≫ p₂)
    (h : χ₀ ▷ v ≫ qp.hom = qd.hom ≫ u ◁ χ₁)
    (k : χ₁ ▷ t ≫ rp.hom = rd.hom ≫ s ◁ χ₂) :
    χ₀ ▷ w ≫ (whiskerLeftIso p₀ e ≪≫ stackSquare qp rp).hom =
      (whiskerLeftIso d₀ e ≪≫ stackSquare qd rd).hom ≫ (u ≫ s) ◁ χ₂ := by
  simp only [Iso.trans_hom, whiskerLeftIso_hom, Category.assoc]
  rw [← whisker_exchange_assoc, stackSquare_coherence χ₀ χ₁ χ₂ qd qp rd rp h k]

end SquareKit.FiniteHigherCell

namespace SquareKit.FiniteHigherCell
open CategoryTheory Bicategory SquareKit.HigherCategory SquareKit.FiniteHigherMap
open SquareKit.PseudofunctorMapping SquareKit.PseudofunctorPostcomposition SquareKit.PseudofunctorComposition
open scoped Pseudofunctor.StrongTrans
universe u v w u' v' w'
variable {F : FullDiagram.{u,v,w}} {T : FullDiagram.{u',v',w'}}
variable {H K J : Map (F := F) (T := T)}
theorem rightEmpty_comp (a : ArrowCore H K) (b : ArrowCore K J) (x : F.right) :
    appIso (arrowCoreComp a b).rightEmpty x =
      adjustSquare (stackSquare (appIso a.rightEmpty x) (appIso b.rightEmpty x))
        (Iso.refl _) (T.sR.mapComp (a.right.app x) (b.right.app x)) := by
  apply Iso.ext
  simp [appIso, arrowCoreComp, composeSquare, pre, post, postComp, adjustSquare,
    stackSquare, preTrans, Category.assoc]

theorem topRight_comp (a : ArrowCore H K) (b : ArrowCore K J) (x : F.top) :
    appIso (arrowCoreComp a b).topRight x =
      adjustSquare (stackSquare (appIso a.topRight x) (appIso b.topRight x))
        (Iso.refl _) (T.rR.mapComp (a.top.app x) (b.top.app x)) := by
  apply Iso.ext
  simp [appIso, arrowCoreComp, composeSquare, pre, post, postComp, adjustSquare,
    stackSquare, preTrans, Category.assoc]

theorem rightDirectSquare_comp (a : ArrowCore H K) (b : ArrowCore K J) (x : F.top) :
    rightDirectSquare (arrowCoreComp a b) x =
      whiskerLeftIso (H.empty.map (F.cR.hom.app x) ≫ H.topEmpty.hom.app x)
        (T.r0.mapComp (a.top.app x) (b.top.app x)) ≪≫
      stackSquare (rightDirectSquare a x) (rightDirectSquare b x) := by
  calc
    _ = whiskerLeftIso (H.empty.map (F.cR.hom.app x) ≫ H.topEmpty.hom.app x)
          (T.r0.mapComp (a.top.app x) (b.top.app x)) ≪≫
        pasteSquare (stackSquare (a.empty.naturality (F.cR.hom.app x))
          (b.empty.naturality (F.cR.hom.app x)))
          (stackSquare (appIso a.topEmpty x) (appIso b.topEmpty x)) := by
      apply Iso.ext
      dsimp [rightDirectSquare, arrowCoreComp, composeSquare, appIso, stackSquare, pasteSquare,
        pre, post, postComp]
      simp [Category.assoc, preTrans]
      bicategory
    _ = _ := by
      rw [← pasteSquare_stackSquare]
      rfl
theorem rightPastedSquare_comp (a : ArrowCore H K) (b : ArrowCore K J) (x : F.top) :
    rightPastedSquare (arrowCoreComp a b) x =
      whiskerLeftIso (H.rightEmpty.hom.app (F.rR.obj x) ≫
        T.sR.map (H.topRight.hom.app x) ≫ T.cR.hom.app (H.top.obj x))
        (T.r0.mapComp (a.top.app x) (b.top.app x)) ≪≫
      stackSquare (rightPastedSquare a x) (rightPastedSquare b x) := by
  change pasteSquare (appIso (arrowCoreComp a b).rightEmpty (F.rR.obj x))
    (pasteSquare (mapSquare T.sR (appIso (arrowCoreComp a b).topRight x))
      (T.cR.hom.naturality (a.top.app x ≫ b.top.app x)).symm) = _
  rw [rightEmpty_comp, topRight_comp, mapSquare_adjustSquare]
  have hm := mapSquare_stackSquare T.sR (appIso a.topRight x) (appIso b.topRight x)
  change mapSquare T.sR (stackSquare (appIso a.topRight x) (appIso b.topRight x)) =
    adjustSquare (stackSquare (mapSquare T.sR (appIso a.topRight x))
      (mapSquare T.sR (appIso b.topRight x)))
      (T.sR.mapComp (a.right.app (F.rR.obj x)) (b.right.app (F.rR.obj x)))
      (T.sR.mapComp (T.rR.map (a.top.app x)) (T.rR.map (b.top.app x))) at hm
  rw [hm, adjustSquare_trans, naturality_symm_comp]
  erw [map₂Iso_refl, Iso.refl_trans]
  change pasteSquare (adjustSquare _ (Iso.refl _) (T.sR.mapComp _ _))
    (pasteSquare (adjustSquare _ (T.sR.mapComp _ _) ((T.rR.comp T.sR).mapComp _ _))
      (adjustSquare _ ((T.rR.comp T.sR).mapComp _ _) (T.r0.mapComp _ _))) = _
  rw [pasteSquare_adjustSquare, pasteSquare_adjustSquare,
    ← pasteSquare_stackSquare, ← pasteSquare_stackSquare]
  apply Iso.ext
  simp [adjustSquare]
  rfl

end SquareKit.FiniteHigherCell

namespace SquareKit.FiniteHigherCell
open CategoryTheory Bicategory SquareKit.HigherCategory SquareKit.FiniteHigherMap
open SquareKit.PseudofunctorMapping SquareKit.PseudofunctorPostcomposition SquareKit.PseudofunctorComposition
open scoped Pseudofunctor.StrongTrans
universe u v w u' v' w'
variable {F : FullDiagram.{u,v,w}} {T : FullDiagram.{u',v',w'}}
variable {H K J : Map (F := F) (T := T)}

def arrowComp (a : Arrow H K) (b : Arrow K J) : Arrow H J where
  toArrowCore := arrowCoreComp a.toArrowCore b.toArrowCore
  leftCoherence x := by
    change (leftChi H x).hom ▷ T.r0.map (a.top.app x ≫ b.top.app x) ≫
      (leftPastedSquare (arrowCoreComp a.toArrowCore b.toArrowCore) x).hom =
      (leftDirectSquare (arrowCoreComp a.toArrowCore b.toArrowCore) x).hom ≫
        (a.empty.app ((F.rL.comp F.sL).obj x) ≫ b.empty.app ((F.rL.comp F.sL).obj x)) ◁
          (leftChi J x).hom
    rw [leftPastedSquare_comp, leftDirectSquare_comp]
    exact stackSquare_coherence_boundary (T.r0.mapComp _ _) (leftChi H x).hom
      (leftChi K x).hom (leftChi J x).hom _ _ _ _ (a.leftCoherence x) (b.leftCoherence x)
  rightCoherence x := by
    change (rightChi H x).hom ▷ T.r0.map (a.top.app x ≫ b.top.app x) ≫
      (rightPastedSquare (arrowCoreComp a.toArrowCore b.toArrowCore) x).hom =
      (rightDirectSquare (arrowCoreComp a.toArrowCore b.toArrowCore) x).hom ≫
        (a.empty.app ((F.rR.comp F.sR).obj x) ≫ b.empty.app ((F.rR.comp F.sR).obj x)) ◁
          (rightChi J x).hom
    rw [rightPastedSquare_comp, rightDirectSquare_comp]
    exact stackSquare_coherence_boundary (T.r0.mapComp _ _) (rightChi H x).hom
      (rightChi K x).hom (rightChi J x).hom _ _ _ _ (a.rightCoherence x) (b.rightCoherence x)

end SquareKit.FiniteHigherCell

end

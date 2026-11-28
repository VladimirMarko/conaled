import SquareKit.PseudofunctorMapping

/-! The iso-comma bicategory of two weak pseudofunctors, with projections and comparison transformation. -/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
namespace SquareKit.BicategoryIsoComma
open CategoryTheory Bicategory
universe u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃
variable {A : Type u₁} [Bicategory.{w₁,v₁} A]
  {B : Type u₂} [Bicategory.{w₂,v₂} B]
  {E : Type u₃} [Bicategory.{w₃,v₃} E]
  (L : Pseudofunctor A E) (R : Pseudofunctor B E)

structure Obj where
  left : A
  right : B
  overlap : Bicategory.Equivalence (L.obj left) (R.obj right)

variable {L R}
structure Arrow (x y : Obj L R) where
  left : x.left ⟶ y.left
  right : x.right ⟶ y.right
  square : L.map left ≫ y.overlap.hom ≅ x.overlap.hom ≫ R.map right

structure Cell {x y : Obj L R} (f g : Arrow x y) where
  left : f.left ⟶ g.left
  right : f.right ⟶ g.right
  compatibility : (L.map₂ left ▷ y.overlap.hom) ≫ g.square.hom =
    f.square.hom ≫ (x.overlap.hom ◁ R.map₂ right)

@[ext] theorem Cell.ext {x y : Obj L R} {f g : Arrow x y} {a b : Cell f g}
    (hl : a.left = b.left) (hr : a.right = b.right) : a = b := by
  cases a; cases b; cases hl; cases hr; rfl

def cellId {x y : Obj L R} (f : Arrow x y) : Cell f f where
  left := 𝟙 f.left
  right := 𝟙 f.right
  compatibility := by simp

def cellComp {x y : Obj L R} {f g h : Arrow x y} (a : Cell f g) (b : Cell g h) :
    Cell f h where
  left := a.left ≫ b.left
  right := a.right ≫ b.right
  compatibility := by
    simp only [PrelaxFunctor.map₂_comp, comp_whiskerRight, whiskerLeft_comp,
      Category.assoc]
    rw [b.compatibility, ← Category.assoc, a.compatibility, Category.assoc]

instance homCategory (x y : Obj L R) : Category (Arrow x y) where
  Hom := Cell
  id := cellId
  comp := cellComp
  id_comp _ := Cell.ext (Category.id_comp _) (Category.id_comp _)
  comp_id _ := Cell.ext (Category.comp_id _) (Category.comp_id _)
  assoc _ _ _ := Cell.ext (Category.assoc _ _ _) (Category.assoc _ _ _)

def arrowId (x : Obj L R) : Arrow x x where
  left := 𝟙 x.left
  right := 𝟙 x.right
  square := whiskerRightIso (L.mapId x.left) x.overlap.hom ≪≫
    λ_ x.overlap.hom ≪≫ (ρ_ x.overlap.hom).symm ≪≫
    whiskerLeftIso x.overlap.hom (R.mapId x.right).symm

def arrowComp {x y z : Obj L R} (f : Arrow x y) (g : Arrow y z) : Arrow x z where
  left := f.left ≫ g.left
  right := f.right ≫ g.right
  square := whiskerRightIso (L.mapComp f.left g.left) z.overlap.hom ≪≫
    α_ (L.map f.left) (L.map g.left) z.overlap.hom ≪≫
    whiskerLeftIso (L.map f.left) g.square ≪≫
    (α_ (L.map f.left) y.overlap.hom (R.map g.right)).symm ≪≫
    whiskerRightIso f.square (R.map g.right) ≪≫
    α_ x.overlap.hom (R.map f.right) (R.map g.right) ≪≫
    whiskerLeftIso x.overlap.hom (R.mapComp f.right g.right).symm

def cellWhiskerLeft {x y z : Obj L R} (f : Arrow x y) {g h : Arrow y z}
    (a : Cell g h) : Cell (arrowComp f g) (arrowComp f h) where
  left := f.left ◁ a.left
  right := f.right ◁ a.right
  compatibility := by
    simp only [arrowComp, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
      whiskerRightIso_hom]
    simp [Category.assoc]
    rw [← whiskerLeft_comp_assoc, a.compatibility, whiskerLeft_comp_assoc,
      associator_inv_naturality_right_assoc, whisker_exchange_assoc,
      associator_naturality_right_assoc]

def cellWhiskerRight {x y z : Obj L R} {f g : Arrow x y}
    (a : Cell f g) (h : Arrow y z) : Cell (arrowComp f h) (arrowComp g h) where
  left := a.left ▷ h.left
  right := a.right ▷ h.right
  compatibility := by
    simp only [arrowComp, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
      whiskerRightIso_hom]
    simp [Category.assoc]
    rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
      associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc,
      a.compatibility, comp_whiskerRight_assoc,
      associator_naturality_middle_assoc]

-- The projections retain all compatible cells; neither assumes E contractible.
def cellIso {x y : Obj L R} {f g : Arrow x y}
    (l : f.left ≅ g.left) (r : f.right ≅ g.right)
    (h : L.map₂ l.hom ▷ y.overlap.hom ≫ g.square.hom =
      f.square.hom ≫ x.overlap.hom ◁ R.map₂ r.hom) : f ≅ g where
  hom := ⟨l.hom, r.hom, h⟩
  inv := {
    left := l.inv
    right := r.inv
    compatibility := by
      have hl : L.map₂ l.inv ▷ y.overlap.hom ≫ L.map₂ l.hom ▷ y.overlap.hom = 𝟙 _ := by
        rw [← comp_whiskerRight, ← L.map₂_comp, l.inv_hom_id]
        simp
      have h' := congrArg (fun t => L.map₂ l.inv ▷ y.overlap.hom ≫ t ≫
        x.overlap.hom ◁ R.map₂ r.inv) h
      simp only [Category.assoc, ← whiskerLeft_comp, ← R.map₂_comp,
        r.hom_inv_id, R.map₂_id, whiskerLeft_id, Category.comp_id] at h'
      rw [← Category.assoc (L.map₂ l.inv ▷ y.overlap.hom), hl,
        Category.id_comp] at h'
      exact h'.symm }
  hom_inv_id := Cell.ext l.hom_inv_id r.hom_inv_id
  inv_hom_id := Cell.ext l.inv_hom_id r.inv_hom_id

def arrowLeftUnitor {x y : Obj L R} (f : Arrow x y) : arrowComp (arrowId x) f ≅ f :=
  cellIso (λ_ f.left) (λ_ f.right) (by
    simp [arrowComp, arrowId, Category.assoc]
    rw [associator_naturality_left_assoc, ← associator_inv_naturality_left_assoc]
    simp only [Iso.inv_hom_id_assoc, whisker_exchange_assoc]
    simp)

def arrowRightUnitor {x y : Obj L R} (f : Arrow x y) : arrowComp f (arrowId y) ≅ f :=
  cellIso (ρ_ f.left) (ρ_ f.right) (by
    simp [arrowComp, arrowId, Category.assoc]
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
      ← associator_naturality_right_assoc]
    simp)

def leftHomFunctor (x y : Obj L R) : Arrow x y ⥤ (x.left ⟶ y.left) where
  obj f := f.left
  map a := a.left

def arrowAssociator {x y z t : Obj L R} (f : Arrow x y) (g : Arrow y z)
    (h : Arrow z t) : arrowComp (arrowComp f g) h ≅ arrowComp f (arrowComp g h) :=
  cellIso (α_ f.left g.left h.left) (α_ f.right g.right h.right) (by
    simp [arrowComp, Category.assoc]
    rw [← associator_inv_naturality_left_assoc, whisker_exchange_assoc,
      ← associator_naturality_left_assoc]
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
      associator_naturality_right_assoc]
    bicategory)

def rightHomFunctor (x y : Obj L R) : Arrow x y ⥤ (x.right ⟶ y.right) where
  obj f := f.right
  map a := a.right

instance categoryStruct : CategoryStruct (Obj L R) where
  Hom := Arrow
  id := arrowId
  comp := arrowComp

instance bicategory : Bicategory (Obj L R) where
  homCategory := homCategory
  whiskerLeft := cellWhiskerLeft
  whiskerRight := cellWhiskerRight
  associator := arrowAssociator
  leftUnitor := arrowLeftUnitor
  rightUnitor := arrowRightUnitor
  whiskerLeft_id _ _ := Cell.ext (whiskerLeft_id _ _) (whiskerLeft_id _ _)
  whiskerLeft_comp := by intros; exact Cell.ext (whiskerLeft_comp _ _ _) (whiskerLeft_comp _ _ _)
  id_whiskerLeft _ := Cell.ext (id_whiskerLeft _) (id_whiskerLeft _)
  comp_whiskerLeft := by intros; exact Cell.ext (comp_whiskerLeft _ _ _) (comp_whiskerLeft _ _ _)
  id_whiskerRight _ _ := Cell.ext (id_whiskerRight _ _) (id_whiskerRight _ _)
  comp_whiskerRight _ _ _ := Cell.ext (comp_whiskerRight _ _ _) (comp_whiskerRight _ _ _)
  whiskerRight_id _ := Cell.ext (whiskerRight_id _) (whiskerRight_id _)
  whiskerRight_comp _ _ _ := Cell.ext (whiskerRight_comp _ _ _) (whiskerRight_comp _ _ _)
  whisker_assoc := by intros; exact Cell.ext (whisker_assoc _ _ _) (whisker_assoc _ _ _)
  whisker_exchange _ _ := Cell.ext (whisker_exchange _ _) (whisker_exchange _ _)
  pentagon _ _ _ _ := Cell.ext (pentagon _ _ _ _) (pentagon _ _ _ _)
  triangle _ _ := Cell.ext (triangle _ _) (triangle _ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def leftProjection : Pseudofunctor (Obj L R) A where
  obj x := x.left
  map f := f.left
  map₂ a := a.left
  mapId _ := Iso.refl _
  mapComp _ _ := Iso.refl _
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def rightProjection : Pseudofunctor (Obj L R) B where
  obj x := x.right
  map f := f.right
  map₂ a := a.right
  mapId _ := Iso.refl _
  mapComp _ _ := Iso.refl _
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def overlapTrans : Pseudofunctor.StrongTrans
    ((leftProjection : Pseudofunctor (Obj L R) A).comp L)
    ((rightProjection : Pseudofunctor (Obj L R) B).comp R) where
  app x := x.overlap.hom
  naturality f := f.square
  naturality_naturality a := a.compatibility
  naturality_id x := by
    change (arrowId x).square.hom ≫ x.overlap.hom ◁ (R.map₂ (𝟙 _) ≫ (R.mapId x.right).hom) =
      (L.map₂ (𝟙 _) ≫ (L.mapId x.left).hom) ▷ x.overlap.hom ≫
        (λ_ x.overlap.hom).hom ≫ (ρ_ x.overlap.hom).inv
    dsimp [arrowId]
    simp
  naturality_comp {x y z} f g := by
    change (arrowComp f g).square.hom ≫ x.overlap.hom ◁
      (R.map₂ (𝟙 (f.right ≫ g.right)) ≫ (R.mapComp f.right g.right).hom) =
      (L.map₂ (𝟙 (f.left ≫ g.left)) ≫ (L.mapComp f.left g.left).hom) ▷ z.overlap.hom ≫
      (α_ (L.map f.left) (L.map g.left) z.overlap.hom).hom ≫
      L.map f.left ◁ g.square.hom ≫ (α_ (L.map f.left) y.overlap.hom (R.map g.right)).inv ≫
      f.square.hom ▷ R.map g.right ≫ (α_ x.overlap.hom (R.map f.right) (R.map g.right)).hom
    dsimp [arrowComp]
    simp

theorem jointly_faithful {x y : Obj L R} {f g : x ⟶ y} (a b : f ⟶ g)
    (hl : (leftProjection : Pseudofunctor (Obj L R) A).map₂ a = leftProjection.map₂ b)
    (hr : (rightProjection : Pseudofunctor (Obj L R) B).map₂ a = rightProjection.map₂ b) :
    a = b := Cell.ext hl hr

instance [IsLocallyGroupoid A] [IsLocallyGroupoid B] : IsLocallyGroupoid (Obj L R) :=
  fun _ _ => {
    all_isIso := fun a => by
      let e := cellIso (asIso a.left) (asIso a.right) a.compatibility
      have h : e.hom = a := Cell.ext rfl rfl
      rw [← h]
      infer_instance }

def diagonalObj (x : E) : Obj (Pseudofunctor.id E) (Pseudofunctor.id E) :=
  ⟨x, x, Bicategory.Equivalence.id x⟩

def diagonalArrow {x y : E} (f : x ⟶ y) : diagonalObj x ⟶ diagonalObj y where
  left := f
  right := f
  square := ρ_ f ≪≫ (λ_ f).symm

def diagonalCell {x y : E} {f g : x ⟶ y} (a : f ⟶ g) :
    diagonalArrow f ⟶ diagonalArrow g where
  left := a
  right := a
  compatibility := by
    change a ▷ 𝟙 y ≫ ((ρ_ g).hom ≫ (λ_ g).inv) =
      ((ρ_ f).hom ≫ (λ_ f).inv) ≫ 𝟙 x ◁ a
    simp

theorem diagonalCell_injective {x y : E} {f g : x ⟶ y} :
    Function.Injective (diagonalCell (f := f) (g := g)) :=
  fun _ _ h => congrArg Cell.left h

open CategoryTheory.Prod
def productProjection : Pseudofunctor (Obj L R) (A × B) := by
  let F : Pseudofunctor (Obj L R) A := leftProjection
  let G : Pseudofunctor (Obj L R) B := rightProjection
  exact {
    obj := fun x => (F.obj x, G.obj x)
    map := fun f => F.map f ×ₘ G.map f
    map₂ := fun a => F.map₂ a ×ₘ G.map₂ a
    mapId := fun x => Iso.prod (F.mapId x) (G.mapId x)
    mapComp := fun f g => Iso.prod (F.mapComp f g) (G.mapComp f g)
    map₂_id := fun f => Prod.ext (F.map₂_id f) (G.map₂_id f)
    map₂_comp := fun a b => Prod.ext (F.map₂_comp a b) (G.map₂_comp a b)
    map₂_whisker_left := by intros; exact Prod.ext (F.map₂_whisker_left _ _) (G.map₂_whisker_left _ _)
    map₂_whisker_right := fun a f => Prod.ext (F.map₂_whisker_right a f) (G.map₂_whisker_right a f)
    map₂_associator := fun f g h => Prod.ext (F.map₂_associator f g h) (G.map₂_associator f g h)
    map₂_left_unitor := fun f => Prod.ext (F.map₂_left_unitor f) (G.map₂_left_unitor f)
    map₂_right_unitor := fun f => Prod.ext (F.map₂_right_unitor f) (G.map₂_right_unitor f) }

section ContractibleOverlap
variable [∀ (x y : E) (f g : x ⟶ y), Unique (f ⟶ g)]

def uniqueIso {x y : E} (f g : x ⟶ y) : f ≅ g where
  hom := default
  inv := default
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

theorem productProjection_local (x y : Obj L R) :
    ((productProjection (L := L) (R := R)).toPrelaxFunctor.mapFunctor x y).IsEquivalence where
  faithful := {
    map_injective := by
      intro a b m n h
      exact Cell.ext (congrArg Prod.fst h) (congrArg Prod.snd h) }
  full := {
    map_surjective := by
      intro a b m
      exact ⟨{ left := m.1, right := m.2, compatibility := Subsingleton.elim _ _ }, rfl⟩ }
  essSurj := {
    mem_essImage := by
      intro k
      exact ⟨{ left := k.1, right := k.2, square := uniqueIso _ _ }, ⟨Iso.refl k⟩⟩ }

variable [∀ (x y : E), Nonempty (x ⟶ y)]

noncomputable def uniqueEquivalence (x y : E) : Bicategory.Equivalence x y where
  hom := Classical.choice (inferInstance : Nonempty (x ⟶ y))
  inv := Classical.choice (inferInstance : Nonempty (y ⟶ x))
  unit := uniqueIso _ _
  counit := uniqueIso _ _
  left_triangle := Iso.ext (Subsingleton.elim _ _)

theorem productProjection_essentially_surjective (p : A × B) :
    ∃ x : Obj L R, Nonempty (Bicategory.Equivalence (productProjection.obj x) p) :=
  ⟨⟨p.1, p.2, uniqueEquivalence _ _⟩, ⟨Bicategory.Equivalence.id p⟩⟩
end ContractibleOverlap

end SquareKit.BicategoryIsoComma

end

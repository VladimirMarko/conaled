import SquareKit.SheafContextTopology
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-! Groupoids represented by object and arrow sheaves. Composition uses the
actual categorical pullback; parameter restriction is derived by precomposition. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Primitive represented operations and their endpoint equations. -/
structure Operations (J : GrothendieckTopology C) where
  objects : Sheaf J (Type (max u v))
  arrows : Sheaf J (Type (max u v))
  source : arrows ⟶ objects
  target : arrows ⟶ objects
  unit : objects ⟶ arrows
  inverse : arrows ⟶ arrows
  comp : pullback target source ⟶ arrows
  unit_source : unit ≫ source = 𝟙 objects
  unit_target : unit ≫ target = 𝟙 objects
  inverse_source : inverse ≫ source = target
  inverse_target : inverse ≫ target = source
  comp_source : comp ≫ source = pullback.fst target source ≫ source
  comp_target : comp ≫ target = pullback.snd target source ≫ target

namespace Operations
variable (G : Operations J) {X Y Z : Sheaf J (Type (max u v))}

/-- An object over an arbitrary sheaf parameter. -/
structure Object (X : Sheaf J (Type (max u v))) : Type (max (u + 1) (v + 1)) where
  map : X ⟶ G.objects

/-- Arrows retain a map into the arrow sheaf, with both endpoints. -/
structure Arrow (m n : G.Object X) where
  map : X ⟶ G.arrows
  source : map ≫ G.source = m.map
  target : map ≫ G.target = n.map

@[ext] theorem Arrow.ext {m n : G.Object X} (f g : G.Arrow m n)
    (h : f.map = g.map) : f = g := by cases f; cases g; cases h; rfl

def Arrow.ident (m : G.Object X) : G.Arrow m m :=
  ⟨m.map ≫ G.unit, by simp [Category.assoc, G.unit_source],
    by simp [Category.assoc, G.unit_target]⟩

def Arrow.comp {m n p : G.Object X} (f : G.Arrow m n) (g : G.Arrow n p) : G.Arrow m p :=
  ⟨pullback.lift f.map g.map (f.target.trans g.source.symm) ≫ G.comp,
    by simp [Category.assoc, G.comp_source, f.source],
    by simp [Category.assoc, G.comp_target, g.target]⟩

def Arrow.inverse {m n : G.Object X} (f : G.Arrow m n) : G.Arrow n m :=
  ⟨f.map ≫ G.inverse, by simpa [Category.assoc, G.inverse_source] using f.target,
    by simpa [Category.assoc, G.inverse_target] using f.source⟩

/-- Laws on the primitive operations, tested on all generalized arrows. -/
class Laws : Prop where
  id_comp : ∀ {X} {m n : G.Object X} (f : G.Arrow m n),
    (Arrow.ident G m).comp G f = f
  comp_id : ∀ {X} {m n : G.Object X} (f : G.Arrow m n),
    f.comp G (Arrow.ident G n) = f
  assoc : ∀ {X} {m n p q : G.Object X}
    (f : G.Arrow m n) (g : G.Arrow n p) (h : G.Arrow p q),
    (f.comp G g).comp G h = f.comp G (g.comp G h)
  inv_comp : ∀ {X} {m n : G.Object X} (f : G.Arrow m n),
    (f.inverse G).comp G f = Arrow.ident G n
  comp_inv : ∀ {X} {m n : G.Object X} (f : G.Arrow m n),
    f.comp G (f.inverse G) = Arrow.ident G m

instance [G.Laws] : Category (G.Object X) where
  Hom := G.Arrow
  id := Arrow.ident G
  comp := Arrow.comp G
  id_comp := Laws.id_comp
  comp_id := Laws.comp_id
  assoc := Laws.assoc

instance [G.Laws] : Groupoid (G.Object X) where
  inv := Arrow.inverse G
  inv_comp := Laws.inv_comp
  comp_inv := Laws.comp_inv

def Object.restrict (r : Y ⟶ X) (m : G.Object X) : G.Object Y := ⟨r ≫ m.map⟩
def Arrow.restrict (r : Y ⟶ X) {m n : G.Object X} (f : G.Arrow m n) :
    G.Arrow (m.restrict G r) (n.restrict G r) :=
  ⟨r ≫ f.map, by simp [Category.assoc, f.source, Object.restrict],
    by simp [Category.assoc, f.target, Object.restrict]⟩

@[simp] theorem Arrow.restrict_ident (r : Y ⟶ X) (m : G.Object X) :
    (Arrow.ident G m).restrict G r = Arrow.ident G (m.restrict G r) :=
  by
    apply Arrow.ext
    exact (Category.assoc _ _ _).symm

@[simp] theorem Arrow.restrict_comp (r : Y ⟶ X) {m n p : G.Object X}
    (f : G.Arrow m n) (g : G.Arrow n p) :
    (f.comp G g).restrict G r = (f.restrict G r).comp G (g.restrict G r) := by
  apply Arrow.ext
  change r ≫ pullback.lift _ _ _ ≫ G.comp = pullback.lift _ _ _ ≫ G.comp
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp [Arrow.restrict]

@[simp] theorem Arrow.restrict_inverse (r : Y ⟶ X) {m n : G.Object X}
    (f : G.Arrow m n) :
    (f.inverse G).restrict G r = (f.restrict G r).inverse G :=
  by
    apply Arrow.ext
    exact (Category.assoc _ _ _).symm

/-- Restriction preserves the actual arrow map, not merely its endpoints. -/
def restriction [G.Laws] (r : Y ⟶ X) : G.Object X ⥤ G.Object Y where
  obj := Object.restrict G r
  map := Arrow.restrict G r
  map_id := Arrow.restrict_ident G r
  map_comp := Arrow.restrict_comp G r

@[simp] theorem restriction_id [G.Laws] : restriction G (𝟙 X) = 𝟭 (G.Object X) := rfl
@[simp] theorem restriction_comp [G.Laws] (r : Y ⟶ X) (s : Z ⟶ Y) :
    restriction G r ⋙ restriction G s = restriction G (s ≫ r) := rfl

def functor [G.Laws] : (Sheaf J (Type (max u v)))ᵒᵖ ⥤ Cat where
  obj X := Cat.of (G.Object X.unop)
  map r := (restriction G r.unop).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev pseudofunctor [G.Laws] := (functor G).toPseudofunctor'

variable {A : Sheaf J (Type (max u v))} (e : A ≅ G.arrows)

/-- Change the arrow representation by an actual isomorphism, retaining objects. -/
abbrev changeArrows : Operations J where
  objects := G.objects
  arrows := A
  source := e.hom ≫ G.source
  target := e.hom ≫ G.target
  unit := G.unit ≫ e.inv
  inverse := e.hom ≫ G.inverse ≫ e.inv
  comp := pullback.lift
    (pullback.fst (e.hom ≫ G.target) (e.hom ≫ G.source) ≫ e.hom)
    (pullback.snd (e.hom ≫ G.target) (e.hom ≫ G.source) ≫ e.hom)
    (by simpa only [Category.assoc] using
      pullback.condition (f := e.hom ≫ G.target) (g := e.hom ≫ G.source)) ≫ G.comp ≫ e.inv
  unit_source := by simp [Category.assoc, G.unit_source]
  unit_target := by simp [Category.assoc, G.unit_target]
  inverse_source := by simp [Category.assoc, G.inverse_source]
  inverse_target := by simp [Category.assoc, G.inverse_target]
  comp_source := by simp [Category.assoc, G.comp_source]
  comp_target := by simp [Category.assoc, G.comp_target]

abbrev changeObject (m : (G.changeArrows e).Object X) : G.Object X := ⟨m.map⟩

def changeArrow {m n : (G.changeArrows e).Object X}
    (f : (G.changeArrows e).Arrow m n) : G.Arrow (G.changeObject e m) (G.changeObject e n) :=
  ⟨f.map ≫ e.hom, by simpa only [Category.assoc] using f.source,
    by simpa only [Category.assoc] using f.target⟩

/-- Changing coordinates retains every arrow, including coincident endpoints. -/
def changeArrowEquiv (m n : (G.changeArrows e).Object X) :
    (G.changeArrows e).Arrow m n ≃ G.Arrow (G.changeObject e m) (G.changeObject e n) where
  toFun := G.changeArrow e
  invFun f := ⟨f.map ≫ e.inv,
    by simpa [changeArrows, Category.assoc] using f.source,
    by simpa [changeArrows, Category.assoc] using f.target⟩
  left_inv f := by apply Arrow.ext; simp [changeArrow, Category.assoc]
  right_inv f := by apply Arrow.ext; simp [changeArrow, Category.assoc]

@[simp] theorem changeArrow_ident (m : (G.changeArrows e).Object X) :
    G.changeArrow e (Arrow.ident _ m) = Arrow.ident G (G.changeObject e m) := by
  apply Arrow.ext
  simp [changeArrow, Arrow.ident, changeArrows, Category.assoc]

@[simp] theorem changeArrow_comp {m n p : (G.changeArrows e).Object X}
    (f : (G.changeArrows e).Arrow m n) (g : (G.changeArrows e).Arrow n p) :
    G.changeArrow e (f.comp _ g) = (G.changeArrow e f).comp G (G.changeArrow e g) := by
  apply Arrow.ext
  simp only [changeArrow, Arrow.comp, changeArrows, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]

@[simp] theorem changeArrow_inverse {m n : (G.changeArrows e).Object X}
    (f : (G.changeArrows e).Arrow m n) :
    G.changeArrow e (f.inverse _) = (G.changeArrow e f).inverse G := by
  apply Arrow.ext
  simp [changeArrow, Arrow.inverse, changeArrows, Category.assoc]

instance changeArrows_laws [G.Laws] : (G.changeArrows e).Laws where
  id_comp f := (G.changeArrowEquiv e _ _).injective (by
    change G.changeArrow e _ = G.changeArrow e _
    rw [changeArrow_comp, changeArrow_ident]
    exact Laws.id_comp _)
  comp_id f := (G.changeArrowEquiv e _ _).injective (by
    change G.changeArrow e _ = G.changeArrow e _
    rw [changeArrow_comp, changeArrow_ident]
    exact Laws.comp_id _)
  assoc f g h := (G.changeArrowEquiv e _ _).injective (by
    change G.changeArrow e _ = G.changeArrow e _
    simp only [changeArrow_comp]
    exact Laws.assoc _ _ _)
  inv_comp f := (G.changeArrowEquiv e _ _).injective (by
    change G.changeArrow e _ = G.changeArrow e _
    rw [changeArrow_comp, changeArrow_inverse, changeArrow_ident]
    exact Laws.inv_comp _)
  comp_inv f := (G.changeArrowEquiv e _ _).injective (by
    change G.changeArrow e _ = G.changeArrow e _
    rw [changeArrow_comp, changeArrow_inverse, changeArrow_ident]
    exact Laws.comp_inv _)

def changeFunctor [G.Laws] : (G.changeArrows e).Object X ⥤ G.Object X where
  obj := G.changeObject e
  map := G.changeArrow e
  map_id := G.changeArrow_ident e
  map_comp := G.changeArrow_comp e

def changeFullyFaithful [G.Laws] : (G.changeFunctor (X := X) e).FullyFaithful where
  preimage := (G.changeArrowEquiv e _ _).symm
  map_preimage := (G.changeArrowEquiv e _ _).apply_symm_apply
  preimage_map := (G.changeArrowEquiv e _ _).symm_apply_apply

@[simp] theorem changeFunctor_restriction [G.Laws] (r : Y ⟶ X) :
    (G.changeArrows e).restriction r ⋙ G.changeFunctor e =
      G.changeFunctor e ⋙ G.restriction r := rfl

def changeTransformation [G.Laws] : Pseudofunctor.StrongTrans
    (G.changeArrows e).pseudofunctor G.pseudofunctor where
  app X := (G.changeFunctor (X := X.as.unop) e).toCatHom
  naturality _ := Iso.refl _
  naturality_naturality := by
    intro X Y f g h
    obtain rfl := LocallyDiscrete.eq_of_hom h
    have hh : h = 𝟙 f := Subsingleton.elim _ _
    subst h
    simp only [PrelaxFunctor.map₂_id]
    apply Cat.Hom₂.ext
    ext m
    simp
  naturality_id X := by
    cases X
    apply Cat.Hom₂.ext
    ext m
    dsimp [pseudofunctor, functor, Functor.toPseudofunctor']
    simp
    exact ((G.changeFunctor e).map_id _).symm
  naturality_comp f g := by
    cases f
    cases g
    apply Cat.Hom₂.ext
    ext m
    dsimp [pseudofunctor, functor, Functor.toPseudofunctor']
    simp
    exact ((G.changeFunctor e).map_id _).symm
end Operations

end SquareKit.SheafGroupoid

namespace SquareKit
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C]

/-- A represented groupoid, with laws on its supplied operations. -/
structure SheafGroupoid (J : GrothendieckTopology C) extends SheafGroupoid.Operations J where
  lawful : toOperations.Laws

attribute [instance] SheafGroupoid.lawful
end SquareKit

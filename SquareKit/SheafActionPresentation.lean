import SquareKit.SheafActionQuotientStack
import SquareKit.SheafActionQuotientLabels
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-! The action presentation has independent group labels as arrows. Its chart
comparison retains every arrow of the torsor quotient between regular objects. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafActionPresentation
open CategoryTheory Opposite SheafTorsor
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M : Sheaf J (Type (max u v))}
variable (a : SheafActionQuotient.Action G M)
variable {X Y Z : Sheaf J (Type (max u v))}

/-- An object is an actual map to the space acted upon. -/
structure Object (a : SheafActionQuotient.Action G M) (X : Sheaf J (Type (max u v))) : Type (max (u + 1) (v + 1)) where
  map : X ⟶ M

/-- Labels use the right-translation convention of regular left torsors. -/
structure Arrow (m n : Object a X) where
  label : X ⟶ groupSheaf G
  relation : a.onMap label n.map = m.map

variable {a}
@[ext] theorem Arrow.ext {m n : Object a X} (f g : Arrow a m n)
    (h : f.label = g.label) : f = g := by cases f; cases g; cases h; rfl

def Arrow.ident (m : Object a X) : Arrow a m m where
  label := labelOne X
  relation := by ext U x; exact a.one_act U _

def Arrow.comp {m n p : Object a X} (f : Arrow a m n) (g : Arrow a n p) : Arrow a m p where
  label := labelMul f.label g.label
  relation := by
    ext U x
    exact (a.mul_act U _ _ _).trans
      ((congrArg (a.act U (f.label.hom.app U x))
        (congrArg (fun k => k.hom.app U x) g.relation)).trans
          (congrArg (fun k => k.hom.app U x) f.relation))

instance : Category (Object a X) where
  Hom := Arrow a
  id := Arrow.ident
  comp := Arrow.comp
  id_comp f := Arrow.ext _ _ (labelOne_mul f.label)
  comp_id f := Arrow.ext _ _ (labelMul_one f.label)
  assoc f g h := Arrow.ext _ _ (labelMul_assoc f.label g.label h.label)

def Arrow.inverse {m n : Object a X} (f : Arrow a m n) : Arrow a n m where
  label := labelInv f.label
  relation := by
    ext U x
    have h := congrArg (fun k => k.hom.app U x) f.relation
    change a.act U (f.label.hom.app U x) (n.map.hom.app U x) = m.map.hom.app U x at h
    change a.act U ((show G.obj.obj U from f.label.hom.app U x)⁻¹) (m.map.hom.app U x) = _
    rw [← h, ← a.mul_act, inv_mul_cancel, a.one_act]
    rfl

instance : Groupoid (Object a X) where
  inv := Arrow.inverse
  inv_comp f := Arrow.ext _ _ (labelInv_mul f.label)
  comp_inv f := Arrow.ext _ _ (labelMul_inv f.label)

variable (a)
def quotient : Object a X ⥤ SheafActionQuotient.Object a X where
  obj m := SheafActionQuotient.chart a m.map
  map f := SheafActionQuotient.chartArrowOfRelation f.label _ _ f.relation
  map_id _ := by
    apply SheafActionQuotient.Arrow.ext
    exact regularArrow_ident
  map_comp f g := by
    apply SheafActionQuotient.Arrow.ext
    exact (regularArrow_comp f.label g.label).symm

/-- Recover a label from every quotient arrow, including ineffective labels. -/
def quotientHomEquiv (m n : Object a X) :
    (m ⟶ n) ≃ ((quotient a).obj m ⟶ (quotient a).obj n) where
  toFun := (quotient a).map
  invFun f := ⟨SheafActionQuotient.arrowLabel f, SheafActionQuotient.arrowLabel_relation f⟩
  left_inv f := Arrow.ext _ _ (regularArrowLabel_regularArrow f.label)
  right_inv := SheafActionQuotient.arrowLabel_recovers

def quotientFullyFaithful : (quotient (X := X) a).FullyFaithful where
  preimage := (quotientHomEquiv a _ _).symm
  map_preimage := (quotientHomEquiv a _ _).apply_symm_apply
  preimage_map := (quotientHomEquiv a _ _).symm_apply_apply

instance : (quotient (X := X) a).Full := (quotientFullyFaithful a).full
instance : (quotient (X := X) a).Faithful := (quotientFullyFaithful a).faithful

/-- Base change restricts maps and all group labels. -/
def restriction (f : Y ⟶ X) : Object a X ⥤ Object a Y where
  obj m := ⟨f ≫ m.map⟩
  map h := ⟨f ≫ h.label, congrArg (fun k => f ≫ k) h.relation⟩
  map_id _ := Arrow.ext _ _ rfl
  map_comp _ _ := Arrow.ext _ _ rfl

@[simp] theorem restriction_id : restriction a (𝟙 X) = 𝟭 (Object a X) := rfl
@[simp] theorem restriction_comp (f : Y ⟶ X) (g : Z ⟶ Y) :
    restriction a f ⋙ restriction a g = restriction a (g ≫ f) := rfl

def functor : (Sheaf J (Type (max u v)))ᵒᵖ ⥤ Cat where
  obj X := Cat.of (Object a X.unop)
  map f := (restriction a f.unop).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev pseudofunctor := (functor a).toPseudofunctor'

/-- The full chart comparison commutes with parameter restriction. -/
def transformation : Pseudofunctor.StrongTrans (pseudofunctor a)
    (SheafActionQuotient.Stack.pseudofunctor a) where
  app X := (quotient (X := X.as.unop) a).toCatHom
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
    apply Cat.Hom₂.ext
    ext m
    change 𝟙 _ = (quotient a).map (𝟙 _)
    exact (quotient a).map_id _ |>.symm
  naturality_comp f g := by
    apply Cat.Hom₂.ext
    ext m
    change 𝟙 _ = (quotient a).map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.comp_id]
    exact (quotient a).map_id _ |>.symm

end SquareKit.SheafActionPresentation

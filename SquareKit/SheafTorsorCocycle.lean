import SquareKit.SheafTorsorLabels
import SquareKit.SheafTorsorDescent
import SquareKit.SplitSheafCech

/-! Primitive group-valued cocycles and gauge arrows on a split sheaf cover.
The torsor action is on the left; transition labels multiply on the right. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafTorsor.Cocycle
open CategoryTheory Opposite
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (G : Sheaf J GrpCat.{w}) {X : Sheaf J (Type w)} (A : SplitSheaf.Ty X)

/-- Independent labels on pairs of lifts, natural at every restriction stage.
The equation orders successive transitions as `c(a,b) * c(b,c)`. -/
structure Datum where
  label (x : X.obj.Elements) (a b : A.family.obj x) : G.obj.obj x.obj
  identity (x : X.obj.Elements) (a : A.family.obj x) : label x a a = 1
  cocycle (x : X.obj.Elements) (a b c : A.family.obj x) :
    label x a b * label x b c = label x a c
  natural {x y : X.obj.Elements} (f : x ⟶ y) (a b : A.family.obj x) :
    G.obj.map f.hom (label x a b) = label y (A.family.map f a) (A.family.map f b)

variable {G A}

@[ext] theorem Datum.ext (c d : Datum G A) (h : ∀ x a b, c.label x a b = d.label x a b) : c = d := by
  cases c
  cases d
  congr
  funext x a b
  exact h x a b

/-- A gauge is an actual sheaf label on the cover, with its compatibility equation.
No inverse or global descended map is part of this primitive input. -/
structure Gauge (c d : Datum G A) where
  label : SplitSheaf.extension A ⟶ groupSheaf G
  compatible (x : X.obj.Elements) (a b : A.family.obj x) :
    c.label x a b * (show G.obj.obj x.obj from label.hom.app x.obj ⟨x.val, b⟩) =
      (show G.obj.obj x.obj from label.hom.app x.obj ⟨x.val, a⟩) * d.label x a b

@[ext] theorem Gauge.ext {c d : Datum G A} (a b : Gauge c d) (h : a.label = b.label) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- The identity cocycle is defined on every cover, including empty covers. -/
def trivial : Datum G A where
  label _ _ _ := 1
  identity _ _ := rfl
  cocycle _ _ _ _ := one_mul _
  natural f _ _ := (G.obj.map f.hom).hom.map_one

def labelValue (g : SplitSheaf.extension A ⟶ groupSheaf G)
    (x : X.obj.Elements) (a : A.family.obj x) : G.obj.obj x.obj := g.hom.app x.obj ⟨x.val, a⟩

/-- A restriction carries a chosen lift to its restricted lift. -/
def coverArrow {x y : X.obj.Elements} (f : x ⟶ y) (a : A.family.obj x) :
    (SplitSheaf.extension A).obj.elementsMk x.obj ⟨x.val, a⟩ ⟶
      (SplitSheaf.extension A).obj.elementsMk y.obj ⟨y.val, A.family.map f a⟩ :=
  Functor.Elements.homMk f.hom (by
      apply ElementFamilies.total_ext X.obj f.map_val
      change A.family.map _ (A.family.map _ a) = A.family.map f a
      rw [← ConcreteCategory.comp_apply, ← A.family.map_comp]
      have he : ElementFamilies.along X.obj f.hom x.val ≫
          ElementFamilies.vertical X.obj f.map_val = f := by
        apply Functor.Elements.hom_ext
        simp [ElementFamilies.vertical]
      rw [he])

theorem labelValue_natural (g : SplitSheaf.extension A ⟶ groupSheaf G)
    {x y : X.obj.Elements} (f : x ⟶ y) (a : A.family.obj x) :
    G.obj.map f.hom (labelValue g x a) = labelValue g y (A.family.map f a) := by
  let k := coverArrow f a
  have h := NatTrans.naturality_apply (regularArrow g).iso.hom k (1 : G.obj.obj x.obj)
  change G.obj.map f.hom (1 : G.obj.obj x.obj) * labelValue g y (A.family.map f a) =
    G.obj.map f.hom (1 * labelValue g x a) at h
  rw [(G.obj.map f.hom).hom.map_one, one_mul, one_mul] at h
  exact h.symm

/-- A chosen cover label produces its coboundary in the right-translation convention. -/
def coboundary (g : SplitSheaf.extension A ⟶ groupSheaf G) : Datum G A where
  label x a b := (labelValue g x a)⁻¹ * labelValue g x b
  identity x a := inv_mul_cancel _
  cocycle x a b c := by simp [mul_assoc]
  natural f a b := by
    rw [(G.obj.map f.hom).hom.map_mul, (G.obj.map f.hom).hom.map_inv,
      labelValue_natural, labelValue_natural]

/-- This explicit gauge records the chosen trivialization of a coboundary. -/
def coboundaryGauge (g : SplitSheaf.extension A ⟶ groupSheaf G) : Gauge trivial (coboundary g) where
  label := g
  compatible x a b := by
    change 1 * labelValue g x b = labelValue g x a * ((labelValue g x a)⁻¹ * labelValue g x b)
    simp

namespace Gauge

def ident (c : Datum G A) : Gauge c c where
  label := labelOne _
  compatible x a b := by change c.label x a b * 1 = 1 * c.label x a b; simp

def comp {c d e : Datum G A} (g : Gauge c d) (h : Gauge d e) : Gauge c e where
  label := labelMul g.label h.label
  compatible x a b := by
    change c.label x a b * (_ * _) = (_ * _) * e.label x a b
    rw [← mul_assoc, g.compatible, mul_assoc, h.compatible, ← mul_assoc]

def inverse {c d : Datum G A} (g : Gauge c d) : Gauge d c where
  label := labelInv g.label
  compatible x a b := by
    change d.label x a b * _⁻¹ = _⁻¹ * c.label x a b
    apply (eq_inv_mul_iff_mul_eq).mpr
    rw [← mul_assoc]
    exact (mul_inv_eq_iff_eq_mul).mpr (g.compatible x a b).symm

end Gauge

instance : Category (Datum G A) where
  Hom := Gauge
  id := Gauge.ident
  comp := Gauge.comp
  id_comp f := Gauge.ext _ _ (labelOne_mul f.label)
  comp_id f := Gauge.ext _ _ (labelMul_one f.label)
  assoc f g h := Gauge.ext _ _ (labelMul_assoc f.label g.label h.label)

instance : Groupoid (Datum G A) where
  inv := Gauge.inverse
  inv_comp f := Gauge.ext _ _ (labelInv_mul f.label)
  comp_inv f := Gauge.ext _ _ (labelMul_inv f.label)

def Gauge.toIso {c d : Datum G A} (g : Gauge c d) : c ≅ d where
  hom := g
  inv := g.inverse
  hom_inv_id := Gauge.ext _ _ (labelMul_inv g.label)
  inv_hom_id := Gauge.ext _ _ (labelInv_mul g.label)

/-- Cocycles act on the regular torsor by right translation. -/
def Datum.toDescent {G : Sheaf J GrpCat.{max u v}} {X : Sheaf J (Type (max u v))}
    {A : SplitSheaf.Ty X} (c : Datum G A) :
    Descent.Datum A (SheafTorsor.trivial G (SplitSheaf.extension A)) where
  transport x a b p := (show G.obj.obj x.obj from p) * c.label x a b
  identity x a p := by rw [c.identity, mul_one]
  cocycle x a b k p := by
    change G.obj.obj x.obj at p
    change (p * c.label x a b) * c.label x b k = p * c.label x a k
    rw [mul_assoc, c.cocycle]
  natural {x y} f a b p := by
    change G.obj.obj x.obj at p
    change G.obj.map f.hom (p * c.label _ a b) =
      G.obj.map f.hom p * c.label _ (A.family.map f a) (A.family.map f b)
    rw [(G.obj.map f.hom).hom.map_mul, c.natural]
  equivariant x a b g p := mul_assoc g (show G.obj.obj x.obj from p) (c.label x a b)

/-- Reading a regular descent transport at one recovers its primitive label. -/
def ofDescent {G : Sheaf J GrpCat.{max u v}} {X : Sheaf J (Type (max u v))}
    {A : SplitSheaf.Ty X} (d : Descent.Datum A (SheafTorsor.trivial G (SplitSheaf.extension A))) :
    Datum G A where
  label x a b := d.transport x a b (1 : G.obj.obj x.obj)
  identity x a := d.identity x a (1 : G.obj.obj x.obj)
  cocycle x a b k := by
    let t (a b : A.family.obj x) (p : G.obj.obj x.obj) : G.obj.obj x.obj := d.transport x a b p
    have he : t b k (t a b 1 * 1) = t a b 1 * t b k 1 :=
      d.equivariant x b k (t a b 1) (1 : G.obj.obj x.obj)
    rw [mul_one] at he
    exact he.symm.trans (d.cocycle x a b k (1 : G.obj.obj x.obj))
  natural {x y} f a b := by
    have h := d.natural f a b (1 : G.obj.obj x.obj)
    change G.obj.map f.hom (show G.obj.obj x.obj from d.transport x a b (1 : G.obj.obj x.obj)) =
      d.transport y (A.family.map f a) (A.family.map f b) (G.obj.map f.hom (1 : G.obj.obj x.obj)) at h
    rw [(G.obj.map f.hom).hom.map_one] at h
    exact h

end SquareKit.SheafTorsor.Cocycle

import SquareKit.SheafTorsor
import Mathlib.CategoryTheory.Discrete.Basic

/-! Action quotients with actual sheaf torsors and equivariant maps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafActionQuotient
open CategoryTheory Opposite
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A group sheaf acts naturally on the sections of a sheaf. -/
structure Action (G : Sheaf J GrpCat.{w}) (M : Sheaf J (Type w)) where
  act (U : Cᵒᵖ) : G.obj.obj U → M.obj.obj U → M.obj.obj U
  one_act (U : Cᵒᵖ) (m : M.obj.obj U) : act U 1 m = m
  mul_act (U : Cᵒᵖ) (g h : G.obj.obj U) (m : M.obj.obj U) :
    act U (g * h) m = act U g (act U h m)
  natural {U V : Cᵒᵖ} (f : U ⟶ V) (g : G.obj.obj U) (m : M.obj.obj U) :
    M.obj.map f (act U g m) = act V (G.obj.map f g) (M.obj.map f m)

variable {G : Sheaf J GrpCat.{w}} {M : Sheaf J (Type w)}
variable (a : Action G M) {X Y Z : Sheaf J (Type w)}

/-- Quotient objects include every locally trivial torsor, with a genuine
natural equivariant map from its total sheaf to the acted-on sheaf. -/
structure Object (X : Sheaf J (Type w)) where
  torsor : SheafTorsor.Torsor G X
  value (x : X.obj.Elements) : torsor.family.family.obj x → M.obj.obj x.obj
  natural {x y : X.obj.Elements} (f : x ⟶ y) (p : torsor.family.family.obj x) :
    M.obj.map f.hom (value x p) = value y (torsor.family.family.map f p)
  equivariant (x : X.obj.Elements) (g : G.obj.obj x.obj) (p : torsor.family.family.obj x) :
    value x (torsor.act x g p) = a.act x.obj g (value x p)

variable {a}

def Object.totalMap (P : Object a X) : SplitSheaf.Ext P.torsor.family ⟶ M := ⟨{
  app U := ↾fun p => P.value (X.obj.elementsMk U p.1) p.2
  naturality {U V} f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨x,p⟩
    exact (P.natural (ElementFamilies.along X.obj f x) p).symm }⟩

structure Arrow (P Q : Object a X) where
  torsorArrow : SheafTorsor.Arrow P.torsor Q.torsor
  preserves (x : X.obj.Elements) (p : P.torsor.family.family.obj x) :
    Q.value x (torsorArrow.iso.hom.app x p) = P.value x p

@[ext] theorem Arrow.ext {P Q : Object a X} (f g : Arrow P Q)
    (h : f.torsorArrow = g.torsorArrow) : f = g := by
  cases f
  cases g
  cases h
  rfl

def Arrow.ident (P : Object a X) : Arrow P P where
  torsorArrow := SheafTorsor.Arrow.ident P.torsor
  preserves _ _ := rfl

def Arrow.comp {P Q R : Object a X} (f : Arrow P Q) (g : Arrow Q R) : Arrow P R where
  torsorArrow := f.torsorArrow.comp g.torsorArrow
  preserves x p := (g.preserves x (f.torsorArrow.iso.hom.app x p)).trans (f.preserves x p)

instance : Category (Object a X) where
  Hom := Arrow
  id := Arrow.ident
  comp := Arrow.comp
  id_comp f := by apply Arrow.ext; apply SheafTorsor.Arrow.ext; exact Category.id_comp _
  comp_id f := by apply Arrow.ext; apply SheafTorsor.Arrow.ext; exact Category.comp_id _
  assoc f g h := by apply Arrow.ext; apply SheafTorsor.Arrow.ext; exact Category.assoc _ _ _

def Arrow.inverse {P Q : Object a X} (f : Arrow P Q) : Arrow Q P where
  torsorArrow := f.torsorArrow.inverse
  preserves x q := by
    have h := f.preserves x (f.torsorArrow.iso.inv.app x q)
    have he := congrArg (fun k => k.app x q) f.torsorArrow.iso.inv_hom_id
    exact h.symm.trans (congrArg (Q.value x) he)

instance : Groupoid (Object a X) where
  inv := Arrow.inverse
  inv_comp f := by apply Arrow.ext; apply SheafTorsor.Arrow.ext; exact f.torsorArrow.iso.inv_hom_id
  comp_inv f := by apply Arrow.ext; apply SheafTorsor.Arrow.ext; exact f.torsorArrow.iso.hom_inv_id

def Arrow.toIso {P Q : Object a X} (f : Arrow P Q) : P ≅ Q where
  hom := f
  inv := f.inverse
  hom_inv_id := by apply Arrow.ext; apply SheafTorsor.Arrow.ext; exact f.torsorArrow.iso.hom_inv_id
  inv_hom_id := by apply Arrow.ext; apply SheafTorsor.Arrow.ext; exact f.torsorArrow.iso.inv_hom_id

def forget : Object a X ⥤ SheafTorsor.Torsor G X where
  obj P := P.torsor
  map f := f.torsorArrow

instance : (forget (a := a) (X := X)).Faithful where
  map_injective := Arrow.ext _ _

def reindex (P : Object a X) (f : Y ⟶ X) : Object a Y where
  torsor := SheafTorsor.reindex P.torsor f
  value x := P.value (f.hom.mapElements.obj x)
  natural k p := P.natural (f.hom.mapElements.map k) p
  equivariant x := P.equivariant (f.hom.mapElements.obj x)

def Arrow.reindex {P Q : Object a X} (h : Arrow P Q) (f : Y ⟶ X) :
    Arrow (reindex P f) (reindex Q f) where
  torsorArrow := h.torsorArrow.reindex f
  preserves x := h.preserves (f.hom.mapElements.obj x)

def restriction (f : Y ⟶ X) : Object a X ⥤ Object a Y where
  obj P := reindex P f
  map h := h.reindex f

@[simp] theorem reindex_id (P : Object a X) : reindex P (𝟙 X) = P := rfl
@[simp] theorem reindex_comp (P : Object a X) (f : Y ⟶ X) (g : Z ⟶ Y) :
    reindex (reindex P f) g = reindex P (g ≫ f) := rfl
@[simp] theorem restriction_id : restriction (a := a) (𝟙 X) = 𝟭 (Object a X) := rfl
@[simp] theorem restriction_comp (f : Y ⟶ X) (g : Z ⟶ Y) :
    restriction (a := a) f ⋙ restriction g = restriction (g ≫ f) := rfl

/-- A chart point is represented by the regular torsor and its orbit map. -/
def chart (a : Action G M) (m : X ⟶ M) : Object a X where
  torsor := SheafTorsor.trivial G X
  value x g := a.act x.obj g (m.hom.app x.obj x.val)
  natural {x y} f g := by
    rw [a.natural]
    congr 1
    exact (NatTrans.naturality_apply m.hom f.hom x.val).symm.trans
      (congrArg (m.hom.app y.obj) f.map_val)
  equivariant x g h := a.mul_act x.obj g h _

@[simp] theorem chart_reindex (m : X ⟶ M) (f : Y ⟶ X) :
    reindex (chart a m) f = chart a (f ≫ m) := rfl

/-- Applying a variable group label to a sheaf-valued point is natural. -/
def Action.onMap (a : Action G M) (g : X ⟶ SheafTorsor.groupSheaf G) (m : X ⟶ M) : X ⟶ M := ⟨{
  app U := ↾fun x => a.act U (g.hom.app U x) (m.hom.app U x)
  naturality {U V} f := by
    apply ConcreteCategory.hom_ext
    intro x
    symm
    change M.obj.map f (a.act U (g.hom.app U x) (m.hom.app U x)) = _
    rw [a.natural]
    exact congrArg₂ (a.act V) (NatTrans.naturality_apply g.hom f x).symm
      (NatTrans.naturality_apply m.hom f x).symm }⟩

/-- The regular-torsor arrow uses right translation. Its label h satisfies
m = h·n; this orientation is explicit and retains the entire arrow label. -/
def chartArrowOfRelation (g : X ⟶ SheafTorsor.groupSheaf G) (m n : X ⟶ M)
    (h : a.onMap g n = m) : Arrow (chart a m) (chart a n) where
  torsorArrow := SheafTorsor.regularArrow g
  preserves x p := by
    change G.obj.obj x.obj at p
    change a.act x.obj (p * (show G.obj.obj x.obj from g.hom.app x.obj x.val))
      (n.hom.app x.obj x.val) = a.act x.obj p (m.hom.app x.obj x.val)
    rw [a.mul_act]
    exact congrArg (a.act x.obj p) (congrArg (fun k : X ⟶ M => k.hom.app x.obj x.val) h)

theorem chartArrowOfRelation_injective (m n : X ⟶ M) :
    Function.Injective (fun g : {g : X ⟶ SheafTorsor.groupSheaf G // a.onMap g n = m} =>
      chartArrowOfRelation g.val m n g.property) := by
  intro g h he
  apply Subtype.ext
  apply SheafTorsor.regularArrow_injective
  exact congrArg Arrow.torsorArrow he

/-- Transport a quotient object along any equivariant torsor isomorphism. -/
def Object.transfer (P : Object a X) {T : SheafTorsor.Torsor G X}
    (e : SheafTorsor.Arrow T P.torsor) : Object a X where
  torsor := T
  value x p := P.value x (e.iso.hom.app x p)
  natural f p := (P.natural f _).trans
    (congrArg (P.value _) (NatTrans.naturality_apply e.iso.hom f p).symm)
  equivariant x g p := by rw [e.equivariant, P.equivariant]

def Object.transferArrow (P : Object a X) {T : SheafTorsor.Torsor G X}
    (e : SheafTorsor.Arrow T P.torsor) : Arrow (P.transfer e) P where
  torsorArrow := e
  preserves _ _ := rfl

def chartFunctor (a : Action G M) (X : Sheaf J (Type w)) :
    Discrete (X ⟶ M) ⥤ Object a X := Discrete.functor (chart a)

/-- Evaluation at the identity recovers the variable label of every regular arrow. -/
def arrowLabel {m n : X ⟶ M} (f : Arrow (chart a m) (chart a n)) :
    X ⟶ SheafTorsor.groupSheaf G := ⟨{
  app U := ↾fun x => f.torsorArrow.iso.hom.app (X.obj.elementsMk U x) (1 : G.obj.obj U)
  naturality {U V} k := by
    apply ConcreteCategory.hom_ext
    intro x
    have h := NatTrans.naturality_apply f.torsorArrow.iso.hom
      (ElementFamilies.along X.obj k x) (1 : G.obj.obj U)
    change f.torsorArrow.iso.hom.app (X.obj.elementsMk V (X.obj.map k x)) (G.obj.map k 1) = _ at h
    rw [(G.obj.map k).hom.map_one] at h
    exact h }⟩

theorem arrowLabel_relation {m n : X ⟶ M} (f : Arrow (chart a m) (chart a n)) :
    a.onMap (arrowLabel f) n = m := by
  ext U x
  exact (f.preserves (X.obj.elementsMk U x) (1 : G.obj.obj U)).trans
    (a.one_act U (m.hom.app U x))

theorem arrowLabel_recovers {m n : X ⟶ M} (f : Arrow (chart a m) (chart a n)) :
    chartArrowOfRelation (arrowLabel f) m n (arrowLabel_relation f) = f := by
  apply Arrow.ext
  apply SheafTorsor.Arrow.ext
  ext x p
  change G.obj.obj x.obj at p
  have h := f.torsorArrow.equivariant x p (1 : G.obj.obj x.obj)
  change f.torsorArrow.iso.hom.app x (p * 1) =
    p * (show G.obj.obj x.obj from f.torsorArrow.iso.hom.app x (1 : G.obj.obj x.obj)) at h
  rw [mul_one] at h
  exact h.symm

def chartArrowEquiv (m n : X ⟶ M) :
    Arrow (chart a m) (chart a n) ≃
      {g : X ⟶ SheafTorsor.groupSheaf G // a.onMap g n = m} where
  toFun f := ⟨arrowLabel f, arrowLabel_relation f⟩
  invFun g := chartArrowOfRelation g.val m n g.property
  left_inv := arrowLabel_recovers
  right_inv g := by
    apply Subtype.ext
    ext U x
    exact one_mul (show G.obj.obj U from g.val.hom.app U x)

/-- A section of an arbitrary torsor produces a sheaf-valued point. -/
def Object.sectionMap (P : Object a X) (t : SplitSheaf.Tm P.torsor.family) : X ⟶ M := ⟨{
  app U := ↾fun x => P.value (X.obj.elementsMk U x) (t.val (X.obj.elementsMk U x))
  naturality {U V} f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact ((P.natural (ElementFamilies.along X.obj f x) _).trans
      (congrArg (P.value _) (t.natural (ElementFamilies.along X.obj f x)))).symm }⟩

/-- An actual trivialization identifies the object with its orbit-map chart.
This theorem applies only when a trivialization is supplied. -/
def Object.chartOfTrivialization (P : Object a X)
    (e : SheafTorsor.Arrow (SheafTorsor.trivial G X) P.torsor) :
    Arrow (chart a (P.sectionMap (SheafTorsor.sectionOfArrow e))) P where
  torsorArrow := e
  preserves x g := by
    change G.obj.obj x.obj at g
    have h := e.equivariant x g (1 : G.obj.obj x.obj)
    change e.iso.hom.app x (g * 1) = P.torsor.act x g (e.iso.hom.app x (1 : G.obj.obj x.obj)) at h
    rw [mul_one] at h
    exact (congrArg (P.value x) h).trans (P.equivariant x g _)

/-- An invariant point equips any torsor with a quotient object, including
nontrivial torsors without global sections. -/
def invariantObject (T : SheafTorsor.Torsor G X) (m : X ⟶ M)
    (h : ∀ (x : X.obj.Elements) (g : G.obj.obj x.obj),
      a.act x.obj g (m.hom.app x.obj x.val) = m.hom.app x.obj x.val) : Object a X where
  torsor := T
  value x _ := m.hom.app x.obj x.val
  natural {x y} f _ := (NatTrans.naturality_apply m.hom f.hom x.val).symm.trans
    (congrArg (m.hom.app y.obj) f.map_val)
  equivariant x g _ := (h x g).symm

/-- An invariant-point object cannot become a chart unless its torsor admits
a global section. -/
theorem not_chart_of_no_section (P : Object a X)
    (h : ¬ Nonempty (SplitSheaf.Tm P.torsor.family)) (m : X ⟶ M) :
    ¬ Nonempty (Arrow (chart a m) P) := by
  rintro ⟨e⟩
  exact h ⟨SheafTorsor.sectionOfArrow e.torsorArrow⟩

end SquareKit.SheafActionQuotient

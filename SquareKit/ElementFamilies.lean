import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! Experimental fibers and dependent total spaces over a type-valued functor.
The section universe is independent of the base category's hom universe. -/
namespace SquareKit.ElementFamilies
open CategoryTheory
universe u v w
variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)

/-- Actual section-map fibers, varying over Mathlib's category of elements. -/
def fibers (p : Over F) : F.Elements ⥤ Type w where
  obj x := {a : p.left.obj x.obj // p.hom.app x.obj a = x.val}
  map f := ↾fun a => ⟨p.left.map f.hom a.val, by
    rw [NatTrans.naturality_apply, a.property, f.map_val]⟩
  map_id x := by apply ConcreteCategory.hom_ext; intro a; apply Subtype.ext; exact congrArg (fun k => k a.val) (p.left.map_id x.obj)
  map_comp f g := by apply ConcreteCategory.hom_ext; intro a; apply Subtype.ext; exact congrArg (fun k => k a.val) (p.left.map_comp f.hom g.hom)

/-- A morphism over F acts within each actual fiber. -/
def fiberMap {p q : Over F} (k : p ⟶ q) : fibers F p ⟶ fibers F q where
  app x := ↾fun a => ⟨k.left.app x.obj a.val, by
    exact (congrArg (fun n => n.app x.obj a.val) (Over.w k)).trans a.property⟩
  naturality {X Y} f := by
    ext a
    apply Subtype.ext
    exact NatTrans.naturality_apply k.left f.hom a.val

def fiberFunctor : Over F ⥤ (F.Elements ⥤ Type w) where
  obj := fibers F
  map := fiberMap F

/-- A total section retains its base section and its dependent fiber value. -/
abbrev Total (Q : F.Elements ⥤ Type w) (U : C) := Σ x : F.obj U, Q.obj (F.elementsMk U x)

/-- Transport within one base object; the underlying arrow is the identity. -/
def vertical {U : C} {x y : F.obj U} (h : x = y) : F.elementsMk U x ⟶ F.elementsMk U y :=
  Functor.Elements.homMk (𝟙 U) (by simpa using h)

@[simp] theorem vertical_rfl {U : C} (x : F.obj U) : vertical F (rfl : x = x) = 𝟙 _ := by
  apply Functor.Elements.hom_ext
  rfl

/-- Equality of dependent pairs expressed using the functor's own transport. -/
theorem total_ext {Q : F.Elements ⥤ Type w} {U : C} {p q : Total F Q U}
    (h : p.1 = q.1) (hv : Q.map (vertical F h) p.2 = q.2) : p = q := by
  rcases p with ⟨x, a⟩
  rcases q with ⟨y, b⟩
  dsimp at h
  subst y
  simp only [vertical_rfl, Q.map_id, types_id_apply] at hv
  cases hv
  rfl

/-- The canonical arrow carrying a section along a base arrow. -/
abbrev along {U V : C} (f : U ⟶ V) (x : F.obj U) :
    F.elementsMk U x ⟶ F.elementsMk V (F.map f x) := Functor.Elements.homMk f rfl

def totalMap (Q : F.Elements ⥤ Type w) {U V : C} (f : U ⟶ V) : Total F Q U → Total F Q V :=
  fun p => ⟨F.map f p.1, Q.map (along F f p.1) p.2⟩

theorem totalMap_id (Q : F.Elements ⥤ Type w) (U : C) (p : Total F Q U) :
    totalMap F Q (𝟙 U) p = p := by
  apply total_ext F (by simp [totalMap])
  dsimp only [totalMap]
  change Q.map _ (Q.map _ p.2) = p.2
  rw [← ConcreteCategory.comp_apply, ← Q.map_comp]
  have h : along F (𝟙 U) p.1 ≫ vertical F (by simp) = 𝟙 (F.elementsMk U p.1) := by
    apply Functor.Elements.hom_ext
    simp [vertical]
  rw [h, Q.map_id]
  rfl

theorem totalMap_comp (Q : F.Elements ⥤ Type w) {U V W : C}
    (f : U ⟶ V) (g : V ⟶ W) (p : Total F Q U) :
    totalMap F Q (f ≫ g) p = totalMap F Q g (totalMap F Q f p) := by
  apply total_ext F (by simp [totalMap])
  dsimp only [totalMap]
  change Q.map _ (Q.map _ p.2) = Q.map _ (Q.map _ p.2)
  simp only [← ConcreteCategory.comp_apply, ← Q.map_comp]
  congr 2
  congr 1
  apply Functor.Elements.hom_ext
  simp [vertical]

/-- The dependent sum of the fibers, as an actual functor. -/
def total (Q : F.Elements ⥤ Type w) : C ⥤ Type w where
  obj := Total F Q
  map f := ↾totalMap F Q f
  map_id U := by apply ConcreteCategory.hom_ext; intro p; exact totalMap_id F Q U p
  map_comp f g := by apply ConcreteCategory.hom_ext; intro p; exact totalMap_comp F Q f g p

def display (Q : F.Elements ⥤ Type w) : total F Q ⟶ F where
  app U := ↾Sigma.fst

/-- A natural map of fibers preserves the base section in the total space. -/
def totalNat {Q R : F.Elements ⥤ Type w} (k : Q ⟶ R) : total F Q ⟶ total F R where
  app U := ↾fun p => ⟨p.1, k.app (F.elementsMk U p.1) p.2⟩
  naturality {U V} f := by
    apply ConcreteCategory.hom_ext
    intro p
    exact congrArg (fun a => (⟨F.map f p.1, a⟩ : Total F R V))
      (NatTrans.naturality_apply k (along F f p.1) p.2)

def totalFunctor : (F.Elements ⥤ Type w) ⥤ Over F where
  obj Q := Over.mk (display F Q)
  map k := Over.homMk (totalNat F k) rfl

/-- Rebuilding a display forgets only its redundant fiber equation. -/
def reconstructionEquiv (p : Over F) (U : C) : Total F (fibers F p) U ≃ p.left.obj U :=
  Equiv.sigmaFiberEquiv (p.hom.app U)

def reconstruction (p : Over F) : (totalFunctor F).obj ((fiberFunctor F).obj p) ≅ p :=
  Over.isoMk (NatIso.ofComponents (fun U => (reconstructionEquiv F p U).toIso)
    (by intro U V f; rfl)) (by
      ext U z
      exact z.2.property)

def unitIso : 𝟭 (Over F) ≅ fiberFunctor F ⋙ totalFunctor F :=
  (NatIso.ofComponents (reconstruction F) (by intro p q k; rfl)).symm

/-- The fiber of a dependent sum recovers exactly the original fiber. -/
def fiberTotalEquiv (Q : F.Elements ⥤ Type w) (x : F.Elements) :
    (fibers F (Over.mk (display F Q))).obj x ≃ Q.obj x where
  toFun z := Q.map (vertical F z.property) z.val.2
  invFun a := ⟨⟨x.val, a⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨y, a⟩, h⟩
    change y = x.val at h
    cases h
    apply Subtype.ext
    change (⟨x.val, Q.map (vertical F (rfl : x.val = x.val)) a⟩ : Total F Q x.obj) = ⟨x.val, a⟩
    simp only [vertical_rfl, Q.map_id, types_id_apply]
  right_inv a := by
    change Q.map (vertical F (rfl : x.val = x.val)) a = a
    simp only [vertical_rfl, Q.map_id, types_id_apply]

def fiberTotalIso (Q : F.Elements ⥤ Type w) :
    (totalFunctor F ⋙ fiberFunctor F).obj Q ≅ Q :=
  NatIso.ofComponents (fun x => (fiberTotalEquiv F Q x).toIso) (by
    intro x y f
    apply ConcreteCategory.hom_ext
    intro z
    change Q.map (vertical F _) (Q.map (along F f.hom z.val.1) z.val.2) =
      Q.map f (Q.map (vertical F z.property) z.val.2)
    have hz : F.map f.hom z.val.1 = y.val := by
      rw [show z.val.1 = x.val from z.property]
      exact f.map_val
    have hm : along F f.hom z.val.1 ≫ vertical F hz = vertical F z.property ≫ f := by
      apply Functor.Elements.hom_ext
      simp [vertical]
    have hh := congrArg (fun k => Q.map k z.val.2) hm
    erw [Q.map_comp, Q.map_comp] at hh
    exact hh)

def counitIso : totalFunctor F ⋙ fiberFunctor F ≅ 𝟭 (F.Elements ⥤ Type w) :=
  NatIso.ofComponents (fiberTotalIso F) (by
    intro Q R k
    ext x z
    exact (NatTrans.naturality_apply k (vertical F z.property) z.val.2).symm)

/-- Slice objects are equivalent to families on the category of elements. -/
def equivalence : Over F ≌ (F.Elements ⥤ Type w) :=
  CategoryTheory.Equivalence.mk (fiberFunctor F) (totalFunctor F) (unitIso F) (counitIso F)

end SquareKit.ElementFamilies

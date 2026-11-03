import SquareKit.GroupoidTransportRoutes
import Mathlib.CategoryTheory.Groupoid.Basic
import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
import Mathlib.CategoryTheory.Groupoid.Discrete
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma

/-! A bounded universe of finite sets. Enumeration is chosen, not canonical.
Arrows retain bijections even when source and target cardinalities agree. -/
noncomputable section
namespace SquareKit.FiniteUniverse
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

structure Code where
  size : Nat
  deriving DecidableEq

instance : Groupoid Code where
  Hom n m := Fin n.size ≃ Fin m.size
  id _ := Equiv.refl _
  comp p q := p.trans q
  inv p := p.symm
  id_comp _ := Equiv.ext fun _ => rfl
  comp_id _ := Equiv.ext fun _ => rfl
  assoc _ _ _ := Equiv.ext fun _ => rfl
  inv_comp p := Equiv.ext p.apply_symm_apply
  comp_inv p := Equiv.ext p.symm_apply_apply

abbrev decode : Code ⥤ Type where
  obj n := Fin n.size
  map p := ↾p.toFun
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Any chosen enumeration gives a code, without identifying its automorphisms. -/
structure Enumeration (A : Type) where
  code : Code
  decode : Fin code.size ≃ A

namespace Enumeration
variable {A B C : Type}
def map (a : Enumeration A) (b : Enumeration B) (e : A ≃ B) : Fin a.code.size ≃ Fin b.code.size :=
  a.decode.trans (e.trans b.decode.symm)

theorem naturality (a : Enumeration A) (b : Enumeration B) (e : A ≃ B)
    (i : Fin a.code.size) : b.decode (a.map b e i) = e (a.decode i) := by
  simp [map]

theorem map_identity (a : Enumeration A) : a.map a (Equiv.refl A) = Equiv.refl _ := by
  ext i; simp [map]

theorem map_comp (a : Enumeration A) (b : Enumeration B) (c : Enumeration C)
    (e : A ≃ B) (f : B ≃ C) :
    a.map c (e.trans f) = (a.map b e).trans (b.map c f) := by
  ext i; simp [map]

/-- Change-of-enumeration arrows obey the same cocycle law. -/
theorem change_comp (a b c : Enumeration A) :
    a.map c (Equiv.refl A) = (a.map b (Equiv.refl A)).trans (b.map c (Equiv.refl A)) :=
  a.map_comp b c (Equiv.refl A) (Equiv.refl A)
end Enumeration

def enumerate (A : Type) [Fintype A] : Enumeration A :=
  ⟨⟨Fintype.card A⟩, (Fintype.equivFin A).symm⟩

/-- Codes come with actual decoding bijections, not just cardinality equations. -/
def sumCode {n : Nat} (b : Fin n → Nat) : Enumeration (Σ i, Fin (b i)) := enumerate _
def productCode {n : Nat} (b : Fin n → Nat) : Enumeration ((i : Fin n) → Fin (b i)) :=
  enumerate _

def sumEquiv {n m : Nat} {b : Fin n → Nat} {c : Fin m → Nat}
    (e : Fin n ≃ Fin m) (f : ∀ i, Fin (b i) ≃ Fin (c (e i))) :
    (Σ i, Fin (b i)) ≃ (Σ j, Fin (c j)) := Equiv.sigmaCongr e f

def productEquiv {n m : Nat} {b : Fin n → Nat} {c : Fin m → Nat}
    (e : Fin n ≃ Fin m) (f : ∀ i, Fin (b i) ≃ Fin (c (e i))) :
    ((i : Fin n) → Fin (b i)) ≃ ((j : Fin m) → Fin (c j)) := Equiv.piCongr e f

theorem sum_naturality {n m : Nat} {b : Fin n → Nat} {c : Fin m → Nat}
    (e : Fin n ≃ Fin m) (f : ∀ i, Fin (b i) ≃ Fin (c (e i)))
    (x : Fin (sumCode b).code.size) :
    (sumCode c).decode ((sumCode b).map (sumCode c) (sumEquiv e f) x) =
      ⟨e ((sumCode b).decode x).1, f _ ((sumCode b).decode x).2⟩ :=
  Enumeration.naturality _ _ _ _

theorem product_naturality {n m : Nat} {b : Fin n → Nat} {c : Fin m → Nat}
    (e : Fin n ≃ Fin m) (f : ∀ i, Fin (b i) ≃ Fin (c (e i)))
    (x : Fin (productCode b).code.size) (i : Fin n) :
    (productCode c).decode ((productCode b).map (productCode c) (productEquiv e f) x) (e i) =
      f i ((productCode b).decode x i) := by
  rw [Enumeration.naturality]
  exact Equiv.piCongr_apply_apply (W := fun i => Fin (b i)) (Z := fun j => Fin (c j)) e f _ i

/-- The ordinary finite-set groupoid is a second presentation. -/
structure FiniteSet where
  carrier : Type
  finite : Fintype carrier
attribute [instance] FiniteSet.finite

instance : Groupoid FiniteSet where
  Hom A B := A.carrier ≃ B.carrier
  id _ := Equiv.refl _
  comp p q := p.trans q
  inv p := p.symm
  id_comp _ := Equiv.ext fun _ => rfl
  comp_id _ := Equiv.ext fun _ => rfl
  assoc _ _ _ := Equiv.ext fun _ => rfl
  inv_comp p := Equiv.ext p.apply_symm_apply
  comp_inv p := Equiv.ext p.symm_apply_apply

abbrev elements : FiniteSet ⥤ Type where
  obj A := A.carrier
  map p := ↾p.toFun
  map_id _ := rfl
  map_comp _ _ := rfl

open GroupoidTransport

def realize : Route decode elements where
  base := { obj := fun n => ⟨Fin n.size, inferInstance⟩, map := fun p => p }
  fiber := { app := fun _ => ↾id }

def classify : Route elements decode where
  base :=
    { obj := fun A => (enumerate A.carrier).code
      map := fun {A B} p => (enumerate A.carrier).map (enumerate B.carrier) p
      map_id := fun A => Enumeration.map_identity _
      map_comp := fun p q => Enumeration.map_comp _ _ _ p q }
  fiber :=
    { app := fun A => ↾(enumerate A.carrier).decode.symm
      naturality := by
        intro A B p
        ext x
        change (enumerate B.carrier).decode.symm ((show A.carrier ≃ B.carrier from p) x) =
          (enumerate A.carrier).map (enumerate B.carrier) p ((enumerate A.carrier).decode.symm x)
        simp [Enumeration.map] }

/-- Bounded generic-family property: every finite set with its chosen Fintype
has a decoding bijection; naturality covers every bijection between fibres. -/
def genericFiber (A : FiniteSet) : Fin (classify.base.obj A).size ≃ A.carrier :=
  (enumerate A.carrier).decode

theorem generic_natural {A B : FiniteSet} (p : A.carrier ≃ B.carrier)
    (x : Fin (classify.base.obj A).size) :
    genericFiber B ((show Fin (classify.base.obj A).size ≃ Fin (classify.base.obj B).size from classify.base.map p) x) = p (genericFiber A x) :=
  Enumeration.naturality _ _ _ _

/-- Chosen finite families are pullbacks of decoding on their object sets.
The projection is unchanged; `family_transport` supplies the arrow comparison. -/
def familyEquiv {C : Type} [Category C] (B : C ⥤ FiniteSet) :
    (Σ x, Fin (classify.base.obj (B.obj x)).size) ≃ (Σ x, (B.obj x).carrier) :=
  Equiv.sigmaCongrRight fun x => genericFiber (B.obj x)

theorem family_projection {C : Type} [Category C] (B : C ⥤ FiniteSet)
    (x : Σ x, Fin (classify.base.obj (B.obj x)).size) :
    (familyEquiv B x).1 = x.1 := rfl

theorem family_transport {C : Type} [Category C] (B : C ⥤ FiniteSet)
    {x y : C} (p : x ⟶ y) (i : Fin (classify.base.obj (B.obj x)).size) :
    genericFiber (B.obj y) (decode.map ((B ⋙ classify.base).map p) i) =
      elements.map (B.map p) (genericFiber (B.obj x) i) :=
  generic_natural (B.map p) i

theorem sumEquiv_comp {n m k : Nat} {b : Fin n → Nat} {c : Fin m → Nat}
    {d : Fin k → Nat} (e : Fin n ≃ Fin m) (g : Fin m ≃ Fin k)
    (f : ∀ i, Fin (b i) ≃ Fin (c (e i)))
    (h : ∀ j, Fin (c j) ≃ Fin (d (g j))) :
    sumEquiv (e.trans g) (fun i => (f i).trans (h (e i))) =
      (sumEquiv e f).trans (sumEquiv g h) := by
  apply Equiv.ext; intro x; rfl

theorem productEquiv_comp {n m k : Nat} {b : Fin n → Nat} {c : Fin m → Nat}
    {d : Fin k → Nat} (e : Fin n ≃ Fin m) (g : Fin m ≃ Fin k)
    (f : ∀ i, Fin (b i) ≃ Fin (c (e i)))
    (h : ∀ j, Fin (c j) ≃ Fin (d (g j))) :
    productEquiv (e.trans g) (fun i => (f i).trans (h (e i))) =
      (productEquiv e f).trans (productEquiv g h) := by
  apply Equiv.ext; intro x; funext z
  obtain ⟨j, rfl⟩ := g.surjective z
  obtain ⟨i, rfl⟩ := e.surjective j
  change Equiv.piCongr (e.trans g) _ x ((e.trans g) i) = _
  simp only [Equiv.piCongr_apply_apply, productEquiv, Equiv.trans_apply]
  exact Equiv.piCongr_apply_apply (W := fun i => Fin (b i)) (Z := fun z => Fin (d z)) (e.trans g) (fun i => (f i).trans (h (e i))) x i

/-- Enumeration transport composes with the actual dependent-sum bijections. -/
theorem sumCode_comp {n m k : Nat} {b : Fin n → Nat} {c : Fin m → Nat}
    {d : Fin k → Nat} (e : Fin n ≃ Fin m) (g : Fin m ≃ Fin k)
    (f : ∀ i, Fin (b i) ≃ Fin (c (e i)))
    (h : ∀ j, Fin (c j) ≃ Fin (d (g j))) :
    (sumCode b).map (sumCode d) (sumEquiv (e.trans g) (fun i => (f i).trans (h (e i)))) =
      ((sumCode b).map (sumCode c) (sumEquiv e f)).trans
        ((sumCode c).map (sumCode d) (sumEquiv g h)) := by
  rw [sumEquiv_comp, Enumeration.map_comp]

theorem productCode_comp {n m k : Nat} {b : Fin n → Nat} {c : Fin m → Nat}
    {d : Fin k → Nat} (e : Fin n ≃ Fin m) (g : Fin m ≃ Fin k)
    (f : ∀ i, Fin (b i) ≃ Fin (c (e i)))
    (h : ∀ j, Fin (c j) ≃ Fin (d (g j))) :
    (productCode b).map (productCode d)
        (productEquiv (e.trans g) (fun i => (f i).trans (h (e i)))) =
      ((productCode b).map (productCode c) (productEquiv e f)).trans
        ((productCode c).map (productCode d) (productEquiv g h)) := by
  rw [productEquiv_comp, Enumeration.map_comp]

/-- This is a small tagged extension, not closure under arbitrary groupoid families. -/
inductive LargerCode
  | finite (n : Nat)
  | universe

def largerDecode : LargerCode → Grpd.{0, 0}
  | .finite n => Grpd.of (Discrete (Fin n))
  | .universe => Grpd.of Code

end SquareKit.FiniteUniverse

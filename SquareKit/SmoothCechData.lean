import SquareKit.SmoothRepresentedCover
import SquareKit.SmoothManifoldActionComparison

/-! Independent ordinary smooth cocycles and complete local arrow families. -/
noncomputable section
open scoped Manifold ContDiff
namespace SquareKit.SmoothCech
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothRepresentedCover SmoothManifoldAction
open ManifoldRealization
variable {X : Sheaf topology Type} {I : Type} (A : Atlas X I)
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]

/-- Smooth local maps and forward labels are supplied before any sheaf descent. -/
structure Datum where
  localMap : ∀ i, External.SmoothMap (A.domain i) d M
  transition : ∀ i j, External.Labels (G := G) (A.pair i j)
    ((localMap i).restrict (A.left i j)) ((localMap j).restrict (A.right i j))
  diagonal : ∀ i (x : Points (A.domain i)),
    (transition i i).val ((show EuclideanOpen.Map _ _ from A.diagonal i) x) = 1
  cocycle : ∀ i j k (x : Points (A.triple i j k)),
    (transition i k).val ((show EuclideanOpen.Map _ _ from A.firstThird i j k) x) =
      (transition j k).val ((show EuclideanOpen.Map _ _ from A.secondThird i j k) x) *
        (transition i j).val ((show EuclideanOpen.Map _ _ from A.firstSecond i j k) x)

variable {A}

omit [TopologicalSpace G] [DiscreteTopology G] [IsManifold (modelWithCorners d) ∞ M] in
@[ext] theorem Datum.ext (p q : Datum (d := d) (G := G) (M := M) A)
    (hm : p.localMap = q.localMap) (ht : HEq p.transition q.transition) : p = q := by
  cases p
  cases q
  cases hm
  cases ht
  rfl

structure Hom (p q : Datum (d := d) (G := G) (M := M) A) where
  labels : ∀ i, External.Labels (G := G) (A.domain i) (p.localMap i) (q.localMap i)
  commutes : ∀ i j (x : Points (A.pair i j)),
    (q.transition i j).val x * (labels i).val ((show EuclideanOpen.Map _ _ from A.left i j) x) =
      (labels j).val ((show EuclideanOpen.Map _ _ from A.right i j) x) * (p.transition i j).val x

namespace Hom
variable {p q r : Datum (d := d) (G := G) (M := M) A}

omit [TopologicalSpace G] [DiscreteTopology G] [IsManifold (modelWithCorners d) ∞ M] in
@[ext] theorem ext (f g : Hom p q) (h : f.labels = g.labels) : f = g := by
  cases f
  cases g
  cases h
  rfl

def ident (p : Datum (d := d) (G := G) (M := M) A) : Hom p p where
  labels i := ⟨1, fun x => one_smul G _⟩
  commutes i j x := by change _ * 1 = 1 * _; simp

def comp (f : Hom p q) (g : Hom q r) : Hom p r where
  labels i := ⟨(g.labels i).val * (f.labels i).val, fun x => by
    change ((g.labels i).val x * (f.labels i).val x) • _ = _
    rw [mul_smul, (f.labels i).property, (g.labels i).property]⟩
  commutes i j x := by
    change (r.transition i j).val x * ((g.labels i).val _ * (f.labels i).val _) =
      ((g.labels j).val _ * (f.labels j).val _) * (p.transition i j).val x
    rw [← mul_assoc, g.commutes, mul_assoc, f.commutes, ← mul_assoc]

def inverse (f : Hom p q) : Hom q p where
  labels i := ⟨(f.labels i).val⁻¹, fun x => inv_smul_eq_iff.mpr ((f.labels i).property x).symm⟩
  commutes i j x := by
    change (p.transition i j).val x * ((f.labels i).val _)⁻¹ =
      ((f.labels j).val _)⁻¹ * (q.transition i j).val x
    apply (eq_inv_mul_iff_mul_eq).mpr
    rw [← mul_assoc, ← f.commutes, mul_inv_cancel_right]

/-- The displayed family retains the source coordinate and endpoint certificates. -/
def families (f : Hom p q) (i : I) :
    External.Family (G := G) (A.domain i) (p.localMap i) (q.localMap i) :=
  External.labelsEquiv _ _ (f.labels i)

omit [IsManifold (modelWithCorners d) ∞ M] in
theorem families_apply (f : Hom p q) (i : I) (x : Points (A.domain i)) :
    (f.families i).val x = ((f.labels i).val x, (p.localMap i).val x) := rfl

omit [IsManifold (modelWithCorners d) ∞ M] in
theorem families_injective : Function.Injective (fun f : Hom p q => f.families) := by
  intro f g h
  apply Hom.ext
  funext i
  exact (External.labelsEquiv _ _).injective (congrFun h i)

omit [TopologicalSpace G] [DiscreteTopology G] [IsManifold (modelWithCorners d) ∞ M] in
theorem ident_comp (f : Hom p q) : (ident p).comp f = f := by
  apply Hom.ext
  funext i
  apply Subtype.ext
  exact mul_one _

omit [TopologicalSpace G] [DiscreteTopology G] [IsManifold (modelWithCorners d) ∞ M] in
theorem comp_ident (f : Hom p q) : f.comp (ident q) = f := by
  apply Hom.ext
  funext i
  apply Subtype.ext
  exact one_mul _

omit [TopologicalSpace G] [DiscreteTopology G] [IsManifold (modelWithCorners d) ∞ M] in
theorem comp_assoc {s : Datum (d := d) (G := G) (M := M) A}
    (f : Hom p q) (g : Hom q r) (h : Hom r s) : (f.comp g).comp h = f.comp (g.comp h) := by
  apply Hom.ext
  funext i
  apply Subtype.ext
  exact (mul_assoc _ _ _).symm

omit [TopologicalSpace G] [DiscreteTopology G] [IsManifold (modelWithCorners d) ∞ M] in
theorem inverse_comp (f : Hom p q) : f.inverse.comp f = ident q := by
  apply Hom.ext
  funext i
  apply Subtype.ext
  exact mul_inv_cancel _

omit [TopologicalSpace G] [DiscreteTopology G] [IsManifold (modelWithCorners d) ∞ M] in
theorem comp_inverse (f : Hom p q) : f.comp f.inverse = ident p := by
  apply Hom.ext
  funext i
  apply Subtype.ext
  exact inv_mul_cancel _

end Hom
instance : Category (Datum (d := d) (G := G) (M := M) A) where
  Hom := Hom
  id := Hom.ident
  comp := Hom.comp
  id_comp := Hom.ident_comp
  comp_id := Hom.comp_ident
  assoc := Hom.comp_assoc

instance : Groupoid (Datum (d := d) (G := G) (M := M) A) where
  inv := Hom.inverse
  inv_comp := Hom.inverse_comp
  comp_inv := Hom.comp_inverse

end SquareKit.SmoothCech

import SquareKit.SmoothBundleMapsRealization

/-! Ordinary discrete principal bundles with varying actual total manifolds.
Objects are Type-sized manifolds; arrows are all existing smooth bundle maps.
No separation, countability or global triviality is required. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.SmoothPrincipalBundle
open CategoryTheory ManifoldRealization SmoothOpenSite
open scoped Manifold ContDiff

/-- Bundle the carrier and its structures, retaining the original ordinary data. -/
structure Ordinary (n : ℕ) (G B : Type) [Group G] [TopologicalSpace B]
    [ChartedSpace (Space n) B] where
  Total : Type
  [topology : TopologicalSpace Total]
  [charts : ChartedSpace (Space n) Total]
  [manifold : IsManifold (modelWithCorners n) ∞ Total]
  [action : MulAction G Total]
  bundle : Bundle (n := n) (G := G) (B := B) (E := Total)

attribute [instance] Ordinary.topology Ordinary.charts Ordinary.manifold Ordinary.action

namespace Ordinary
variable {n : ℕ} {G B : Type} [Group G] [TopologicalSpace B]
  [ChartedSpace (Space n) B]

/-- Existing independently supplied bundles enter without changing their total space. -/
def ofBundle {E : Type} [TopologicalSpace E] [ChartedSpace (Space n) E]
    [IsManifold (modelWithCorners n) ∞ E] [MulAction G E]
    (P : Bundle (n := n) (G := G) (B := B) (E := E)) : Ordinary n G B where
  Total := E
  bundle := P

instance : Category.{0} (Ordinary n G B) where
  Hom P Q := Map P.bundle Q.bundle
  id P := Map.ident P.bundle
  comp f g := f.comp g
  id_comp f := Map.ident_comp f
  comp_id f := Map.comp_ident f
  assoc _ _ _ := rfl

@[ext] theorem hom_ext {P Q : Ordinary n G B} (f g : P ⟶ Q)
    (h : f.toFun = g.toFun) : f = g := Map.ext f g h

@[simp] theorem id_apply (P : Ordinary n G B) (x : P.Total) :
    (𝟙 P : P ⟶ P).toFun x = x := rfl

@[simp] theorem comp_apply {P Q R : Ordinary n G B} (f : P ⟶ Q) (g : Q ⟶ R)
    (x : P.Total) : (f ≫ g).toFun x = g.toFun (f.toFun x) := rfl

variable [TopologicalSpace G] [DiscreteTopology G] [IsManifold (modelWithCorners n) ∞ B]

/-- Invertibility follows from principality and full faithfulness. -/
instance : Groupoid (Ordinary n G B) where
  inv f := f.inverse
  inv_comp f := f.inverse_comp
  comp_inv f := f.comp_inverse

def realization : Ordinary n G B ⥤ SheafTorsor.Torsor (locallyConstantGroup G) (object n B) where
  obj P := P.bundle.realizedTorsor
  map f := f.realizedArrow
  map_id _ := Map.realizedArrow_ident
  map_comp f g := Map.realizedArrow_comp f g

/-- The all-map correspondence is the existing ordinary/sheaf comparison. -/
def realizationFullyFaithful : (realization (n := n) (G := G) (B := B)).FullyFaithful where
  preimage h := mapEquiv.symm h
  map_preimage h := mapEquiv.apply_symm_apply h
  preimage_map f := mapEquiv.symm_apply_apply f

instance : (realization (n := n) (G := G) (B := B)).Full := realizationFullyFaithful.full
instance : (realization (n := n) (G := G) (B := B)).Faithful := realizationFullyFaithful.faithful

end Ordinary
end SquareKit.SmoothPrincipalBundle

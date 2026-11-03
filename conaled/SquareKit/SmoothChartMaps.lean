import SquareKit.SmoothChartRealization

/-! Experimental chartwise ordinary maps and their realized sheaf maps. -/
noncomputable section
open CategoryTheory
namespace SquareKit.EuclideanOpen.Charts
variable {M N P : Type} (A : Charts M) (B : Charts N) (C : Charts P)

/-- A map whose restriction to each source chart lands in a chosen target chart. -/
structure Map where
  point : M → N
  index : A.Index → B.Index
  coordinate : ∀ i, A.domain i ⟶ B.domain (index i)
  agreement : ∀ i x, point (A.coordinate i x) =
    B.coordinate (index i) ((show EuclideanOpen.Map _ _ from coordinate i) x)

namespace Map
variable {A B C}

def ident (A : Charts M) : Map A A := ⟨id, id, fun _ => 𝟙 _, fun _ _ => rfl⟩

def comp (f : Map A B) (g : Map B C) : Map A C where
  point := g.point ∘ f.point
  index := g.index ∘ f.index
  coordinate i := f.coordinate i ≫ g.coordinate (f.index i)
  agreement i x := by rw [Function.comp_apply, f.agreement, g.agreement]; rfl

def relation (f : Map A B) (r : A.Relation) : B.Relation where
  first := f.index r.first
  second := f.index r.second
  domain := r.domain
  left := r.left ≫ f.coordinate r.first
  right := r.right ≫ f.coordinate r.second
  agreement x := by
    change B.coordinate _ ((show EuclideanOpen.Map _ _ from f.coordinate r.first) ((show EuclideanOpen.Map _ _ from r.left) x)) =
      B.coordinate _ ((show EuclideanOpen.Map _ _ from f.coordinate r.second) ((show EuclideanOpen.Map _ _ from r.right) x))
    rw [← f.agreement, ← f.agreement, r.agreement]

def realize (f : Map A B) : A.realization ⟶ B.realization :=
  A.descend (fun i => embedding.map (f.coordinate i) ≫ B.chart (f.index i)) (fun r => by
    simpa only [relation, ← Category.assoc, ← Functor.map_comp] using B.chart_compatible (f.relation r))

@[reassoc (attr := simp)] theorem chart_realize (f : Map A B) (i : A.Index) :
    A.chart i ≫ f.realize = embedding.map (f.coordinate i) ≫ B.chart (f.index i) :=
  A.chart_descend _ _ i

theorem realize_ident : (ident A).realize = 𝟙 A.realization := by
  apply A.hom_ext
  intro i
  simp [ident]

theorem realize_comp (f : Map A B) (g : Map B C) :
    (f.comp g).realize = f.realize ≫ g.realize := by
  apply A.hom_ext
  intro i
  simp [comp, Functor.map_comp, Category.assoc]

/-- Different chart choices for the same ordinary function induce the same map. -/
theorem realize_eq (f g : Map A B) (h : f.point = g.point) : f.realize = g.realize := by
  apply A.hom_ext
  intro i
  rw [chart_realize, chart_realize]
  apply B.chart_compatible
    (⟨f.index i, g.index i, A.domain i, f.coordinate i, g.coordinate i, ?_⟩ : B.Relation)
  intro x
  rw [← f.agreement, ← g.agreement, h]

end Map
end SquareKit.EuclideanOpen.Charts

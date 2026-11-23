import SquareKit.SmoothOpenPullback
import SquareKit.SmoothCoordinateAlgebra
import SquareKit.SmoothManifoldFullFaithfulness

/-! Principal supports covering a compatible locus at an arbitrary presentation stage.
Real points establish the covering predicate; all lifted maps retain the full algebra.
-/
noncomputable section
set_option autoImplicit false
namespace SquareKit.SmoothTransverseStageCover
open CategoryTheory Opposite SmoothAlgebra SmoothPresentationSite
open SmoothAlgebra.Localization EuclideanOpen

variable {n : ℕ} (A : Code) (u : Hom (Free n) (Carrier A))

/-- Evaluate a smooth operation after a real reduction of an arbitrary stage. -/
theorem real_coordinate (h : Hom (Carrier A) ℝ) (q : Free n) :
    h (u q) = q.val (fun i => h (u (generator i))) := by
  exact (congrArg (fun k : Hom (Free n) ℝ => k q) (evaluate_unique (h.comp u))).symm

/-- Supports need cover only the locus known to contain the stage's real reductions. -/
theorem covers_of_locus {I : Type} (S : Set (Fin n → ℝ)) (q : I → Free n)
    (hu : ∀ h : Hom (Carrier A) ℝ, (fun i => h (u (generator i))) ∈ S)
    (hq : ∀ x ∈ S, ∃ i, (q i).val x ≠ 0) :
    OpenCover.Covers (fun i => u (q i)) := by
  intro h
  obtain ⟨i, hi⟩ := hq _ (hu h)
  exact ⟨i, by rwa [real_coordinate]⟩

theorem locus_covering {I : Type} (S : Set (Fin n → ℝ)) (q : I → Free n)
    (hu : ∀ h : Hom (Carrier A) ℝ, (fun i => h (u (generator i))) ∈ S)
    (hq : ∀ x ∈ S, ∃ i, (q i).val x ≠ 0) :
    principalSieve A (fun i => u (q i)) ∈ SmoothOpenSite.topology (op A) :=
  SmoothOpenSite.principal_covering A _ (covers_of_locus A u S q hu hq)

/-- The full coordinate map factors into the principal support after localization. -/
def localCoordinates (q : Free n) :
    Hom (Principal q) (Carrier (localization A (u q))) :=
  principalLift q ((localizationBase A (u q)).comp u)
    (PresentedLocalization.atBase_isUnit A.equations (u q))

theorem localCoordinates_base (q : Free n) :
    (localCoordinates A u q).comp (principalBase q) =
      (localizationBase A (u q)).comp u :=
  lift_base _ _ (fun _ => PresentedLocalization.atBase_isUnit A.equations (u q))

theorem localCoordinates_generator (q : Free n) (i : Fin n) :
    localCoordinates A u q (principalBase q (generator i)) =
      smoothMap (localizationBase A (u q)) (u (generator i)) :=
  congrArg (fun k : Hom (Free n) (Carrier (localization A (u q))) => k (generator i))
    (localCoordinates_base A u q)

section Compatible
variable {U V W : Domain} (f : U ⟶ W) (g : V ⟶ W) (B : Code)
  (a : Hom (Principal U.defining) (Carrier B))
  (b : Hom (Principal V.defining) (Carrier B))

def coordinatePair : Hom (Free (U.dimension + V.dimension)) (Carrier B) :=
  SmoothAlgebra.Coordinates.pair (a.comp (principalBase U.defining))
    (b.comp (principalBase V.defining))

theorem real_pair (h : Hom (Carrier B) ℝ) :
    (fun i => h (coordinatePair B a b (generator i))) =
      Fin.addCases (realPoints U.defining (h.comp a)).val
        (realPoints V.defining (h.comp b)).val := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [coordinatePair, SmoothAlgebra.Coordinates.pair, evaluate_generator,
      Fin.addCases_left]
    rfl
  · simp only [coordinatePair, SmoothAlgebra.Coordinates.pair, evaluate_generator,
      Fin.addCases_right]
    rfl

theorem real_compatible
    (hc : a.comp (Localization.pullback f) = b.comp (Localization.pullback g))
    (h : Hom (Carrier B) ℝ) :
    (show Map U W from f) (realPoints U.defining (h.comp a)) =
      (show Map V W from g) (realPoints V.defining (h.comp b)) := by
  rw [← real_map, ← real_map]
  congr 1
  simpa only [Hom.comp_assoc] using congrArg (Hom.comp h) hc

/-- The family covers the equal-image locus, not necessarily the ambient product. -/
theorem compatible_cover {I : Type} (q : I → Free (U.dimension + V.dimension))
    (hc : a.comp (Localization.pullback f) = b.comp (Localization.pullback g))
    (hq : ∀ x : Points U, ∀ y : Points V,
      (show Map U W from f) x = (show Map V W from g) y →
      ∃ i, (q i).val (Fin.addCases x.val y.val) ≠ 0) :
    OpenCover.Covers (fun i => coordinatePair B a b (q i)) := by
  intro h
  obtain ⟨i, hi⟩ := hq _ _ (real_compatible f g B a b hc h)
  refine ⟨i, ?_⟩
  rw [real_coordinate, real_pair]
  exact hi

end Compatible

end SquareKit.SmoothTransverseStageCover

namespace SquareKit.ManifoldRealization.ChartFamily
open CategoryTheory Opposite SmoothAlgebra SmoothPresentationSite EuclideanOpen SmoothOpenSite
open SmoothAlgebra.Localization
open scoped Manifold ContDiff
variable {m n : ℕ} {M N : Type} [TopologicalSpace M] [ChartedSpace (Space m) M]
  [TopologicalSpace N] [ChartedSpace (Space n) N]
  (A : ChartFamily m M) (B : ChartFamily n N)

/-- Restriction to a real reduction of an arbitrary finitely presented stage. -/
def realReduction (V : Code) (x : A.realization.obj.obj (op (op V)))
    (h : Hom (Carrier V) ℝ) : M :=
  A.charts.realEquiv A.atlas.covers
    (A.realization.obj.map (show op (free 0) ⟶ op V from
      (show V ⟶ free 0 from DualExtension.realHom.comp h).op).op x)

set_option backward.isDefEq.respectTransparency false in
theorem realReduction_chart (i : A.Index) (V : Code)
    (a : Hom (Principal (A.charts.domain i).defining) (Carrier V))
    (h : Hom (Carrier V) ℝ) :
    A.realReduction V ((A.charts.chart i).hom.app (op (op V))
      (show code (A.charts.domain i) ⟶ V from a).op) h =
    chartPoint (A.chart i) (realPoints (A.charts.domain i).defining (h.comp a)) := by
  unfold realReduction
  rw [← NatTrans.naturality_apply]
  change A.charts.realEquiv A.atlas.covers
    (realSections.map (A.charts.chart i)
      (show code (A.charts.domain i) ⟶ free 0 from
        (DualExtension.realHom.comp h).comp a).op) = _
  refine (A.charts.realEquiv_chart A.atlas.covers i _).trans ?_
  congr 1

set_option backward.isDefEq.respectTransparency false in
theorem realReduction_interpret (f : M → N)
    (hf : ContMDiff (Model m) (Model n) ∞ f) (V : Code)
    (x : A.realization.obj.obj (op (op V))) (h : Hom (Carrier V) ℝ) :
    B.realReduction V ((A.interpret B f hf).hom.app (op (op V)) x) h =
      f (A.realReduction V x h) := by
  unfold realReduction
  rw [← NatTrans.naturality_apply]
  have he := congrFun (A.reconstruct_interpret B f hf)
    (A.charts.realEquiv A.atlas.covers
      (A.realization.obj.map (show op (free 0) ⟶ op V from
        (show V ⟶ free 0 from DualExtension.realHom.comp h).op).op x))
  change B.charts.realEquiv B.atlas.covers
    ((A.interpret B f hf).hom.app _
      ((A.charts.realEquiv A.atlas.covers).symm
        (A.charts.realEquiv A.atlas.covers _))) = _ at he
  simpa only [Equiv.symm_apply_apply] using he

end SquareKit.ManifoldRealization.ChartFamily

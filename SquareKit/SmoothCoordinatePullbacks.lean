import SquareKit.SmoothCoordinateAlgebra
import SquareKit.SmoothOpenScalar
import SquareKit.SmoothGeometricDual
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! Coordinate products and coordinate zero fibers as actual pullback squares
of sheaves. The lift formulas work for arbitrary sheaf test objects. -/
noncomputable section
namespace SquareKit.SmoothOpenSite.Coordinates
open CategoryTheory CategoryTheory.Limits Opposite SmoothAlgebra SmoothPresentationSite SmoothGeometricKL

variable {n k : ℕ} {F G : Sheaf topology Type}

def first (n k : ℕ) : scalarPower (n+k) ⟶ scalarPower n :=
  tuple (fun i => projection (n+k) (Fin.castAdd k i))

def last (n k : ℕ) : scalarPower (n+k) ⟶ scalarPower k :=
  tuple (fun i => projection (n+k) (Fin.natAdd n i))

def join (u : F ⟶ scalarPower n) (v : F ⟶ scalarPower k) : F ⟶ scalarPower (n+k) :=
  tuple (Fin.addCases (fun i => u ≫ projection n i) (fun i => v ≫ projection k i))

def toPoint (n : ℕ) : scalarPower n ⟶ scalarPower 0 := tuple Fin.elim0

def zero (k : ℕ) : scalarPower 0 ⟶ scalarPower k :=
  tuple (fun _ => operation (constant 0 0))

def insertZero (n k : ℕ) : scalarPower n ⟶ scalarPower (n+k) :=
  join (𝟙 _) (toPoint n ≫ zero k)

theorem join_apply_left (u : F ⟶ scalarPower n) (v : F ⟶ scalarPower k)
    (X : Siteᵒᵖ) (x : F.obj.obj X) (i : Fin n) :
    (join u v).hom.app X x (Fin.castAdd k i) = u.hom.app X x i := by
  change ((Fin.addCases (motive := fun _ => F ⟶ scalar) (fun j => u ≫ projection n j) (fun j => v ≫ projection k j)
    (Fin.castAdd k i)).hom.app X) x = _
  rw [Fin.addCases_left]
  rfl

theorem join_apply_right (u : F ⟶ scalarPower n) (v : F ⟶ scalarPower k)
    (X : Siteᵒᵖ) (x : F.obj.obj X) (i : Fin k) :
    (join u v).hom.app X x (Fin.natAdd n i) = v.hom.app X x i := by
  change ((Fin.addCases (motive := fun _ => F ⟶ scalar) (fun j => u ≫ projection n j) (fun j => v ≫ projection k j)
    (Fin.natAdd n i)).hom.app X) x = _
  rw [Fin.addCases_right]
  rfl

@[simp] theorem join_first (u : F ⟶ scalarPower n) (v : F ⟶ scalarPower k) :
    join u v ≫ first n k = u := by
  ext X x
  funext i
  exact join_apply_left u v X x i

@[simp] theorem join_last (u : F ⟶ scalarPower n) (v : F ⟶ scalarPower k) :
    join u v ≫ last n k = v := by
  ext X x
  funext i
  exact join_apply_right u v X x i

theorem join_unique (u : F ⟶ scalarPower n) (v : F ⟶ scalarPower k)
    (w : F ⟶ scalarPower (n+k)) (hl : w ≫ first n k = u) (hr : w ≫ last n k = v) :
    w = join u v := by
  apply Fan.IsLimit.hom_ext (powerIsLimit (n+k))
  intro i
  ext X x
  change w.hom.app X x i = (join u v).hom.app X x i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact (congrArg (fun f : F ⟶ scalarPower n => f.hom.app X x j) hl).trans
      (join_apply_left u v X x j).symm
  · exact (congrArg (fun f : F ⟶ scalarPower k => f.hom.app X x j) hr).trans
      (join_apply_right u v X x j).symm

theorem join_precomp (h : G ⟶ F) (u : F ⟶ scalarPower n) (v : F ⟶ scalarPower k) :
    h ≫ join u v = join (h ≫ u) (h ≫ v) := by
  apply join_unique <;> simp

theorem point_unique (u v : F ⟶ scalarPower 0) : u = v := by
  ext X x
  funext i
  exact Fin.elim0 i

theorem product_isPullback (n k : ℕ) :
    IsPullback (first n k) (last n k) (toPoint n) (toPoint k) := by
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk (point_unique _ _)
    (fun c => join c.fst c.snd) (fun c => join_first _ _) (fun c => join_last _ _)
    (fun c w hl hr => join_unique c.fst c.snd w hl hr))

@[simp] theorem insertZero_first (n k : ℕ) : insertZero n k ≫ first n k = 𝟙 _ :=
  join_first _ _

theorem insertZero_last (n k : ℕ) : insertZero n k ≫ last n k = toPoint n ≫ zero k :=
  join_last _ _

/-- Keep the free block; compatibility ensures that the other block is zero. -/
def fiberLift (u : F ⟶ scalarPower (n+k)) : F ⟶ scalarPower n := u ≫ first n k

theorem fiberLift_insertZero (u : F ⟶ scalarPower (n+k)) (v : F ⟶ scalarPower 0)
    (hc : u ≫ last n k = v ≫ zero k) : fiberLift u ≫ insertZero n k = u := by
  apply (product_isPullback n k).hom_ext
  · simp [fiberLift]
  · rw [Category.assoc, insertZero_last, ← Category.assoc,
      point_unique (fiberLift u ≫ toPoint n) v]
    exact hc.symm

theorem fiberLift_toPoint (u : F ⟶ scalarPower (n+k)) (v : F ⟶ scalarPower 0) :
    fiberLift u ≫ toPoint n = v := point_unique _ _

theorem fiberLift_unique (u : F ⟶ scalarPower (n+k)) (w : F ⟶ scalarPower n)
    (hw : w ≫ insertZero n k = u) : w = fiberLift u := by
  rw [fiberLift, ← hw, Category.assoc, insertZero_first, Category.comp_id]

theorem zero_fiber_isPullback (n k : ℕ) :
    IsPullback (insertZero n k) (toPoint n) (last n k) (zero k) := by
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk (insertZero_last n k)
    (fun c => fiberLift c.fst) (fun c => fiberLift_insertZero c.fst c.snd c.condition)
    (fun c => fiberLift_toPoint c.fst c.snd) (fun c w hw _ => fiberLift_unique c.fst w hw))

theorem fiberLift_precomp (h : G ⟶ F) (u : F ⟶ scalarPower (n+k)) :
    h ≫ fiberLift u = fiberLift (h ≫ u) := (Category.assoc _ _ _).symm

theorem first_apply (n k : ℕ) (A : Code) (x : Fin (n+k) → Carrier A) (i : Fin n) :
    (first n k).hom.app (atStage A) x i = x (Fin.castAdd k i) := rfl

theorem last_apply (n k : ℕ) (A : Code) (x : Fin (n+k) → Carrier A) (i : Fin k) :
    (last n k).hom.app (atStage A) x i = x (Fin.natAdd n i) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem insertZero_apply (n k : ℕ) (A : Code) (x : Fin n → Carrier A) :
    (insertZero n k).hom.app (atStage A) x = Fin.addCases x (fun _ => 0) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · change (join (𝟙 _) (toPoint n ≫ zero k)).hom.app (atStage A) x (Fin.castAdd k j) = _
    rw [join_apply_left, Fin.addCases_left]
    rfl
  · change (join (𝟙 _) (toPoint n ≫ zero k)).hom.app (atStage A) x (Fin.natAdd n j) = _
    rw [join_apply_right, Fin.addCases_right]
    change act (constant 0 0) _ = 0
    simp [Structure.constant]

/-- Restriction of the explicit inverse at every presentation-stage arrow. -/
theorem fiberLift_stage (u : F ⟶ scalarPower (n+k)) {A B : Code} (f : A ⟶ B)
    (x : F.obj.obj (atStage A)) :
    (fiberLift u).hom.app (atStage B) (F.obj.map (stageMap f) x) =
      fun i => smoothMap f ((fiberLift u).hom.app (atStage A) x i) := by
  exact congrArg (fun h => h x) ((fiberLift u).hom.naturality (stageMap f))

theorem fiberLift_stage_comp (u : F ⟶ scalarPower (n+k)) {A B C : Code}
    (f : A ⟶ B) (g : B ⟶ C) (x : F.obj.obj (atStage A)) :
    (fiberLift u).hom.app (atStage C) (F.obj.map (stageMap (f ≫ g)) x) =
      fun i => smoothMap g (smoothMap f ((fiberLift u).hom.app (atStage A) x i)) :=
  fiberLift_stage u (f ≫ g) x

theorem fiberLift_stage_id (u : F ⟶ scalarPower (n+k)) (A : Code)
    (x : F.obj.obj (atStage A)) :
    (fiberLift u).hom.app (atStage A) (F.obj.map (stageMap (𝟙 A)) x) =
      (fiberLift u).hom.app (atStage A) x := fiberLift_stage u (𝟙 A) x

theorem first_stage (n k : ℕ) {A B : Code} (f : A ⟶ B) (x : Fin (n+k) → Carrier A) :
    (first n k).hom.app (atStage B) (fun i => smoothMap f (x i)) =
      fun i => smoothMap f ((first n k).hom.app (atStage A) x i) := rfl

theorem last_stage (n k : ℕ) {A B : Code} (f : A ⟶ B) (x : Fin (n+k) → Carrier A) :
    (last n k).hom.app (atStage B) (fun i => smoothMap f (x i)) =
      fun i => smoothMap f ((last n k).hom.app (atStage A) x i) := rfl

theorem insertZero_stage (n k : ℕ) {A B : Code} (f : A ⟶ B) (x : Fin n → Carrier A) :
    (insertZero n k).hom.app (atStage B) (fun i => smoothMap f (x i)) =
      fun i => smoothMap f ((insertZero n k).hom.app (atStage A) x i) :=
  congrArg (fun h => h x) ((insertZero n k).hom.naturality (stageMap f))

/-- The represented coordinate projection is the actual free-algebra map. -/
theorem first_algebra (n k : ℕ) (A : Code) (x : Fin (n+k) → Carrier A) :
    (first n k).hom.app (atStage A) x =
      freeEquiv n ((evaluate x).comp (SmoothAlgebra.Coordinates.left n k)) := by
  funext i
  exact (evaluate_generator x (Fin.castAdd k i)).symm

theorem last_algebra (n k : ℕ) (A : Code) (x : Fin (n+k) → Carrier A) :
    (last n k).hom.app (atStage A) x =
      freeEquiv k ((evaluate x).comp (SmoothAlgebra.Coordinates.right n k)) := by
  funext i
  exact (evaluate_generator x (Fin.natAdd n i)).symm

end SquareKit.SmoothOpenSite.Coordinates

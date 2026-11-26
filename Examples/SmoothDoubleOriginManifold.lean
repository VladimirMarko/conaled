import SquareKit.SmoothLocalHomeomorph
import Mathlib.Topology.Gluing

/-! An ordinary smooth line with two inseparable origins. -/
noncomputable section
set_option autoImplicit false
namespace Examples.SmoothDoubleOriginManifold
open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Set
open SquareKit.ManifoldRealization
open scoped Manifold ContDiff

def overlap (i j : Bool) : Opens (Space 1) :=
  ⟨{x | i = j ∨ x ≠ 0}, by
    by_cases h : i = j
    · simp [h]
    · simp only [h, false_or]
      exact isClosed_singleton.isOpen_compl⟩

@[simp] theorem mem_overlap (i j : Bool) (x : Space 1) :
    x ∈ overlap i j ↔ i = j ∨ x ≠ 0 := Iff.rfl

def core : TopCat.GlueData.MkCore where
  J := Bool
  U _ := TopCat.of (Space 1)
  V := overlap
  t i j := TopCat.ofHom ⟨fun x => ⟨x.val, x.property.elim (fun h => Or.inl h.symm) Or.inr⟩,
    by fun_prop⟩
  V_id i := by ext x; simp
  t_id i := by funext x; rfl
  t_inter := by
    intro i j k x hx
    change j = k ∨ x.val ≠ 0
    change i = k ∨ x.val ≠ 0 at hx
    rcases x.property with hij | hn
    · simpa [← hij] using hx
    · exact Or.inr hn
  cocycle _ _ _ _ _ := rfl

def glue : TopCat.GlueData := TopCat.GlueData.mk' core
abbrev D : Type := glue.toGlueData.glued

def inclusion (i : Bool) : Space 1 → D := glue.toGlueData.ι i

def coordinateMap : glue.toGlueData.glued ⟶ TopCat.of (Space 1) :=
  Multicoequalizer.desc _ _ (fun _ => 𝟙 _) (by rintro ⟨i,j⟩; ext x; rfl)

def coordinate : D → Space 1 := coordinateMap

@[simp] theorem coordinate_inclusion (i : Bool) (x : Space 1) :
    coordinate (inclusion i x) = x := by
  have h : glue.toGlueData.ι i ≫ coordinateMap = 𝟙 _ :=
    Multicoequalizer.π_desc _ _ _ _ _
  exact congrArg (fun f => f x) h

theorem inclusion_eq_iff (i j : Bool) (x y : Space 1) :
    inclusion i x = inclusion j y ↔ x = y ∧ (i = j ∨ x ≠ 0) := by
  rw [show inclusion i x = inclusion j y ↔ _ from glue.ι_eq_iff_rel i j x y]
  change (∃ z : overlap i j, z.val = x ∧ z.val = y) ↔ _
  constructor
  · rintro ⟨z, rfl, rfl⟩
    exact ⟨rfl, z.property⟩
  · rintro ⟨rfl, hx⟩
    exact ⟨⟨x, hx⟩, rfl, rfl⟩

def origin (i : Bool) : D := inclusion i 0

theorem origins_ne : origin false ≠ origin true := by
  simp [origin, inclusion_eq_iff]

theorem continuous_inclusion (i : Bool) : Continuous (inclusion i) :=
  (glue.ι_isOpenEmbedding i).continuous

theorem continuous_coordinate : Continuous coordinate := coordinateMap.hom.continuous

def sheet (i : Bool) : OpenPartialHomeomorph D (Space 1) where
  toFun := coordinate
  invFun := inclusion i
  source := Set.range (inclusion i)
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' x _ := ⟨x, rfl⟩
  left_inv' := by rintro _ ⟨x, rfl⟩; simp
  right_inv' x _ := coordinate_inclusion i x
  open_source := (glue.ι_isOpenEmbedding i).isOpen_range
  open_target := isOpen_univ
  continuousOn_toFun := continuous_coordinate.continuousOn
  continuousOn_invFun := (continuous_inclusion i).continuousOn

theorem exists_sheet (x : D) : ∃ i : Bool, x ∈ (sheet i).source := by
  obtain ⟨i, y, hy⟩ := glue.ι_jointly_surjective x
  exact ⟨i, y, hy⟩

def sheets : SquareKit.SmoothLocalHomeomorph.ProjectionSheets coordinate where
  sheet x := sheet (exists_sheet x).choose
  mem_source x := (exists_sheet x).choose_spec
  projection _ := rfl

instance : ChartedSpace (Space 1) D := sheets.chartedSpace
instance : IsManifold (modelWithCorners 1) ∞ D := sheets.isManifold

theorem smooth_coordinate : ContMDiff (modelWithCorners 1) (modelWithCorners 1) ∞ coordinate :=
  sheets.smooth_proj

theorem smooth_inclusion (i : Bool) :
    ContMDiff (modelWithCorners 1) (modelWithCorners 1) ∞ (inclusion i) := by
  apply sheets.smooth_of_proj _ (continuous_inclusion i)
  have h : coordinate ∘ inclusion i = id := funext (coordinate_inclusion i)
  rw [h]
  exact contMDiff_id

theorem not_t2Space : ¬ T2Space D := by
  intro h
  let := h
  have he : inclusion false = inclusion true :=
    Continuous.ext_on (dense_compl_singleton (0 : Space 1))
      (continuous_inclusion false) (continuous_inclusion true) (by
        intro x hx
        exact (inclusion_eq_iff false true x x).mpr ⟨rfl, Or.inr hx⟩)
  exact origins_ne (congrFun he 0)

end Examples.SmoothDoubleOriginManifold

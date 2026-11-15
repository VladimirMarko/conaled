import Applications.GroupActions.Schreier
import Mathlib.Data.List.FinRange

/-! Finite export of directed labelled Schreier edges. Vertex IDs are an explicit
bijection; generator indices are retained even when their group labels coincide. -/

open Quiver
namespace Schreier.FiniteDiagram

variable {G X : Type*} [Group G] [MulAction G X] {n m : Nat}

/-- An exported mathematical row. Display labels are added only by serialization. -/
@[ext] structure Row (G : Type*) (n m : Nat) where
  source : Fin n
  target : Fin n
  generator : Fin m
  label : G
  deriving DecidableEq

variable (vertices : Fin n ≃ X) (generators : Fin m → G)

/-- Exactly one row per source and generator index, without deduplication. -/
def row (v : Fin n) (s : Fin m) : Row G n m :=
  ⟨v, vertices.symm (generators s • vertices v), s, generators s⟩

def rows : List (Row G n m) :=
  (List.finRange n).flatMap fun v => (List.finRange m).map (row vertices generators v)

@[simp] theorem mem_rows (r : Row G n m) : r ∈ rows vertices generators ↔
    ∃ v s, row vertices generators v s = r := by
  simp [rows]

@[simp] theorem row_mem (v : Fin n) (s : Fin m) :
    row vertices generators v s ∈ rows vertices generators := by
  exact (mem_rows vertices generators _).mpr ⟨v, s, rfl⟩

/-- The pair ID is unique even if generator labels or endpoints agree. -/
theorem row_injective : Function.Injective (fun p : Fin n × Fin m =>
    row vertices generators p.1 p.2) := by
  intro p q h
  exact Prod.ext (congrArg Row.source h) (congrArg Row.generator h)

/-- Decoding the target recovers the original action, not an unlabelled adjacency. -/
@[simp] theorem target_correct (v : Fin n) (s : Fin m) :
    vertices (row vertices generators v s).target = generators s • vertices v :=
  vertices.apply_symm_apply _

/-- Every exported row is an actual labelled Mathlib edge with the same index. -/
def edge (v : Fin n) (s : Fin m) :
    @Quiver.Hom (SchreierGraph X generators) _ ⟨vertices v⟩
      ⟨vertices (row vertices generators v s).target⟩ :=
  ⟨s, by apply SchreierGraph.ext; exact (target_correct vertices generators v s).symm⟩

/-- Exact correspondence with the original edge subtype, for every endpoint pair
and generator index. Equal group values do not identify distinct indices. -/
theorem edge_iff_row (v w : Fin n) (s : Fin m) :
    (∃ e : @Quiver.Hom (SchreierGraph X generators) _ ⟨vertices v⟩ ⟨vertices w⟩,
      e.val = s) ↔
    (⟨v, w, s, generators s⟩ : Row G n m) ∈ rows vertices generators := by
  constructor
  · rintro ⟨⟨t, ht⟩, rfl⟩
    apply (mem_rows vertices generators _).mpr
    refine ⟨v, t, ?_⟩
    have h := congrArg SchreierGraph.toVertex ht
    change generators t • vertices v = vertices w at h
    simp [row, h]
  · intro h
    obtain ⟨a, b, hab⟩ := (mem_rows vertices generators _).mp h
    have ha : a = v := congrArg Row.source hab
    have hb : b = s := congrArg Row.generator hab
    subst a; subst b
    refine ⟨⟨s, ?_⟩, rfl⟩
    apply SchreierGraph.ext
    have ht := congrArg (fun r : Row G n m => vertices r.target) hab
    change generators s • vertices v = vertices w
    simpa using ht

/-- The existing path interpreter reads exactly the exported group label. -/
theorem interpreted_label (v : Fin n) (s : Fin m) :
    ((edgeInterpretation generators).map (.inl (edge vertices generators v s))).hom =
      (row vertices generators v s).label := rfl

/-- There are n*m rows, including loops and repeated values. -/
theorem length_rows : (rows vertices generators).length = n * m := by
  simp [rows, List.length_flatMap, List.sum_replicate]

end Schreier.FiniteDiagram

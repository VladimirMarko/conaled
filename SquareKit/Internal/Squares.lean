import SquareKit.Internal.Graph
import SquareKit.RelationalCategory
import SquareKit.RelationComposition

/-! Comparison of interpreted graph composition with existing square pasting.
Experimental Set graph slice of issue #38. Scope and remaining model work:
`docs/research/internal-languages-lean.md`, Implemented Set graph slice.
-/
namespace SquareKit.Internal.Graph
universe u
open Squares Relational

/-- Existential graph composition retains its intermediate witness in Prop. -/
def composedGraph (A : Rep.{u}) {T : Type u} (d : A.S → T) : RelRep.{u} :=
  existential (graph A).Rel (fun s t => d s = t)

/-- Equality orientation follows `Relational.graph`, not the internal sequent. -/
theorem composedGraph_iff (A : Rep.{u}) {T : Type u} (d : A.S → T) (r : A.R) (t : T) :
    (composedGraph A d).Rel r t ↔ (graph (A.after d)).Rel r t := by
  have interpreted := inSet A.decode d r t
  constructor
  · rintro ⟨s, hs, ht⟩
    exact (interpreted.mp ⟨s, hs.symm, ht.symm⟩).symm
  · intro h
    obtain ⟨s, hs, ht⟩ := interpreted.mpr h.symm
    exact ⟨s, hs.symm, ht.symm⟩

-- Preserve the #38 qualified caller name for the shared transport operation.
export Relational (transportRelations)

/-- Pasting preserves existentially composed predicates before comparison. -/
def existentialVertical {A B : Rep.{u}} {AS BS : Type u}
    (da : A.S → AS) (db : B.S → BS) (f : Square A B)
    (g : Square (Rep.mk A.S AS da) (Rep.mk B.S BS db))
    (middle : ∀ x, f.spec x = g.impl x) :
    RelSquare (composedGraph A da) (composedGraph B db) :=
  existentialSquare (ofSquare f) (ofSquare g) middle

/-- Principal verification seam: both relations are transported using the
interpreted derivation, and extensionality compares both maps. -/
theorem vertical_comparison {A B : Rep.{u}} {AS BS : Type u}
    (da : A.S → AS) (db : B.S → BS) (f : Square A B)
    (g : Square (Rep.mk A.S AS da) (Rep.mk B.S BS db))
    (middle : ∀ x, f.spec x = g.impl x) :
    transportRelations (existentialVertical da db f g middle)
      (graph (A.after da)).Rel (graph (B.after db)).Rel
      (composedGraph_iff A da) (composedGraph_iff B db) =
      ofSquare (vertical da db f g middle) :=
  RelSquare.ext (fun _ => rfl) (fun _ => rfl)

/-- Horizontal graph composition is a separate use of the existing map law. -/
theorem horizontal_comparison {A B C : Rep.{u}} (g : Square B C) (f : Square A B) :
    ofSquare (Squares.compose g f) = Relational.compose (ofSquare g) (ofSquare f) :=
  RelationalCategory.graphMap_laws.comp (Comma.Exact.ofSquare g) (Comma.Exact.ofSquare f)
end SquareKit.Internal.Graph

import SquareKit.ListFusion
import SquareKit.Relations

/-!
# A minimal abstract set interface

Operators, independent membership observations, and validity laws are separate.
Insertion words reuse reachable fold fusion. Element and state universes are
independent in the algebra; the existing relational squares retain their
common-universe specialization. The interface imposes no tree representation,
comparison measure, or physical-sharing convention.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.AbstractSet
universe u v
variable {α : Type u} {S : Type v}

structure Ops (α : Type u) (S : Type v) where
  empty : S
  insert : α → S → S
  member : α → S → Bool

def add (x : α) (contents : α → Prop) : α → Prop := fun y => y = x ∨ contents y

structure Laws (ops : Ops α S) (observe : S → α → Prop) (Valid : S → Prop) : Prop where
  empty_valid : Valid ops.empty
  empty : ∀ x, ¬ observe ops.empty x
  insert_valid : ∀ x s, Valid s → Valid (ops.insert x s)
  insert : ∀ x s, Valid s → ∀ y, observe (ops.insert x s) y ↔ add x (observe s) y
  member : ∀ x s, Valid s → (ops.member x s = true ↔ observe s x)

/-- Change the observer only where the fixed operations' validity contract
applies. Empty and inserted states are valid by the original laws. -/
theorem Laws.congr_observe {ops : Ops α S} {observe observe' : S → α → Prop}
    {Valid : S → Prop} (laws : Laws ops observe Valid)
    (agree : ∀ s, Valid s → ∀ x, observe s x ↔ observe' s x) :
    Laws ops observe' Valid where
  empty_valid := laws.empty_valid
  empty x := fun h => laws.empty x ((agree ops.empty laws.empty_valid x).mpr h)
  insert_valid := laws.insert_valid
  insert x s hs y :=
    (agree (ops.insert x s) (laws.insert_valid x s hs) y).symm.trans
      ((laws.insert x s hs y).trans (or_congr Iff.rfl (agree s hs y)))
  member x s hs := (laws.member x s hs).trans (agree s hs x)

def representation {α S : Type u} (observe : S → α → Prop) (Valid : S → Prop) :
    Relational.RelRep :=
  ⟨S, α → Prop, fun s contents => Valid s ∧ ∀ x, observe s x ↔ contents x⟩

def Laws.insertSquare {α S : Type u} {ops : Ops α S}
    {observe : S → α → Prop} {Valid : S → Prop}
    (laws : Laws ops observe Valid) (x : α) :
    Relational.RelSquare (representation observe Valid) (representation observe Valid) where
  impl := ops.insert x
  spec := add x
  preserves := by
    intro s contents h
    exact ⟨laws.insert_valid x s h.1,
      fun y => (laws.insert x s h.1 y).trans (or_congr Iff.rfl (h.2 y))⟩

def insertMany (ops : Ops α S) (xs : List α) (s : S) : S :=
  xs.foldl (fun q x => ops.insert x q) s

theorem Laws.insertMany_valid {ops : Ops α S} {observe : S → α → Prop}
    {Valid : S → Prop} (laws : Laws ops observe Valid) (xs : List α) {s : S}
    (valid : Valid s) : Valid (insertMany ops xs s) := by
  induction xs generalizing s with
  | nil => exact valid
  | cons x xs ih => exact ih (laws.insert_valid x s valid)

/-- One fold-fusion instance supplies the observation of every insertion word. -/
theorem Laws.insertMany_observe {ops : Ops α S} {observe : S → α → Prop}
    {Valid : S → Prop} (laws : Laws ops observe Valid) (xs : List α) {s : S}
    (valid : Valid s) :
    observe (insertMany ops xs s) = xs.foldl (fun contents x => add x contents) (observe s) := by
  apply SquareKit.ListFusion.foldl_reachable
    (fun q x => ops.insert x q) (fun contents x => add x contents)
    observe Valid s valid
  · exact fun q x hq => laws.insert_valid x q hq
  · intro q x hq
    funext y
    exact propext (laws.insert x q hq y)

theorem fold_add (xs : List α) (contents : α → Prop) (x : α) :
    (xs.foldl (fun current y => add y current) contents) x ↔ x ∈ xs ∨ contents x := by
  induction xs generalizing contents with
  | nil => simp
  | cons y ys ih =>
      simp only [List.foldl_cons, ih, List.mem_cons, add]
      tauto

theorem Laws.member_insertMany {ops : Ops α S} {observe : S → α → Prop}
    {Valid : S → Prop} (laws : Laws ops observe Valid) (xs : List α) {s : S}
    (valid : Valid s) (x : α) :
    ops.member x (insertMany ops xs s) = true ↔ x ∈ xs ∨ observe s x := by
  rw [laws.member x _ (laws.insertMany_valid xs valid), laws.insertMany_observe xs valid]
  exact fold_add xs (observe s) x

theorem Laws.member_from_empty {ops : Ops α S} {observe : S → α → Prop}
    {Valid : S → Prop} (laws : Laws ops observe Valid) (xs : List α) (x : α) :
    ops.member x (insertMany ops xs ops.empty) = true ↔ x ∈ xs := by
  simpa only [laws.empty x, or_false] using
    laws.member_insertMany xs laws.empty_valid x

end Search.AbstractSet

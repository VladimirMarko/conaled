import Applications.Search.AbstractSet

/-!
# An additive deletion capability and mixed update clients

The original insertion-only operations and laws are projections. No ordering
is imposed by this abstract contract. Mixed histories use the existing list
fold and reachable-fusion theorem, with an independent set-update semantics.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.AbstractSet
universe u v
variable {α : Type u} {S : Type v}

structure DeleteOps (α : Type u) (S : Type v) extends Ops α S where
  delete : α → S → S

def remove (x : α) (contents : α → Prop) : α → Prop :=
  fun y => y ≠ x ∧ contents y

structure DeleteLaws (ops : DeleteOps α S) (observe : S → α → Prop)
    (Valid : S → Prop) : Prop extends Laws ops.toOps observe Valid where
  delete_valid : ∀ x s, Valid s → Valid (ops.delete x s)
  delete : ∀ x s, Valid s → ∀ y,
    observe (ops.delete x s) y ↔ remove x (observe s) y

theorem DeleteLaws.congr_observe {ops : DeleteOps α S}
    {observe observe' : S → α → Prop} {Valid : S → Prop}
    (laws : DeleteLaws ops observe Valid)
    (agree : ∀ s, Valid s → ∀ x, observe s x ↔ observe' s x) :
    DeleteLaws ops observe' Valid where
  toLaws := laws.toLaws.congr_observe agree
  delete_valid := laws.delete_valid
  delete x s hs y :=
    (agree (ops.delete x s) (laws.delete_valid x s hs) y).symm.trans
      ((laws.delete x s hs y).trans (and_congr Iff.rfl (agree s hs y)))

/-- Transport only the validity presentation; operations and observations stay fixed. -/
theorem DeleteLaws.congr_valid {ops : DeleteOps α S} {observe : S → α → Prop}
    {Valid Valid' : S → Prop} (laws : DeleteLaws ops observe Valid)
    (agree : ∀ s, Valid s ↔ Valid' s) : DeleteLaws ops observe Valid' where
  empty_valid := (agree ops.empty).mp laws.empty_valid
  empty := laws.empty
  insert_valid x s hs := (agree _).mp (laws.insert_valid x s ((agree s).mpr hs))
  insert x s hs := laws.insert x s ((agree s).mpr hs)
  member x s hs := laws.member x s ((agree s).mpr hs)
  delete_valid x s hs := (agree _).mp (laws.delete_valid x s ((agree s).mpr hs))
  delete x s hs := laws.delete x s ((agree s).mpr hs)

inductive Update (α : Type u) where
  | insert (value : α)
  | delete (value : α)
  deriving Repr

def step (ops : DeleteOps α S) (s : S) : Update α → S
  | .insert x => ops.insert x s
  | .delete x => ops.delete x s

def meaningStep (contents : α → Prop) : Update α → α → Prop
  | .insert x => add x contents
  | .delete x => remove x contents

def execute (ops : DeleteOps α S) (updates : List (Update α)) (s : S) : S :=
  updates.foldl (step ops) s

theorem DeleteLaws.step_valid {ops : DeleteOps α S} {observe : S → α → Prop}
    {Valid : S → Prop} (laws : DeleteLaws ops observe Valid) (s : S)
    (update : Update α) (hs : Valid s) : Valid (step ops s update) := by
  cases update with
  | insert x => exact laws.insert_valid x s hs
  | delete x => exact laws.delete_valid x s hs

theorem DeleteLaws.step_observe {ops : DeleteOps α S} {observe : S → α → Prop}
    {Valid : S → Prop} (laws : DeleteLaws ops observe Valid) (s : S)
    (update : Update α) (hs : Valid s) :
    observe (step ops s update) = meaningStep (observe s) update := by
  funext x
  apply propext
  cases update with
  | insert y => exact laws.insert y s hs x
  | delete y => exact laws.delete y s hs x

theorem DeleteLaws.execute_valid {ops : DeleteOps α S} {observe : S → α → Prop}
    {Valid : S → Prop} (laws : DeleteLaws ops observe Valid)
    (updates : List (Update α)) {s : S} (hs : Valid s) :
    Valid (execute ops updates s) := by
  induction updates generalizing s with
  | nil => exact hs
  | cons update updates ih => exact ih (laws.step_valid s update hs)

theorem DeleteLaws.execute_observe {ops : DeleteOps α S} {observe : S → α → Prop}
    {Valid : S → Prop} (laws : DeleteLaws ops observe Valid)
    (updates : List (Update α)) {s : S} (hs : Valid s) :
    observe (execute ops updates s) = updates.foldl meaningStep (observe s) := by
  apply SquareKit.ListFusion.foldl_reachable (step ops) meaningStep observe Valid s hs
  · exact fun q update hq => laws.step_valid q update hq
  · exact fun q update hq => laws.step_observe q update hq

/-- Every prefix is valid; a prefix length beyond the word is harmless. -/
theorem DeleteLaws.prefix_valid {ops : DeleteOps α S} {observe : S → α → Prop}
    {Valid : S → Prop} (laws : DeleteLaws ops observe Valid)
    (updates : List (Update α)) (n : Nat) {s : S} (hs : Valid s) :
    Valid (execute ops (updates.take n) s) := laws.execute_valid _ hs

theorem DeleteLaws.member_execute {ops : DeleteOps α S} {observe : S → α → Prop}
    {Valid : S → Prop} (laws : DeleteLaws ops observe Valid)
    (updates : List (Update α)) {s : S} (hs : Valid s) (x : α) :
    ops.member x (execute ops updates s) = true ↔
      (updates.foldl meaningStep (observe s)) x := by
  rw [laws.member x _ (laws.execute_valid updates hs), laws.execute_observe updates hs]

theorem DeleteLaws.execute_from_empty {ops : DeleteOps α S}
    {observe : S → α → Prop} {Valid : S → Prop} (laws : DeleteLaws ops observe Valid)
    (updates : List (Update α)) :
    observe (execute ops updates ops.empty) = updates.foldl meaningStep (fun _ => False) := by
  have empty_eq : observe ops.empty = fun _ => False := by
    funext x
    exact propext ⟨laws.empty x, False.elim⟩
  rw [laws.execute_observe updates laws.empty_valid, empty_eq]

def DeleteLaws.deleteSquare {α S : Type u} {ops : DeleteOps α S}
    {observe : S → α → Prop} {Valid : S → Prop} (laws : DeleteLaws ops observe Valid)
    (x : α) :
    Relational.RelSquare (representation observe Valid) (representation observe Valid) where
  impl := ops.delete x
  spec := remove x
  preserves := by
    intro s contents h
    exact ⟨laws.delete_valid x s h.1,
      fun y => (laws.delete x s h.1 y).trans (and_congr Iff.rfl (h.2 y))⟩

end Search.AbstractSet

import Applications.Search.PriorityInterface
import Mathlib.Data.List.Sort

/-! Exact occurrence insertion strengthens the keyed search frontier contract. -/
set_option autoImplicit false
set_option warningAsError true
namespace Search.PriorityInterface
universe u v w z
variable {α : Type u} {π : Type w} {κ : Type v}

/-- Laws for exact insertion and minimum deletion, independent of operations and observation. -/
structure ExactLaws [LE π] (ops : Operations.{u,w,z} α π)
    (entries : ops.Carrier → List (α × π)) (Valid : ops.Carrier → Prop) : Prop where
  empty_entries : entries ops.empty = []
  empty_valid : Valid ops.empty
  add_valid : ∀ xs q, Valid q → Valid (ops.add xs q)
  add_exact : ∀ xs q, (entries (ops.add xs q)).Perm (xs ++ entries q)
  remove_none : ∀ q, ops.remove q = none ↔ entries q = []
  remove_spec : ∀ q e r, Valid q → ops.remove q = some (e,r) →
    Valid r ∧ (entries q).Perm (e :: entries r) ∧ ∀ a ∈ entries q, e.2 ≤ a.2

/-- An implementation and its observation, retaining every repeated occurrence. -/
structure ExactQueue (α : Type u) (π : Type w) [LE π]
    extends Operations.{u,w,z} α π where
  entries : Carrier → List (α × π)
  Valid : Carrier → Prop
  lawful : ExactLaws toOperations entries Valid

abbrev ExactQueue.empty_entries [LE π] (Q : ExactQueue.{u,w,z} α π) := Q.lawful.empty_entries
abbrev ExactQueue.empty_valid [LE π] (Q : ExactQueue.{u,w,z} α π) := Q.lawful.empty_valid
abbrev ExactQueue.add_valid [LE π] (Q : ExactQueue.{u,w,z} α π) := Q.lawful.add_valid
abbrev ExactQueue.add_exact [LE π] (Q : ExactQueue.{u,w,z} α π) := Q.lawful.add_exact
abbrev ExactQueue.remove_none [LE π] (Q : ExactQueue.{u,w,z} α π) := Q.lawful.remove_none
abbrev ExactQueue.remove_spec [LE π] (Q : ExactQueue.{u,w,z} α π) := Q.lawful.remove_spec

/-- The weaker keyed interface follows for any selected key. -/
def ExactQueue.keyed [LE π] [Std.Refl (fun a b : π => a ≤ b)] (Q : ExactQueue.{u,w,z} α π) (key : α → κ) :
    Queue α κ π key where
  toOperations := Q.toOperations
  entries := Q.entries
  Valid := Q.Valid
  lawful := {
    empty_entries := Q.empty_entries
    empty_valid := Q.empty_valid
    add_valid := Q.add_valid
    add_origin := fun xs q _ h => (Q.add_exact xs q).mem_iff.mp h
    add_covers := fun xs q e h => ⟨e, (Q.add_exact xs q).mem_iff.mpr h, rfl, Std.le_refl _⟩
    add_length := fun xs q => by simpa using Nat.le_of_eq (Q.add_exact xs q).length_eq
    remove_none := Q.remove_none
    remove_spec := Q.remove_spec
  }

/-- Existing leftist operations, with no change to insertion order or tie choice. -/
abbrev exactLeftist [LE π] [DecidableLE π] [Std.IsLinearPreorder π] : ExactQueue α π where
  Carrier := LeftistQueue.PQ α π
  empty := LeftistQueue.emptyQ
  add := LeftistQueue.addListQ
  remove := LeftistQueue.deleteQ
  entries := LeftistQueue.entries
  Valid := LeftistQueue.Valid
  lawful := {
    empty_entries := rfl
    empty_valid := LeftistQueue.emptyQ_valid
    add_valid := LeftistQueue.addListQ_valid
    add_exact := LeftistQueue.addListQ_entries
    remove_none := (leftist (id : α → α)).remove_none
    remove_spec := (leftist (id : α → α)).remove_spec
  }

section ListQueue
variable [LE π] [DecidableLE π] [Std.IsLinearPreorder π]

/-- A simple occurrence queue: keep insertion order and sort only at deletion. -/
def listRemove (xs : List (α × π)) : Option ((α × π) × List (α × π)) :=
  match xs.mergeSort (fun a b => decide (a.2 ≤ b.2)) with
  | [] => none
  | a :: rest => some (a, rest)

omit [Std.IsLinearPreorder π] in
theorem listRemove_none (xs : List (α × π)) : listRemove xs = none ↔ xs = [] := by
  unfold listRemove
  have hp := List.mergeSort_perm xs (fun a b => decide (a.2 ≤ b.2))
  cases hs : xs.mergeSort (fun a b => decide (a.2 ≤ b.2)) with
  | nil =>
    have he : xs = [] := List.length_eq_zero_iff.mp (by simpa [hs] using hp.length_eq.symm)
    simp [he]
  | cons a rest =>
    simp only [Option.some_ne_none, false_iff]
    intro he
    subst xs
    simp at hs

theorem listRemove_spec (xs : List (α × π)) (a : α × π) (rest : List (α × π))
    (h : listRemove xs = some (a, rest)) :
    xs.Perm (a :: rest) ∧ ∀ b ∈ xs, a.2 ≤ b.2 := by
  have hp := List.mergeSort_perm xs (fun a b => decide (a.2 ≤ b.2))
  have hs : xs.mergeSort (fun a b => decide (a.2 ≤ b.2)) = a :: rest := by
    unfold listRemove at h
    cases he : xs.mergeSort (fun a b => decide (a.2 ≤ b.2)) with
    | nil => simp [he] at h
    | cons b bs =>
      simp only [he, Option.some.injEq, Prod.mk.injEq] at h
      cases h.1
      cases h.2
      rfl
  rw [hs] at hp
  refine ⟨hp.symm, ?_⟩
  have ho : (a :: rest).Pairwise (fun a b => a.2 ≤ b.2) := by
    rw [← hs]
    have h := List.pairwise_mergeSort
      (le := fun a b : α × π => decide (a.2 ≤ b.2))
      (fun _ _ _ hab hbc => by
        simpa only [decide_eq_true_eq] using
          Std.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
      (fun _ _ => by simpa only [Bool.or_eq_true, decide_eq_true_eq] using Std.le_total (α := π)) xs
    simpa only [decide_eq_true_eq] using h
  intro b hb
  rcases List.mem_cons.mp (hp.mem_iff.mpr hb) with rfl | hb
  · exact Std.le_refl _
  · exact (List.pairwise_cons.mp ho).1 b hb

/-- A second exact realization. No claim equates its tie-selected shapes with leftist trees. -/
abbrev exactList : ExactQueue α π where
  Carrier := List (α × π)
  empty := []
  add := fun xs q => q ++ xs
  remove := listRemove
  entries := id
  Valid := fun _ => True
  lawful := {
    empty_entries := rfl
    empty_valid := trivial
    add_valid := fun _ _ _ => trivial
    add_exact := fun _ _ => List.perm_append_comm
    remove_none := listRemove_none
    remove_spec := fun q e r _ h => ⟨trivial, listRemove_spec q e r h⟩
  }
end ListQueue
end Search.PriorityInterface

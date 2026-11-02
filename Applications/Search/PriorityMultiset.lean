import Applications.Search.ExactPriority
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max

/-!
# Exact priority-queue observations

The existing operations and occurrence laws are unchanged. These ordinary views
retain entry multiplicities, project priorities, and compare actual removals.
Optional access and the nonempty finite minimum do not require default payloads.

The source contract is Chapter 14 of Nipkow et al., *Functional Data Structures
and Algorithms: A Proof Assistant Approach* (July 27, 2026). The companion
`Priority_Queue_Specs.thy` (Tobias Nipkow and Peter Lammich) and `Heaps.thy`
(Tobias Nipkow) at Isabelle revision f86f290225eebcc52c1ae7dba2e098f405f51c21
are BSD-3-Clause sources; see `docs/research/fdsa-priority-queues.md` for their
exact URLs, license notice, and the one-way source adaptation. No timing claim
is attached to projecting a removal or to the separate direct-root observer.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.PriorityInterface

universe u v w z z'
variable {α : Type u} {β : Type v} {π : Type w}

namespace Operations

/-- Singleton insertion uses the supplied batch insertion, in its original order. -/
def insertOne (ops : Operations.{u,w,z} α π) (e : α × π) (q : ops.Carrier) :
    ops.Carrier := ops.add [e] q

/-- This semantic peek projects an actual removal; it has no cheap-access claim. -/
def peekEntry? (ops : Operations.{u,w,z} α π) (q : ops.Carrier) : Option (α × π) :=
  (ops.remove q).map Prod.fst

/-- Priority projection of the same actual removal. -/
def peekPriority? (ops : Operations.{u,w,z} α π) (q : ops.Carrier) : Option π :=
  (ops.remove q).map (fun z => z.1.2)

/-- Keep the input state when removal reports none. -/
def deleteMin (ops : Operations.{u,w,z} α π) (q : ops.Carrier) : ops.Carrier :=
  match ops.remove q with
  | none => q
  | some (_, r) => r

/-- Semantic emptiness of the supplied removal, without a traversal-cost claim. -/
def isEmpty (ops : Operations.{u,w,z} α π) (q : ops.Carrier) : Bool :=
  (ops.remove q).isNone

/-- All views use the same none result and the declared identity deletion branch. -/
theorem views_of_none (ops : Operations.{u,w,z} α π) (q : ops.Carrier)
    (h : ops.remove q = none) :
    ops.peekEntry? q = none ∧ ops.peekPriority? q = none ∧
      ops.deleteMin q = q ∧ ops.isEmpty q = true := by
  simp [peekEntry?, peekPriority?, deleteMin, isEmpty, h]

/-- All successful views use the supplied result, including its actual residual. -/
theorem views_of_some (ops : Operations.{u,w,z} α π) (q : ops.Carrier)
    (e : α × π) (r : ops.Carrier) (h : ops.remove q = some (e, r)) :
    ops.peekEntry? q = some e ∧ ops.peekPriority? q = some e.2 ∧
      ops.deleteMin q = r ∧ ops.isEmpty q = false := by
  simp [peekEntry?, peekPriority?, deleteMin, isEmpty, h]

/-- Boolean reflection is an iff with equality to true, not a Bool/Prop equality. -/
theorem isEmpty_eq_true_iff (ops : Operations.{u,w,z} α π) (q : ops.Carrier) :
    ops.isEmpty q = true ↔ ops.remove q = none := by
  cases h : ops.remove q <;> simp [isEmpty, h]

end Operations

namespace ExactQueue

section LE
variable [LE π] (Q : ExactQueue.{u,w,z} α π)

/-- The exact finite multiset of payload/priority occurrences. -/
def entryMultiset (q : Q.Carrier) : Multiset (α × π) := Q.entries q

/-- Forget payloads while retaining every priority occurrence. -/
def priorityMultiset (q : Q.Carrier) : Multiset π :=
  (Q.entryMultiset q).map Prod.snd

/-- Observe the actual selected priority together with the actual residual content. -/
def popObs (q : Q.Carrier) : Option (π × Multiset π) :=
  (Q.remove q).map (fun (e, r) => (e.2, Q.priorityMultiset r))

@[simp]
theorem entryMultiset_empty : Q.entryMultiset Q.empty = 0 :=
  congrArg (fun xs : List (α × π) => (xs : Multiset (α × π))) Q.empty_entries

@[simp]
theorem priorityMultiset_empty : Q.priorityMultiset Q.empty = 0 := by
  change (Q.entryMultiset Q.empty).map Prod.snd = 0
  rw [Q.entryMultiset_empty, Multiset.map_zero]

/-- Exact insertion holds even for an invalid raw input state. -/
theorem entryMultiset_add (xs : List (α × π)) (q : Q.Carrier) :
    Q.entryMultiset (Q.add xs q) = (xs : Multiset (α × π)) + Q.entryMultiset q :=
  (Multiset.coe_eq_coe.mpr (Q.add_exact xs q)).trans
    (Multiset.coe_add xs (Q.entries q)).symm

theorem priorityMultiset_add (xs : List (α × π)) (q : Q.Carrier) :
    Q.priorityMultiset (Q.add xs q) =
      (xs : Multiset (α × π)).map Prod.snd + Q.priorityMultiset q := by
  change (Q.entryMultiset (Q.add xs q)).map Prod.snd =
    (xs : Multiset (α × π)).map Prod.snd + (Q.entryMultiset q).map Prod.snd
  rw [Q.entryMultiset_add, Multiset.map_add]

theorem entryMultiset_insertOne (e : α × π) (q : Q.Carrier) :
    Q.entryMultiset (Q.toOperations.insertOne e q) = e ::ₘ Q.entryMultiset q :=
  Multiset.coe_eq_coe.mpr (Q.add_exact [e] q)

theorem priorityMultiset_insertOne (e : α × π) (q : Q.Carrier) :
    Q.priorityMultiset (Q.toOperations.insertOne e q) = e.2 ::ₘ Q.priorityMultiset q := by
  change (Q.entryMultiset (Q.toOperations.insertOne e q)).map Prod.snd =
    e.2 ::ₘ (Q.entryMultiset q).map Prod.snd
  rw [Q.entryMultiset_insertOne, Multiset.map_cons]

/-- The source's multiset-plus-singleton form, also valid for general payloads. -/
theorem priorityMultiset_insertOne_add (e : α × π) (q : Q.Carrier) :
    Q.priorityMultiset (Q.toOperations.insertOne e q) = Q.priorityMultiset q + {e.2} := by
  rw [Q.priorityMultiset_insertOne, ← Multiset.singleton_add, Multiset.add_comm]

theorem insertOne_valid (e : α × π) (q : Q.Carrier) (hq : Q.Valid q) :
    Q.Valid (Q.toOperations.insertOne e q) := Q.add_valid [e] q hq

@[simp]
theorem entryMultiset_card (q : Q.Carrier) :
    (Q.entryMultiset q).card = (Q.entries q).length := Multiset.coe_card _

@[simp]
theorem priorityMultiset_card (q : Q.Carrier) :
    (Q.priorityMultiset q).card = (Q.entries q).length :=
  (Multiset.card_map _ _).trans (Q.entryMultiset_card q)

theorem entryMultiset_add_card (xs : List (α × π)) (q : Q.Carrier) :
    (Q.entryMultiset (Q.add xs q)).card = xs.length + (Q.entryMultiset q).card := by
  rw [Q.entryMultiset_add, Multiset.card_add, Multiset.coe_card]

theorem priorityMultiset_add_card (xs : List (α × π)) (q : Q.Carrier) :
    (Q.priorityMultiset (Q.add xs q)).card = xs.length + (Q.priorityMultiset q).card := by
  rw [Q.priorityMultiset_add, Multiset.card_add, Multiset.card_map, Multiset.coe_card]

/-- Failure reflection retains the existing unconditional raw-state law. -/
theorem remove_none_iff_entryMultiset (q : Q.Carrier) :
    Q.remove q = none ↔ Q.entryMultiset q = 0 :=
  (Q.remove_none q).trans (Multiset.coe_eq_zero (Q.entries q)).symm

theorem priorityMultiset_eq_zero_iff (q : Q.Carrier) :
    Q.priorityMultiset q = 0 ↔ Q.entryMultiset q = 0 := Multiset.map_eq_zero

theorem remove_none_iff_priorityMultiset (q : Q.Carrier) :
    Q.remove q = none ↔ Q.priorityMultiset q = 0 :=
  (Q.remove_none_iff_entryMultiset q).trans (Q.priorityMultiset_eq_zero_iff q).symm

theorem isEmpty_eq_true_iff (q : Q.Carrier) :
    Q.toOperations.isEmpty q = true ↔ Q.priorityMultiset q = 0 :=
  (Operations.isEmpty_eq_true_iff Q.toOperations q).trans
    (Q.remove_none_iff_priorityMultiset q)

/-- Nonempty observation already forces an actual successful removal, before validity. -/
theorem exists_remove_of_ne_zero (q : Q.Carrier) (hne : Q.priorityMultiset q ≠ 0) :
    ∃ e r, Q.remove q = some (e, r) := by
  cases h : Q.remove q with
  | none => exact False.elim (hne ((Q.remove_none_iff_priorityMultiset q).mp h))
  | some result =>
    rcases result with ⟨e, r⟩
    exact ⟨e, r, h⟩

/-- A valid actual removal retains one-occurrence decomposition and least priority. -/
theorem remove_spec_multiset (q : Q.Carrier) (e : α × π) (r : Q.Carrier)
    (hq : Q.Valid q) (h : Q.remove q = some (e, r)) :
    Q.Valid r ∧ e ∈ Q.entryMultiset q ∧
      Q.entryMultiset q = e ::ₘ Q.entryMultiset r ∧
      IsLeast {p | p ∈ Q.priorityMultiset q} e.2 ∧
      Q.priorityMultiset q = e.2 ::ₘ Q.priorityMultiset r := by
  rcases Q.remove_spec q e r hq h with ⟨hr, hp, hleast⟩
  have he : Q.entryMultiset q = e ::ₘ Q.entryMultiset r :=
    Multiset.coe_eq_coe.mpr hp
  have hmem : e ∈ Q.entryMultiset q := by
    rw [he]
    exact Multiset.mem_cons_self _ _
  have hpriority : Q.priorityMultiset q = e.2 ::ₘ Q.priorityMultiset r := by
    change (Q.entryMultiset q).map Prod.snd = e.2 ::ₘ (Q.entryMultiset r).map Prod.snd
    rw [he, Multiset.map_cons]
  refine ⟨hr, hmem, he, ?_, hpriority⟩
  refine ⟨Multiset.mem_map_of_mem Prod.snd hmem, ?_⟩
  intro p hp
  rcases Multiset.mem_map.mp hp with ⟨a, ha, rfl⟩
  exact hleast a (Multiset.mem_coe.mp ha)

theorem remove_card (q : Q.Carrier) (e : α × π) (r : Q.Carrier)
    (hq : Q.Valid q) (h : Q.remove q = some (e, r)) :
    (Q.entryMultiset r).card + 1 = (Q.entryMultiset q).card := by
  have he := (Q.remove_spec_multiset q e r hq h).2.2.1
  calc
    (Q.entryMultiset r).card + 1 = (e ::ₘ Q.entryMultiset r).card :=
      (Multiset.card_cons _ _).symm
    _ = (Q.entryMultiset q).card := congrArg Multiset.card he.symm

theorem remove_priority_card (q : Q.Carrier) (e : α × π) (r : Q.Carrier)
    (hq : Q.Valid q) (h : Q.remove q = some (e, r)) :
    (Q.priorityMultiset r).card + 1 = (Q.priorityMultiset q).card := by
  have hp := (Q.remove_spec_multiset q e r hq h).2.2.2.2
  calc
    (Q.priorityMultiset r).card + 1 = (e.2 ::ₘ Q.priorityMultiset r).card :=
      (Multiset.card_cons _ _).symm
    _ = (Q.priorityMultiset q).card := congrArg Multiset.card hp.symm

/-- Identity on none and the actual valid residual on some preserve validity. -/
theorem deleteMin_valid (q : Q.Carrier) (hq : Q.Valid q) :
    Q.Valid (Q.toOperations.deleteMin q) := by
  cases h : Q.remove q with
  | none => simpa only [Operations.deleteMin, h] using hq
  | some result =>
    rcases result with ⟨e, r⟩
    simpa only [Operations.deleteMin, h] using (Q.remove_spec q e r hq h).1

theorem popObs_of_remove (q : Q.Carrier) (e : α × π) (r : Q.Carrier)
    (h : Q.remove q = some (e, r)) :
    Q.popObs q = some (e.2, Q.priorityMultiset r) := by
  simp only [popObs, h, Option.map_some]

/-- The actual priority and residual-priority observation is independent of realization. -/
theorem popObs_eq (R : ExactQueue.{v,w,z'} β π)
    (hantisymm : ∀ p q : π, p ≤ q → q ≤ p → p = q)
    (q : Q.Carrier) (r : R.Carrier) (hq : Q.Valid q) (hr : R.Valid r)
    (hobs : Q.priorityMultiset q = R.priorityMultiset r) :
    Q.popObs q = R.popObs r := by
  cases hQ : Q.remove q with
  | none =>
    have hzQ := (Q.remove_none_iff_priorityMultiset q).mp hQ
    have hR : R.remove r = none :=
      (R.remove_none_iff_priorityMultiset r).mpr (hobs.symm.trans hzQ)
    simp only [popObs, hQ, hR, Option.map_none]
  | some resultQ =>
    rcases resultQ with ⟨a, q'⟩
    rcases Q.remove_spec_multiset q a q' hq hQ with ⟨_, _, _, hminQ, hdecQ⟩
    cases hR : R.remove r with
    | none =>
      have hzR := (R.remove_none_iff_priorityMultiset r).mp hR
      exact False.elim (Multiset.cons_ne_zero (hdecQ.symm.trans (hobs.trans hzR)))
    | some resultR =>
      rcases resultR with ⟨b, r'⟩
      rcases R.remove_spec_multiset r b r' hr hR with ⟨_, _, _, hminR, hdecR⟩
      have hab : a.2 ≤ b.2 := hminQ.2 (by rw [hobs]; exact hminR.1)
      have hba : b.2 ≤ a.2 := hminR.2 (by rw [← hobs]; exact hminQ.1)
      have hp : a.2 = b.2 := hantisymm _ _ hab hba
      have hrest : Q.priorityMultiset q' = R.priorityMultiset r' := by
        apply (Multiset.cons_inj_right a.2).mp
        calc
          a.2 ::ₘ Q.priorityMultiset q' = Q.priorityMultiset q := hdecQ.symm
          _ = R.priorityMultiset r := hobs
          _ = b.2 ::ₘ R.priorityMultiset r' := hdecR
          _ = a.2 ::ₘ R.priorityMultiset r' := by rw [hp]
      simp only [popObs, hQ, hR, Option.map_some]
      exact congrArg some (Prod.ext hp hrest)

/-- Every finite entry multiset has a valid representative obtained by actual insertion. -/
theorem exists_entryMultiset (m : Multiset (α × π)) :
    ∃ q, Q.Valid q ∧ Q.entryMultiset q = m := by
  refine Quotient.inductionOn' m ?_
  intro xs
  refine ⟨Q.add xs Q.empty, Q.add_valid xs Q.empty Q.empty_valid, ?_⟩
  rw [Q.entryMultiset_add, Q.entryMultiset_empty, Multiset.add_zero]

/-- A supplied payload suffices to realize every finite priority multiset. -/
theorem exists_priorityMultiset (a0 : α) (m : Multiset π) :
    ∃ q, Q.Valid q ∧ Q.priorityMultiset q = m := by
  obtain ⟨q, hq, he⟩ := Q.exists_entryMultiset (m.map (fun p => (a0, p)))
  refine ⟨q, hq, ?_⟩
  change (Q.entryMultiset q).map Prod.snd = m
  rw [he, Multiset.map_map]
  exact Multiset.map_id m

/-- An empty payload type leaves no entry occurrences, even on raw states. -/
theorem entryMultiset_eq_zero_of_isEmpty_payload [IsEmpty α] (q : Q.Carrier) :
    Q.entryMultiset q = 0 := by
  apply Multiset.eq_zero_of_forall_notMem
  intro e _
  exact isEmptyElim e.1

/-- An empty priority type likewise leaves no entry occurrences. -/
theorem entryMultiset_eq_zero_of_isEmpty_priority [IsEmpty π] (q : Q.Carrier) :
    Q.entryMultiset q = 0 := by
  apply Multiset.eq_zero_of_forall_notMem
  intro e _
  exact isEmptyElim e.2

end LE

section DecidablePriority
variable [LE π] [DecidableEq π] (Q : ExactQueue.{u,w,z} α π)

/-- Subtract one selected priority; no equality decision on payloads is needed. -/
theorem priorityMultiset_remove_sub (q : Q.Carrier) (e : α × π) (r : Q.Carrier)
    (hq : Q.Valid q) (h : Q.remove q = some (e, r)) :
    Q.priorityMultiset r = Q.priorityMultiset q - {e.2} := by
  rw [(Q.remove_spec_multiset q e r hq h).2.2.2.2,
    Multiset.sub_singleton, Multiset.erase_cons_head]

end DecidablePriority

section LinearOrder
variable [LinearOrder π] (Q : ExactQueue.{u,w,z} α π)

private theorem removed_priority_eq_min (q : Q.Carrier) (e : α × π) (r : Q.Carrier)
    (hq : Q.Valid q) (h : Q.remove q = some (e, r)) (hne : Q.priorityMultiset q ≠ 0) :
    e.2 = (Q.priorityMultiset q).toFinset.min'
      (Multiset.toFinset_nonempty.mpr hne) := by
  have hleast := (Q.remove_spec_multiset q e r hq h).2.2.2.1
  symm
  apply (Finset.min'_eq_iff _ _ e.2).mpr
  refine ⟨Multiset.mem_toFinset.mpr hleast.1, ?_⟩
  intro p hp
  exact hleast.2 (Multiset.mem_toFinset.mp hp)

/-- The optional source minimum on its valid, nonempty domain. -/
theorem peekPriority?_eq_min (q : Q.Carrier) (hq : Q.Valid q)
    (hne : Q.priorityMultiset q ≠ 0) :
    Q.toOperations.peekPriority? q = some ((Q.priorityMultiset q).toFinset.min'
      (Multiset.toFinset_nonempty.mpr hne)) := by
  obtain ⟨e, r, h⟩ := Q.exists_remove_of_ne_zero q hne
  calc
    Q.toOperations.peekPriority? q = some e.2 :=
      (Operations.views_of_some Q.toOperations q e r h).2.1
    _ = some ((Q.priorityMultiset q).toFinset.min'
        (Multiset.toFinset_nonempty.mpr hne)) :=
      congrArg some (Q.removed_priority_eq_min q e r hq h hne)

/-- The state-valued source deletion removes exactly one nonempty-domain minimum. -/
theorem priorityMultiset_deleteMin_sub_min (q : Q.Carrier) (hq : Q.Valid q)
    (hne : Q.priorityMultiset q ≠ 0) :
    Q.priorityMultiset (Q.toOperations.deleteMin q) =
      Q.priorityMultiset q - {(Q.priorityMultiset q).toFinset.min'
        (Multiset.toFinset_nonempty.mpr hne)} := by
  obtain ⟨e, r, h⟩ := Q.exists_remove_of_ne_zero q hne
  calc
    Q.priorityMultiset (Q.toOperations.deleteMin q) = Q.priorityMultiset r :=
      congrArg Q.priorityMultiset (Operations.views_of_some Q.toOperations q e r h).2.2.1
    _ = Q.priorityMultiset q - {e.2} := Q.priorityMultiset_remove_sub q e r hq h
    _ = Q.priorityMultiset q - {(Q.priorityMultiset q).toFinset.min'
        (Multiset.toFinset_nonempty.mpr hne)} := by
      rw [Q.removed_priority_eq_min q e r hq h hne]

end LinearOrder
end ExactQueue
end Search.PriorityInterface

namespace Search.LeftistQueue

universe u v
variable {α : Type u} {π : Type v}

/-- Direct root access, independent of comparison and without a default payload. -/
def peekQ? : PQ α π → Option (α × π)
  | .null => none
  | .fork _ x p _ _ => some (x, p)

/-- This is a value equation; the existing deletion still performs its merge. -/
theorem deleteQ_fst [LE π] [DecidableLE π] (q : PQ α π) :
    (deleteQ q).map Prod.fst = peekQ? q := by
  cases q <;> rfl

theorem peekQ?_eq_none_iff (q : PQ α π) : peekQ? q = none ↔ nullQ q = true := by
  cases q <;> simp [peekQ?, nullQ]

theorem nullQ_iff_entries_nil (q : PQ α π) : nullQ q = true ↔ entries q = [] := by
  rw [nullQ_iff, ← size_zero_iff, ← entries_length, List.length_eq_zero_iff]

/-- Raw structural emptiness reflects the full occurrence observation, with no order. -/
theorem nullQ_iff_entryMultiset (q : PQ α π) :
    nullQ q = true ↔ (entries q : Multiset (α × π)) = 0 :=
  (nullQ_iff_entries_nil q).trans (Multiset.coe_eq_zero (entries q)).symm

theorem nullQ_iff_priorityMultiset (q : PQ α π) :
    nullQ q = true ↔ (entries q : Multiset (α × π)).map Prod.snd = 0 :=
  (nullQ_iff_entryMultiset q).trans Multiset.map_eq_zero.symm

/-- Heap order suffices for root leastness; rankedness and comparison decisions are absent. -/
theorem peekQ?_isLeast [LE π] [Std.IsLinearPreorder π] (q : PQ α π) (e : α × π)
    (hq : Heap q) (h : peekQ? q = some e) :
    IsLeast {p | p ∈ (entries q : Multiset (α × π)).map Prod.snd} e.2 := by
  cases q with
  | null => simp [peekQ?] at h
  | fork k x p l r =>
    have he : (x, p) = e := Option.some.inj h
    cases he
    have hall := (all_iff (fun z : α × π => p ≤ z.2) (.fork k x p l r)).mp
      (root_all k x p l r hq)
    refine ⟨?_, ?_⟩
    · exact Multiset.mem_map_of_mem Prod.snd (a := (x, p))
        (Multiset.mem_coe.mpr (by simp [entries]))
    · intro b hb
      rcases Multiset.mem_map.mp hb with ⟨a, ha, rfl⟩
      exact hall a (Multiset.mem_coe.mp ha)

end Search.LeftistQueue

import Applications.Search.PriorityMultiset

/-!
# Compatible merges for exact occurrence queues

The supplied merge retains its existing carrier, entry observation, and validity
predicate. Its two independent laws are the occurrence and invariant clauses of
FDSA Chapter 14, Figure 14.2 / Isabelle `Priority_Queue_Specs.thy` (Tobias Nipkow
and Peter Lammich, BSD-3-Clause). Pinned provenance and the applicable notice are
recorded in `docs/research/fdsa-priority-queues.md`.

No claim identifies raw states from their contents or assigns an execution cost
to these observations. The sequential client uses the actual merge, insertion,
and removal operations, with validity supplied separately by its theorem.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Search.PriorityInterface

universe u v z
variable {α : Type u} {π : Type v}

/-- Evidence for a supplied merge; the carrier and its observations are parameters. -/
structure MergeLaws {C : Type z} (entries : C → List (α × π))
    (Valid : C → Prop) (merge : C → C → C) : Prop where
  entries_perm : ∀ q r, Valid q → Valid r →
    (entries (merge q r)).Perm (entries q ++ entries r)
  valid : ∀ q r, Valid q → Valid r → Valid (merge q r)

/-- The existing rank-aware leftist merge, retaining both input validity premises. -/
theorem leftistMergeLaws [LE π] [DecidableLE π] [Std.IsLinearPreorder π] :
    MergeLaws (LeftistQueue.entries (α := α) (π := π))
      LeftistQueue.Valid LeftistQueue.combineQ where
  entries_perm := fun q r _ _ => LeftistQueue.combineQ_entries q r
  valid := fun q r hq hr => LeftistQueue.combineQ_valid q r hq hr

/-- Ordinary append is a compatible merge for the existing unsorted list realization. -/
theorem appendMergeLaws :
    MergeLaws (id : List (α × π) → List (α × π)) (fun _ => True) List.append where
  entries_perm := fun q r _ _ => List.Perm.refl (q ++ r)
  valid := fun _ _ _ _ => trivial

/-- Merge, insert one occurrence, then invoke the supplied removal operation. -/
def mergeInsertRemove (ops : Operations.{u,v,z} α π)
    (merge : ops.Carrier → ops.Carrier → ops.Carrier)
    (e : α × π) (q r : ops.Carrier) : Option ((α × π) × ops.Carrier) :=
  ops.remove (ops.add [e] (merge q r))

namespace ExactQueue

variable [LE π]

/-- Compatibility preserves the sum of the full entry multisets on valid inputs. -/
theorem entryMultiset_merge (Q : ExactQueue.{u,v,z} α π)
    (merge : Q.Carrier → Q.Carrier → Q.Carrier)
    (hmerge : MergeLaws Q.entries Q.Valid merge)
    (q r : Q.Carrier) (hq : Q.Valid q) (hr : Q.Valid r) :
    Q.entryMultiset (merge q r) = Q.entryMultiset q + Q.entryMultiset r :=
  (Multiset.coe_eq_coe.mpr (hmerge.entries_perm q r hq hr)).trans
    (Multiset.coe_add (Q.entries q) (Q.entries r)).symm

/-- Priority projection retains the multiplicity sum, including overlapping priorities. -/
theorem priorityMultiset_merge (Q : ExactQueue.{u,v,z} α π)
    (merge : Q.Carrier → Q.Carrier → Q.Carrier)
    (hmerge : MergeLaws Q.entries Q.Valid merge)
    (q r : Q.Carrier) (hq : Q.Valid q) (hr : Q.Valid r) :
    Q.priorityMultiset (merge q r) = Q.priorityMultiset q + Q.priorityMultiset r := by
  change (Q.entryMultiset (merge q r)).map Prod.snd =
    (Q.entryMultiset q).map Prod.snd + (Q.entryMultiset r).map Prod.snd
  rw [Q.entryMultiset_merge merge hmerge q r hq hr, Multiset.map_add]

theorem entryMultiset_merge_card (Q : ExactQueue.{u,v,z} α π)
    (merge : Q.Carrier → Q.Carrier → Q.Carrier)
    (hmerge : MergeLaws Q.entries Q.Valid merge)
    (q r : Q.Carrier) (hq : Q.Valid q) (hr : Q.Valid r) :
    (Q.entryMultiset (merge q r)).card =
      (Q.entryMultiset q).card + (Q.entryMultiset r).card := by
  rw [Q.entryMultiset_merge merge hmerge q r hq hr, Multiset.card_add]

theorem priorityMultiset_merge_card (Q : ExactQueue.{u,v,z} α π)
    (merge : Q.Carrier → Q.Carrier → Q.Carrier)
    (hmerge : MergeLaws Q.entries Q.Valid merge)
    (q r : Q.Carrier) (hq : Q.Valid q) (hr : Q.Valid r) :
    (Q.priorityMultiset (merge q r)).card =
      (Q.priorityMultiset q).card + (Q.priorityMultiset r).card := by
  rw [Q.priorityMultiset_merge merge hmerge q r hq hr, Multiset.card_add]

/-- Commutativity is an occurrence observation, not equality of the merged states. -/
theorem entryMultiset_merge_comm (Q : ExactQueue.{u,v,z} α π)
    (merge : Q.Carrier → Q.Carrier → Q.Carrier)
    (hmerge : MergeLaws Q.entries Q.Valid merge)
    (q r : Q.Carrier) (hq : Q.Valid q) (hr : Q.Valid r) :
    Q.entryMultiset (merge q r) = Q.entryMultiset (merge r q) := by
  rw [Q.entryMultiset_merge merge hmerge q r hq hr,
    Q.entryMultiset_merge merge hmerge r q hr hq, add_comm]

theorem priorityMultiset_merge_comm (Q : ExactQueue.{u,v,z} α π)
    (merge : Q.Carrier → Q.Carrier → Q.Carrier)
    (hmerge : MergeLaws Q.entries Q.Valid merge)
    (q r : Q.Carrier) (hq : Q.Valid q) (hr : Q.Valid r) :
    Q.priorityMultiset (merge q r) = Q.priorityMultiset (merge r q) :=
  congrArg (Multiset.map (Prod.snd : α × π → π))
    (Q.entryMultiset_merge_comm merge hmerge q r hq hr)

/-- Both parenthesizations use the actual validity of their intermediate merge. -/
theorem entryMultiset_merge_assoc (Q : ExactQueue.{u,v,z} α π)
    (merge : Q.Carrier → Q.Carrier → Q.Carrier)
    (hmerge : MergeLaws Q.entries Q.Valid merge)
    (q r s : Q.Carrier) (hq : Q.Valid q) (hr : Q.Valid r) (hs : Q.Valid s) :
    Q.entryMultiset (merge (merge q r) s) =
      Q.entryMultiset (merge q (merge r s)) := by
  calc
    Q.entryMultiset (merge (merge q r) s) =
        Q.entryMultiset (merge q r) + Q.entryMultiset s :=
      Q.entryMultiset_merge merge hmerge (merge q r) s (hmerge.valid q r hq hr) hs
    _ = (Q.entryMultiset q + Q.entryMultiset r) + Q.entryMultiset s := by
      rw [Q.entryMultiset_merge merge hmerge q r hq hr]
    _ = Q.entryMultiset q + (Q.entryMultiset r + Q.entryMultiset s) :=
      add_assoc _ _ _
    _ = Q.entryMultiset q + Q.entryMultiset (merge r s) := by
      rw [Q.entryMultiset_merge merge hmerge r s hr hs]
    _ = Q.entryMultiset (merge q (merge r s)) :=
      (Q.entryMultiset_merge merge hmerge q (merge r s) hq
        (hmerge.valid r s hr hs)).symm

theorem priorityMultiset_merge_assoc (Q : ExactQueue.{u,v,z} α π)
    (merge : Q.Carrier → Q.Carrier → Q.Carrier)
    (hmerge : MergeLaws Q.entries Q.Valid merge)
    (q r s : Q.Carrier) (hq : Q.Valid q) (hr : Q.Valid r) (hs : Q.Valid s) :
    Q.priorityMultiset (merge (merge q r) s) =
      Q.priorityMultiset (merge q (merge r s)) :=
  congrArg (Multiset.map (Prod.snd : α × π → π))
    (Q.entryMultiset_merge_assoc merge hmerge q r s hq hr hs)

theorem entryMultiset_empty_merge (Q : ExactQueue.{u,v,z} α π)
    (merge : Q.Carrier → Q.Carrier → Q.Carrier)
    (hmerge : MergeLaws Q.entries Q.Valid merge)
    (q : Q.Carrier) (hq : Q.Valid q) :
    Q.entryMultiset (merge Q.empty q) = Q.entryMultiset q := by
  rw [Q.entryMultiset_merge merge hmerge Q.empty q Q.empty_valid hq,
    Q.entryMultiset_empty, zero_add]

theorem priorityMultiset_empty_merge (Q : ExactQueue.{u,v,z} α π)
    (merge : Q.Carrier → Q.Carrier → Q.Carrier)
    (hmerge : MergeLaws Q.entries Q.Valid merge)
    (q : Q.Carrier) (hq : Q.Valid q) :
    Q.priorityMultiset (merge Q.empty q) = Q.priorityMultiset q :=
  congrArg (Multiset.map (Prod.snd : α × π → π))
    (Q.entryMultiset_empty_merge merge hmerge q hq)

theorem entryMultiset_merge_empty (Q : ExactQueue.{u,v,z} α π)
    (merge : Q.Carrier → Q.Carrier → Q.Carrier)
    (hmerge : MergeLaws Q.entries Q.Valid merge)
    (q : Q.Carrier) (hq : Q.Valid q) :
    Q.entryMultiset (merge q Q.empty) = Q.entryMultiset q := by
  rw [Q.entryMultiset_merge merge hmerge q Q.empty hq Q.empty_valid,
    Q.entryMultiset_empty, add_zero]

theorem priorityMultiset_merge_empty (Q : ExactQueue.{u,v,z} α π)
    (merge : Q.Carrier → Q.Carrier → Q.Carrier)
    (hmerge : MergeLaws Q.entries Q.Valid merge)
    (q : Q.Carrier) (hq : Q.Valid q) :
    Q.priorityMultiset (merge q Q.empty) = Q.priorityMultiset q :=
  congrArg (Multiset.map (Prod.snd : α × π → π))
    (Q.entryMultiset_merge_empty merge hmerge q hq)

/-- The actual merged state is valid before the singleton insertion preserves it. -/
theorem mergeInsert_valid (Q : ExactQueue.{u,v,z} α π)
    (merge : Q.Carrier → Q.Carrier → Q.Carrier)
    (hmerge : MergeLaws Q.entries Q.Valid merge)
    (e : α × π) (q r : Q.Carrier) (hq : Q.Valid q) (hr : Q.Valid r) :
    Q.Valid (Q.add [e] (merge q r)) :=
  Q.add_valid [e] (merge q r) (hmerge.valid q r hq hr)

/-- Exact input content of the sequential client before its actual removal. -/
theorem entryMultiset_mergeInsert (Q : ExactQueue.{u,v,z} α π)
    (merge : Q.Carrier → Q.Carrier → Q.Carrier)
    (hmerge : MergeLaws Q.entries Q.Valid merge)
    (e : α × π) (q r : Q.Carrier) (hq : Q.Valid q) (hr : Q.Valid r) :
    Q.entryMultiset (Q.add [e] (merge q r)) =
      e ::ₘ (Q.entryMultiset q + Q.entryMultiset r) := by
  change Q.entryMultiset (Q.toOperations.insertOne e (merge q r)) =
    e ::ₘ (Q.entryMultiset q + Q.entryMultiset r)
  rw [Q.entryMultiset_insertOne, Q.entryMultiset_merge merge hmerge q r hq hr]

theorem priorityMultiset_mergeInsert (Q : ExactQueue.{u,v,z} α π)
    (merge : Q.Carrier → Q.Carrier → Q.Carrier)
    (hmerge : MergeLaws Q.entries Q.Valid merge)
    (e : α × π) (q r : Q.Carrier) (hq : Q.Valid q) (hr : Q.Valid r) :
    Q.priorityMultiset (Q.add [e] (merge q r)) =
      e.2 ::ₘ (Q.priorityMultiset q + Q.priorityMultiset r) := by
  change Q.priorityMultiset (Q.toOperations.insertOne e (merge q r)) =
    e.2 ::ₘ (Q.priorityMultiset q + Q.priorityMultiset r)
  rw [Q.priorityMultiset_insertOne, Q.priorityMultiset_merge merge hmerge q r hq hr]

/-- A singleton is present after insertion, regardless of raw validity or merge laws. -/
theorem mergeInsert_nonempty (Q : ExactQueue.{u,v,z} α π)
    (merge : Q.Carrier → Q.Carrier → Q.Carrier)
    (e : α × π) (q r : Q.Carrier) :
    Q.priorityMultiset (Q.add [e] (merge q r)) ≠ 0 := by
  change Q.priorityMultiset (Q.toOperations.insertOne e (merge q r)) ≠ 0
  rw [Q.priorityMultiset_insertOne]
  exact Multiset.cons_ne_zero

/-- Singleton insertion forces a successful result, even before validity is supplied. -/
theorem mergeInsertRemove_exists (Q : ExactQueue.{u,v,z} α π)
    (merge : Q.Carrier → Q.Carrier → Q.Carrier)
    (e : α × π) (q r : Q.Carrier) :
    ∃ a s, mergeInsertRemove Q.toOperations merge e q r = some (a,s) := by
  obtain ⟨a, s, h⟩ := Q.exists_remove_of_ne_zero (Q.add [e] (merge q r))
    (Q.mergeInsert_nonempty merge e q r)
  exact ⟨a, s, by simpa only [mergeInsertRemove] using h⟩

/--
The actual client result retains its intermediate validity, nonempty input,
one-occurrence decompositions, least priority, and exact residual cardinalities.
-/
theorem mergeInsertRemove_spec (Q : ExactQueue.{u,v,z} α π)
    (merge : Q.Carrier → Q.Carrier → Q.Carrier)
    (hmerge : MergeLaws Q.entries Q.Valid merge)
    (e : α × π) (q r : Q.Carrier) (hq : Q.Valid q) (hr : Q.Valid r)
    (a : α × π) (s : Q.Carrier)
    (h : mergeInsertRemove Q.toOperations merge e q r = some (a,s)) :
    Q.Valid (merge q r) ∧
      Q.Valid (Q.add [e] (merge q r)) ∧
      Q.priorityMultiset (Q.add [e] (merge q r)) ≠ 0 ∧
      Q.Valid s ∧
      e ::ₘ (Q.entryMultiset q + Q.entryMultiset r) = a ::ₘ Q.entryMultiset s ∧
      e.2 ::ₘ (Q.priorityMultiset q + Q.priorityMultiset r) =
        a.2 ::ₘ Q.priorityMultiset s ∧
      IsLeast {p | p ∈ e.2 ::ₘ (Q.priorityMultiset q + Q.priorityMultiset r)} a.2 ∧
      (Q.entryMultiset s).card = (Q.entryMultiset q).card + (Q.entryMultiset r).card ∧
      (Q.priorityMultiset s).card =
        (Q.priorityMultiset q).card + (Q.priorityMultiset r).card := by
  have hm : Q.Valid (merge q r) := hmerge.valid q r hq hr
  have hi : Q.Valid (Q.add [e] (merge q r)) :=
    Q.mergeInsert_valid merge hmerge e q r hq hr
  have hremove : Q.remove (Q.add [e] (merge q r)) = some (a,s) :=
    h
  rcases Q.remove_spec_multiset (Q.add [e] (merge q r)) a s hi hremove with
    ⟨hs, _, he, hleast, hp⟩
  have hinputE := Q.entryMultiset_mergeInsert merge hmerge e q r hq hr
  have hinputP := Q.priorityMultiset_mergeInsert merge hmerge e q r hq hr
  have hentry : e ::ₘ (Q.entryMultiset q + Q.entryMultiset r) =
      a ::ₘ Q.entryMultiset s := hinputE.symm.trans he
  have hpriority : e.2 ::ₘ (Q.priorityMultiset q + Q.priorityMultiset r) =
      a.2 ::ₘ Q.priorityMultiset s := hinputP.symm.trans hp
  have hmin : IsLeast
      {p | p ∈ e.2 ::ₘ (Q.priorityMultiset q + Q.priorityMultiset r)} a.2 := by
    simpa only [hinputP] using hleast
  have hcardE : (Q.entryMultiset s).card =
      (Q.entryMultiset q).card + (Q.entryMultiset r).card := by
    have hc := Q.remove_card (Q.add [e] (merge q r)) a s hi hremove
    rw [hinputE, Multiset.card_cons, Multiset.card_add] at hc
    exact Nat.add_right_cancel hc
  have hcardP : (Q.priorityMultiset s).card =
      (Q.priorityMultiset q).card + (Q.priorityMultiset r).card := by
    have hc := Q.remove_priority_card (Q.add [e] (merge q r)) a s hi hremove
    rw [hinputP, Multiset.card_cons, Multiset.card_add] at hc
    exact Nat.add_right_cancel hc
  exact ⟨hm, hi, Q.mergeInsert_nonempty merge e q r,
    hs, hentry, hpriority, hmin, hcardE, hcardP⟩

end ExactQueue

end Search.PriorityInterface

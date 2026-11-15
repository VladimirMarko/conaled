import Applications.Sequences.CursorExtension
import Examples.AbstractFIFO

/-! Checked old/new clients and rejected admission for the experimental cursor
semantic type. The independent meaning is a list with its selected Fin index. -/
namespace Examples.SemanticTypeExtension
open Sequences.AbstractFIFO Sequences.AbstractFIFO.CursorExtension Sequences.Symmetric

/-- Runtime measure examines both physical segments, not an abstract decoder. -/
def size (q : SymList Nat) : Nat := q.1.length + q.2.length

theorem admissible : Admissible (representation Nat).Rel size := by
  intro q xs h
  rw [← h.2]
  simp [size, fromSL]

abbrev runtime := Cursor (SymList Nat) size
abbrev semantic := Cursor (List Nat) List.length

def left : runtime := ⟨AbstractFIFO.leftLayout, ⟨2, by decide⟩⟩
def right : runtime := ⟨AbstractFIFO.rightLayout, ⟨2, by decide⟩⟩
def chosen : semantic := ⟨[1,2,3], ⟨2, by decide⟩⟩

theorem left_related : Related (representation Nat).Rel left chosen :=
  ⟨AbstractFIFO.left_related, rfl⟩
theorem right_related : Related (representation Nat).Rel right chosen :=
  ⟨AbstractFIFO.right_related, rfl⟩

/-- Selected existing public client theorem, with its original Simulation
premise discharged by admission and new-rule compatibility. -/
theorem retained_ordinary :
    AbstractFIFO.ordinary (ops (symmetric Nat) size) (ops (symmetric Nat) size).empty = some 2 :=
  AbstractFIFO.ordinary_correct _ _ (extension _ (symmetric_correct Nat) admissible)

/-- The same extension from an arbitrary nonempty, nonzero selected cursor. -/
theorem retained_head :
    client (ops (symmetric Nat) size) [.delete,.enqueue 4] left = some 2 :=
  (old_client _ (symmetric_correct Nat) admissible _ ⟨chosen,left_related,rfl⟩).trans rfl

/-- The new semantic computation is independently a list update with clipping. -/
theorem expected_semantics :
    run (ops (lists Nat) List.length) [.delete,.enqueue 4] chosen =
      (⟨[2,3,4], ⟨2, by decide⟩⟩ : semantic) := rfl

theorem retained_cursor :
    Related (representation Nat).Rel
      (run (ops (symmetric Nat) size) [.delete,.enqueue 4] left)
      (⟨[2,3,4], ⟨2, by decide⟩⟩ : semantic) := by
  have h := run_retains _ (symmetric_correct Nat) admissible [.delete,.enqueue 4] left_related
  rw [expected_semantics] at h
  exact h

/-- Actual dependent equality at the output family Fin(length [2,3,4] + 1). -/
theorem retained_selected :
    Fin.cast (congrArg (fun n => n + 1) (admissible _ _ retained_cursor.1))
      (run (ops (symmetric Nat) size) [.delete,.enqueue 4] left).position =
        (⟨2, by decide⟩ : Fin ([2,3,4].length + 1)) :=
  selected_transport admissible retained_cursor

/-- The direct proof has the same inputs, semantic result and selected index. -/
theorem direct_cursor :
    Related (representation Nat).Rel
      (run (ops (symmetric Nat) size) [.delete,.enqueue 4] left)
      (⟨[2,3,4], ⟨2, by decide⟩⟩ : semantic) := by
  have h := direct_run _ (symmetric_correct Nat) admissible [.delete,.enqueue 4] left_related
  rw [expected_semantics] at h
  exact h

/-- Direct and reusable routes prove the same head observation on the same word. -/
theorem direct_head :
    client (ops (symmetric Nat) size) [.delete,.enqueue 4] left = some 2 :=
  (symmetric_correct Nat).head _ _ direct_cursor.1

/-- Deleting all three elements clips the selected end position down to zero. -/
example : Related (representation Nat).Rel
    (run (ops (symmetric Nat) size) [.delete,.delete,.delete] right)
    (⟨[], ⟨0, by decide⟩⟩ : semantic) :=
  run_retains _ (symmetric_correct Nat) admissible [.delete,.delete,.delete] right_related

/-- A constructor selects the end position and transports it across distinct
physical layouts. The witness is not chosen anew by the interpretation. -/
example : Related (representation Nat).Rel
    (⟨AbstractFIFO.rightLayout, ⟨3, by decide⟩⟩ : runtime)
    ⟨[1,2,3], Fin.cast (congrArg (fun n => n+1)
      (admissible _ _ AbstractFIFO.right_related)) ⟨3, by decide⟩⟩ :=
  select_related admissible AbstractFIFO.right_related _

/-- Empty and excessive deletions preserve a real inhabitant, index zero. -/
example : Related (representation Nat).Rel
    (run (ops (symmetric Nat) size) [.delete,.delete] (ops (symmetric Nat) size).empty)
    (⟨[], ⟨0, by decide⟩⟩ : semantic) :=
  run_retains _ (symmetric_correct Nat) admissible [.delete,.delete]
    (c := (ops (symmetric Nat) size).empty)
    (d := (ops (lists Nat) List.length).empty) ⟨⟨inv_nilSL,rfl⟩,rfl⟩

/-- This observation detects information absent from the old queue type. -/
def position (c : semantic) : Nat := c.position.val

theorem same_queue_distinct_position :
    (⟨[1,2,3], ⟨0, by decide⟩⟩ : semantic).value = chosen.value ∧
    position ⟨[1,2,3], ⟨0, by decide⟩⟩ ≠ position chosen := by decide

/-- Counting only one segment fails the new semantic type's admission law.
The original relation and independently specified List.length are unchanged. -/
theorem front_size_inadmissible :
    ¬ Admissible (representation Nat).Rel (fun q => q.1.length) := by
  intro h
  have bad := h AbstractFIFO.leftLayout [1,2,3] AbstractFIFO.left_related
  simp [AbstractFIFO.leftLayout] at bad

/-- Resetting every selected index would satisfy the erased queue observation
but cannot be admitted as the identity operation on the richer semantic type. -/
def reset (c : runtime) : runtime := ⟨c.value, ⟨0, Nat.zero_lt_succ _⟩⟩

theorem reset_old_view (c : runtime) : (reset c).value = c.value := rfl

theorem reset_not_identity :
    ¬ (∀ c d, Related (representation Nat).Rel c d →
      Related (representation Nat).Rel (reset c) d) := by
  intro h
  have bad := (h left chosen left_related).2
  simp [reset, left, chosen] at bad

end Examples.SemanticTypeExtension

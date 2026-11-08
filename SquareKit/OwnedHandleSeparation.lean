import SquareKit.OwnedHandle

/-! A native footprint contract, independent of the mode interpretation. -/
namespace SquareKit.OwnedHandle

abbrev Heap := Bool → Option (Nat × Nat)
def disjoint (h k : Heap) : Prop := ∀ a, h a = none ∨ k a = none
def union (h k : Heap) : Heap := fun a => (h a).or (k a)
def Sep (P Q : Heap → Prop) (h : Heap) : Prop :=
  ∃ left right, disjoint left right ∧ h = union left right ∧ P left ∧ Q right

def singleton (h : Bool) (owner value : Nat) : Heap :=
  Function.update (fun _ => none) h (some (owner,value))
def pointsTo (h : Bool) (owner value : Nat) : Heap → Prop :=
  fun heap => heap = singleton h owner value

theorem no_separating_alias (h : Bool) (a b v w : Nat) (heap : Heap) :
    ¬ Sep (pointsTo h a v) (pointsTo h b w) heap := by
  rintro ⟨left, right, hd, _, rfl, rfl⟩
  have := hd h
  simp [singleton] at this

/-- The second owned slot survives a successful transition on the first. -/
theorem frame_live {cmd : Command} {s t : State} (ha : Acts cmd s t) (k : Bool)
    (apart : match cmd with | .transfer h _ _ => k ≠ h | .consume h _ => k ≠ h) :
    liveHeap t k = liveHeap s k := by
  unfold liveHeap
  rw [frame_slot ha k apart]

/-- Consumption publishes the exact selected value, while deleting live ownership. -/
theorem consumption_contract {s t : State} {h : Bool} {a : Nat}
    (ha : Acts (.consume h a) s t) :
    ∃ value, liveHeap s h = some (a,value) ∧ liveHeap t h = none ∧
      t.returned = s.returned ++ [value] := by
  cases ha with
  | consume s h a c hp hl ho hf =>
    exact ⟨c.value, by simp [liveHeap, hp, hl, ho], by simp [liveHeap, replace], rfl⟩

/-- A native finish contract checks live ownership, not receipt count. -/
def Finished (s : State) : Prop := s.failed = false ∧ ∀ h, liveHeap s h = none

/-- Removing a command's footprint leaves the entire frame heap unchanged. -/
def remainder (heap : Heap) (h : Bool) : Heap := Function.update heap h none

theorem frame_remainder {cmd : Command} {s t : State} (ha : Acts cmd s t) :
    remainder (liveHeap t) (target cmd) =
      remainder (liveHeap s) (target cmd) := by
  funext k
  cases cmd with
  | transfer h a b =>
    by_cases hk : k = h
    · subst k; simp [remainder, target]
    · simp only [target, remainder, Function.update_of_ne hk]
      exact frame_live ha k hk
  | consume h a =>
    by_cases hk : k = h
    · subst k; simp [remainder, target]
    · simp only [target, remainder, Function.update_of_ne hk]
      exact frame_live ha k hk

/-- Every predicate of the disjoint remainder is retained, not only a scalar count. -/
theorem frame_predicate {cmd : Command} {s t : State} (ha : Acts cmd s t)
    (P : Heap → Prop)
    (hp : P (remainder (liveHeap s) (target cmd))) :
    P (remainder (liveHeap t) (target cmd)) := by
  rw [frame_remainder ha]
  exact hp

end SquareKit.OwnedHandle

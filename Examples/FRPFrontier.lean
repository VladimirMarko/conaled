import Applications.FRP.Frontier

/-! Checked cases for the complete-window experiment. At time 2 the left source
has [3, 3] and the right has [7]. The expected merge is [3, 3, 7]. -/
namespace Examples.FRPFrontier
open FRPSpec.Frontier

def left : State ℚ Nat := ⟨3, [(2, [3, 3])]⟩
def right : State ℚ Nat := ⟨3, [(2, [7])]⟩
def leftTruth (t : ℚ) : List Nat := if t = 2 then [3, 3] else []
def rightTruth (t : ℚ) : List Nat := if t = 2 then [7] else []

theorem left_accepted : advance (initial 2) 3 [(2, [3, 3])] = some left := by
  decide

theorem left_sound : left.Completes leftTruth := by
  apply advance_sound (s := initial 2) (xs := [(2, [3, 3])]) (w := 3)
  · simp [State.Valid, initial]
  · intro t ht
    simp [initial] at ht
    simp [batch, initial, leftTruth, ne_of_lt ht]
  · exact left_accepted
  · intro t _ _
    simp [batch, leftTruth, eq_comm]

theorem right_sound : right.Completes rightTruth := by
  apply advance_sound (s := initial 2) (xs := [(2, [7])]) (w := 3)
  · simp [State.Valid, initial]
  · intro t ht
    simp [initial] at ht
    simp [batch, initial, rightTruth, ne_of_lt ht]
  · decide
  · intro t _ _
    simp [batch, rightTruth, eq_comm]

/-- Public observation soundness connects the executable output to both truths. -/
theorem ordered_duplicates : leftTruth 2 ++ rightTruth 2 = [3, 3, 7] := by
  exact (observeMerge_sound (l := left) (r := right) (t := 2)
    (out := [3, 3, 7]) (by decide) leftTruth rightTruth left_sound right_sound).symm

/-- A silent source whose frontier equals the query still blocks output. -/
example : observeMerge left (initial 2) 2 = none := by decide

/-- Advancing a silent source certifies absence, enabling the left batch. -/
example : (do
    let quiet ← advance (initial 2 : State ℚ Nat) 3 []
    observeMerge left quiet 2) = some [3, 3] := by decide

/-- A packet cannot revise a closed timestamp. -/
example : advance left 4 [(2, [9])] = none := by decide

/-- A packet cannot claim closure of its own frontier timestamp. -/
example : advance (initial 2 : State ℚ Nat) 3 [(3, [9])] = none := by decide

example : advance left 2 [] = none := by decide

/-- Fragments in a single packet retain their order and duplicates. -/
example : (do
    let s ← advance (initial 2 : State ℚ Nat) 3 [(2, [3]), (2, [3])]
    observeMerge s right 2) = some [3, 3, 7] := by decide

/-- Different packet layouts can describe the same known source. -/
def fragmented : State ℚ Nat := ⟨3, [(2, [3]), (2, [3])]⟩

theorem fragmented_sound : fragmented.Completes leftTruth := by
  intro t _
  by_cases h : t = 2 <;> simp [fragmented, batch, leftTruth, h, eq_comm]

theorem layout_independent {a b : List Nat}
    (ha : observeMerge left right 2 = some a)
    (hb : observeMerge fragmented right 2 = some b) : a = b :=
  observations_agree left_sound right_sound fragmented_sound right_sound ha hb

/-- The frontier exclusion is necessary: two valid completions disagree at it. -/
example : (initial 2 : State ℚ Nat).Completes (fun _ => []) ∧
    (initial 2 : State ℚ Nat).Completes leftTruth ∧
    ([] : List Nat) ≠ leftTruth 2 := by
  refine ⟨?_, ?_, by decide⟩
  · intro t _; rfl
  · intro t ht
    simp [initial] at ht
    simp [initial, batch, leftTruth, ne_of_lt ht]

/-- Mapping the merged batch uses shared relational-square composition. -/
example : ([3, 3, 7] : List Nat).map (· + 1) = [4, 4, 8] := by
  have h := (mappedMergeObservation (fun n : Nat => n + 1) (2 : ℚ)).preserves
    (r := (left, right)) (s := (leftTruth, rightTruth)) ⟨left_sound, right_sound⟩
  have result := h [4, 4, 8] (by
    change (observeMerge left right (2 : ℚ)).map (List.map (fun n => n + 1)) =
      some [4, 4, 8]
    decide)
  exact result.symm

/-- Instantiate the existing real-time prefix contract through the exact bridge. -/
example (s : State ℝ Nat) (e : FRPSpec.Event Nat) (h : s.Completes e.at) :
    (toPrefix s).Sound e := (completes_iff_prefix_sound s e).mp h

end Examples.FRPFrontier

import Applications.ClassicalControl.Machine

/-! Termination and full certificates for the selected finite search. These are
runtime invariants, independent of realizability or membership in a pole. -/
namespace ClassicalControl

def scanResult (j : Nat) (O : List Nat) : List Nat → Value
  | [] => .none O
  | n::ns => if n % 2 = 0 then .found j n (n/2) O
      else scanResult (j+1) (O++[n/2]) ns

/-- The invariant is an exact decomposition into certified odd pre and remaining suffix. -/
theorem scan_first (rest : List Nat) (O : List Nat) :
    First (oddNumerals O ++ rest) (scanResult O.length O rest) := by
  induction rest generalizing O with
  | nil => simp [scanResult, First]
  | cons n ns ih =>
    simp only [scanResult]
    split_ifs with hn
    · exact ⟨rfl, parity_even n hn, ns, rfl⟩
    · have he : oddNumerals O ++ n::ns = oddNumerals (O++[n/2]) ++ ns := by
        simp only [oddNumerals, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]; rw [← parity_odd n hn]
      rw [he]
      simpa using ih (O++[n/2])

/-- Prefix extension retains the complete observation, not only its numeral. -/
def extend (j : Nat) (O : List Nat) : Value → Value
  | .found i n h W => .found (j+i) n h (O++W)
  | .none W => .none (O++W)
  | .odd h => .odd h

theorem scan_direct (rest : List Nat) (j : Nat) (O : List Nat) :
    scanResult j O rest = extend j O (direct rest) := by
  induction rest generalizing j O with
  | nil => simp [scanResult, direct, extend]
  | cons n ns ih =>
    simp only [scanResult, direct]
    split_ifs with hn
    · simp [extend]
    · rw [ih]
      cases direct ns <;> simp [extend, prependOdd, List.append_assoc, Nat.add_comm, Nat.add_left_comm]

theorem scan_empty_direct (L : List Nat) : scanResult 0 [] L = direct L := by
  rw [scan_direct]; cases direct L <;> simp [extend]

namespace Source

def search (L : List Nat) : Term 0 := .app .cc (.lam (.walk (.var 0) L 0 []))

theorem search_initialize (L : List Nat) :
    Runs (.run (search L) (.out L)) (.run (.walk (.saved (.out L)) L 0 []) (.out L)) := by
  apply (Relation.ReflTransGen.single Step.app).trans
  apply (Relation.ReflTransGen.single Step.capture).trans
  exact Relation.ReflTransGen.single Step.beta

/-- A boundary run terminates by induction on its finite unvisited suffix. -/
theorem walk_terminates (rest pre : List Nat) (O : List Nat) :
    Runs (.run (.walk (.saved (.out (pre++rest))) (pre++rest) pre.length O)
        (.out (pre++rest)))
      (.deliver (pre++rest) (scanResult pre.length O rest)) := by
  induction rest generalizing pre O with
  | nil =>
    simpa [scanResult] using
      (Relation.ReflTransGen.single (Step.exhausted (k := .saved (.out pre)) (π := .out pre) (O := O))).trans
        (Relation.ReflTransGen.single Step.output)
  | cons n ns ih =>
    apply (Relation.ReflTransGen.single (Step.walk (by simp))).trans
    simp only [scanResult]
    split_ifs with hn
    · have he : (pre ++ n::ns)[pre.length]? = some (2*(n/2)) := by
        simp [← parity_even n hn]
      apply (Relation.ReflTransGen.single (Step.even he)).trans
      apply (Relation.ReflTransGen.single Step.restore).trans
      have heq := parity_even n hn
      rw [← heq]
      exact Relation.ReflTransGen.single Step.output
    · have ho : (pre ++ n::ns)[pre.length]? = some (2*(n/2)+1) := by
        simp [← parity_odd n hn]
      apply (Relation.ReflTransGen.single (Step.odd ho)).trans
      apply (Relation.ReflTransGen.single (Step.callback ⟨_, _, _, _, fun _ => rfl⟩)).trans
      simpa [callback, List.append_assoc] using ih (pre++[n]) (O++[n/2])

theorem search_runs_direct (L : List Nat) :
    Runs (.run (search L) (.out L)) (.deliver L (direct L)) := by
  apply (search_initialize L).trans
  simpa [scan_empty_direct] using walk_terminates L [] []

theorem search_full_result (L : List Nat) :
    ∃ z, Runs (.run (search L) (.out L)) (.deliver L z) ∧ First L z :=
  ⟨direct L, search_runs_direct L, direct_first L⟩

/-- Actual search membership is derived from its execution, not postulated. -/
theorem search_good : Pgood.holds (.run (search L₀) (.out L₀)) :=
  ⟨direct L₀, by simp [direct, prependOdd, Weak], search_runs_direct L₀⟩

/-- Every possible delivered observation agrees with direct recursion. -/
theorem search_delivery_eq {L K : List Nat} {z : Value}
    (h : Runs (.run (search L) (.out L)) (.deliver K z)) : K = L ∧ z = direct L :=
  delivery_unique h (search_runs_direct L)

/-- Accessibility excludes divergent executions of this finite-input program. -/
theorem search_normalizes (L : List Nat) :
    Acc (fun t s => Step s t) (.run (search L) (.out L)) :=
  normalizes_of_delivery (search_runs_direct L)

/-- Correctness from any boundary satisfying the complete ordered-prefix invariant. -/
theorem certified_boundary (O rest : List Nat) :
    Runs (.run (.walk (.saved (.out (oddNumerals O ++ rest))) (oddNumerals O ++ rest)
        O.length O) (.out (oddNumerals O ++ rest)))
      (.deliver (oddNumerals O ++ rest) (scanResult O.length O rest)) ∧
    First (oddNumerals O ++ rest) (scanResult O.length O rest) := by
  exact ⟨by simpa [oddNumerals] using walk_terminates rest (oddNumerals O) O, scan_first rest O⟩

end Source
end ClassicalControl

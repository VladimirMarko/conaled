import Applications.ClassicalControl.Search

/-! Continuing after an even entry changes the selected observation. It is not
covered by the representation simulation. -/
namespace ClassicalControl.Source

def lastResult (j : Nat) (c : Option (Nat × Nat × Nat)) (O : List Nat) : List Nat → Value
  | [] => finish c O
  | n::ns => if n % 2 = 0 then lastResult (j+1) (some (j,n,n/2)) O ns
      else lastResult (j+1) c (O++[n/2]) ns

theorem last_terminates (rest pre : List Nat) (c : Option (Nat × Nat × Nat)) (O : List Nat) :
    Runs (.run (.last (pre++rest) pre.length c O) (.out (pre++rest)))
      (.deliver (pre++rest) (lastResult pre.length c O rest)) := by
  induction rest generalizing pre c O with
  | nil =>
    simpa [lastResult] using
      (Relation.ReflTransGen.single (Step.lastEnd (L := pre) (π := .out pre) (c := c) (O := O))).trans
        (Relation.ReflTransGen.single Step.output)
  | cons n ns ih =>
    simp only [lastResult]
    split_ifs with hn
    · have he : (pre ++ n::ns)[pre.length]? = some (2*(n/2)) := by
        simp [← parity_even n hn]
      apply (Relation.ReflTransGen.single (Step.lastEven he)).trans
      have heq := parity_even n hn
      convert ih (pre++[n]) (some (pre.length,n,n/2)) O using 1 <;>
        simp only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append]
      rw [← heq]
    · have ho : (pre ++ n::ns)[pre.length]? = some (2*(n/2)+1) := by
        simp [← parity_odd n hn]
      apply (Relation.ReflTransGen.single (Step.lastOdd ho)).trans
      simpa [List.append_assoc] using ih (pre++[n]) c (O++[n/2])

theorem changed_policy_runs :
    Runs (.run (.last L₀ 0 none []) (.out L₀)) (.deliver L₀ (.found 2 4 2 [])) := by
  simpa [lastResult, finish] using last_terminates L₀ [] none []

theorem changed_policy_good : Pgood.holds (.run (.last L₀ 0 none []) (.out L₀)) :=
  ⟨.found 2 4 2 [], by simp [Weak], changed_policy_runs⟩

theorem changed_policy_differs : direct L₀ ≠ Value.found 2 4 2 [] := by
  simp [direct, prependOdd]

end ClassicalControl.Source

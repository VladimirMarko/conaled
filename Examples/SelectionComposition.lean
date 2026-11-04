import Applications.Resources.SelectionBounds
import Examples.SelectionCosts

/-! Relabeling a measured selection can merge values. The rank certificate and
selected value transport, and both executions obey the same uniform affine
bound. The two actual work counts need not agree, as the final case shows.
-/
set_option autoImplicit false
set_option warningAsError true

universe u v

namespace Examples.SelectionComposition
open Applications.Selection
open Resources.Selection

/-- The constants precede both payload types, the map, input, rank and value.
No injectivity or distinctness is required. The premise specifies the input
rank, not a cost assumption; the costs are those of the two actual workers. -/
theorem monotone_ranked_costs :
    ∃ A B : Nat, ∀ (α : Type u) [LinearOrder α] (β : Type v) [LinearOrder β]
      (f : α → β) (_hf : Monotone f) (xs : List α) (k : Nat) (a : α),
      RankedAt xs k a →
        (selectRun k xs).1 = some a ∧
        RankedAt (xs.map f) k (f a) ∧
        (selectRun k (xs.map f)).1 = some (f a) ∧
        (selectRun k xs).2 ≤ A * xs.length + B ∧
        (selectRun k (xs.map f)).2 ≤ A * xs.length + B := by
  obtain ⟨A, B, bound⟩ := Resources.SelectionRecurrence.exists_affine_bound
  refine ⟨A, B, ?_⟩
  intro α instα β instβ f hf xs k a rank
  have mapped := rank.map f hf
  refine ⟨(selectRun_some_iff k xs a).mpr rank, mapped,
    (selectRun_some_iff k (xs.map f) (f a)).mpr mapped,
    (selectRun_cost_le_F k xs).trans (bound xs.length), ?_⟩
  simpa only [List.length_map] using
    (selectRun_cost_le_F k (xs.map f)).trans (bound (xs.map f).length)

/-- A constant relabeling is allowed, including when it identifies every
distinct input value. This is a symbolic consumer of the preceding result. -/
theorem constant_ranked_costs :
    ∃ A B : Nat, ∀ (α : Type u) [LinearOrder α] (β : Type v) [LinearOrder β]
      (b : β) (xs : List α) (k : Nat) (a : α),
      RankedAt xs k a →
        RankedAt (xs.map (fun _ => b)) k b ∧
        (selectRun k (xs.map (fun _ => b))).1 = some b ∧
        (selectRun k xs).2 ≤ A * xs.length + B ∧
        (selectRun k (xs.map (fun _ => b))).2 ≤ A * xs.length + B := by
  obtain ⟨A, B, bound⟩ := monotone_ranked_costs.{u, v}
  refine ⟨A, B, ?_⟩
  intro α instα β instβ b xs k a rank
  have h := bound α β (fun _ => b) (fun _ _ _ => le_rfl) xs k a rank
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- The first recursive size makes the distinction observable: merging the
21 different values into the value4 preserves rank20, but work drops from266 to239.
The same constants still bound both executions, through the symbolic client. -/
theorem collapsed_actual_work :
    ¬ Function.Injective (fun _ : Nat => (4 : Nat)) ∧
      selectRun 20 (List.range 21) = (some 20, 266) ∧
      selectRun 20 ((List.range 21).map (fun _ : Nat => (4 : Nat))) =
        (some 4, 239) ∧
      ∃ A B : Nat,
        RankedAt ((List.range 21).map (fun _ : Nat => (4 : Nat))) 20 4 ∧
        (selectRun 20 (List.range 21)).2 ≤ A * 21 + B ∧
        (selectRun 20 ((List.range 21).map (fun _ : Nat => (4 : Nat)))).2 ≤
          A * 21 + B := by
  have source := Examples.SelectionCosts.first_recursive_right
  have rank : RankedAt (List.range 21) 20 20 :=
    (selectRun_some_iff 20 (List.range 21) 20).mp (congrArg Prod.fst source)
  have shape : (List.range 21).map (fun _ : Nat => (4 : Nat)) =
      List.replicate 21 4 := by simp
  have target : selectRun 20 ((List.range 21).map (fun _ : Nat => (4 : Nat))) =
      (some 4, 239) := by
    rw [shape]
    exact Examples.SelectionCosts.all_equal_last
  obtain ⟨A, B, bound⟩ := constant_ranked_costs.{0, 0}
  have h := bound Nat Nat 4 (List.range 21) 20 20 rank
  refine ⟨?_, source, target, A, B, h.1, ?_, ?_⟩
  · intro injective
    have impossible : (0 : Nat) = 1 := injective rfl
    omega
  · simpa only [List.length_range] using h.2.2.1
  · simpa only [List.length_range] using h.2.2.2

end Examples.SelectionComposition

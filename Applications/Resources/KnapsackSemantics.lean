import Applications.Resources.Knapsack

/-! Exact selection and all-capacity semantics of the existing immutable row.
The recursive specification skips on value ties. Independent feasibility uses
input occurrences, so labels may repeat and positive zero-weight items fit. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources.Knapsack
open Optimization.KnapsackThinning
variable {α : Type}

/-- Source recursive selection, with skip before take and original item order. -/
def select (capacity : Nat) : List (Item α) → Selection α
  | [] => emptySelection
  | i :: items => if capacity < i.weight then select capacity items
      else better (select capacity items) (add i (select (capacity-i.weight) items))

theorem better_tie_skip (s t : Selection α) (he : s.value = t.value) : better s t = s := by
  simp [better, he]

theorem better_value_left (s t : Selection α) : s.value ≤ (better s t).value := by
  unfold better; split <;> simp_all; omega

theorem better_value_right (s t : Selection α) : t.value ≤ (better s t).value := by
  unfold better; split <;> simp_all

theorem select_feasible (capacity : Nat) (items : List (Item α)) :
    Feasible capacity items (select capacity items) := by
  induction items generalizing capacity with
  | nil => exact (feasible_nil_iff capacity _).mpr rfl
  | cons i items ih =>
    rw [select]
    split
    · exact (feasible_cons_iff _ _ _ _).mpr (.inl (ih capacity))
    · rename_i hc
      unfold better
      split
      · exact (feasible_cons_iff _ _ _ _).mpr (.inl (ih capacity))
      · exact (feasible_cons_iff _ _ _ _).mpr
          (.inr ⟨by omega, _, ih (capacity-i.weight), rfl⟩)

theorem select_value_bound (capacity : Nat) (items chosen : List (Item α))
    (hs : chosen.Sublist items) (hw : totalWeight chosen ≤ capacity) :
    totalValue chosen ≤ (select capacity items).value := by
  induction items generalizing capacity chosen with
  | nil =>
    have he := List.eq_nil_of_sublist_nil hs
    subst chosen
    simp [totalValue, select, emptySelection]
  | cons i items ih =>
    rcases List.sublist_cons_iff.mp hs with hs' | ⟨tail, rfl, ht⟩
    · rw [select]
      split
      · exact ih capacity chosen hs' hw
      · exact (ih capacity chosen hs' hw).trans (better_value_left _ _)
    · rw [totalWeight_cons] at hw
      have hc : ¬ capacity < i.weight := by omega
      have hi := ih (capacity-i.weight) tail ht (by omega)
      rw [select, ite_eq_right hc, totalValue_cons]
      exact (Nat.add_le_add_left hi i.value).trans (better_value_right (select capacity items) (add i (select (capacity-i.weight) items)))

theorem select_optimal (capacity : Nat) (items : List (Item α)) :
    Optimal capacity items (select capacity items) :=
  ⟨select_feasible capacity items, fun chosen hs hw => select_value_bound capacity items chosen hs hw⟩

/-- The existing dominance-pruned solver has the same optimum value; tie
selection is kept separate and no equality of chosen names is inferred. -/
theorem select_frontier_value (capacity : Nat) (items : List (Item α))
    (s : Selection α) (hs : solve capacity items = some s) :
    (select capacity items).value = s.value := by
  have ho := solve_optimal capacity items s hs
  obtain ⟨a,ha,wa,ea⟩ := select_feasible capacity items
  obtain ⟨b,hb,wb,eb⟩ := ho.1
  have h₁ := ho.2 a ha wa
  have h₂ := select_value_bound capacity items b hb wb
  have va := congrArg Selection.value ea
  have vb := congrArg Selection.value eb
  change totalValue a = _ at va
  change totalValue b = _ at vb
  omega

theorem select_names_bound (capacity : Nat) (items : List (Item α)) :
    (select capacity items).names.length ≤ items.length := by
  obtain ⟨chosen,hs,_,he⟩ := select_feasible capacity items
  rw [← he]
  simpa [summary] using hs.length_le

def start (capacity : Nat) : Array (Selection α) :=
  (List.replicate (capacity+1) emptySelection).toArray

def table (capacity : Nat) (items : List (Item α)) : Array (Selection α) :=
  items.foldr (step capacity) (start capacity)

def answer (capacity : Nat) (items : List (Item α)) : Selection α :=
  read (table capacity items) capacity

theorem step_size (capacity : Nat) (i : Item α) (old : Array (Selection α)) :
    (step capacity i old).size = old.size := DynamicProgramming.arrayAssign_size old _

theorem step_entry (capacity : Nat) (i : Item α) (old : Array (Selection α))
    (hs : old.size = capacity+1) (j : Nat) (hj : j ≤ capacity) :
    (step capacity i old)[j]? = some (next i old j) := by
  apply DynamicProgramming.arrayAssign_entry
  · simpa [List.map_map, Function.comp_def] using
      (List.nodup_range (n := capacity+1))
  · exact List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩
  · omega

theorem start_size (capacity : Nat) :
    (start capacity : Array (Selection α)).size = capacity+1 := by simp [start]

theorem start_entry (capacity j : Nat) (hj : j ≤ capacity) :
    (start capacity : Array (Selection α))[j]? = some emptySelection := by
  simp [start, show j < capacity+1 by omega]

theorem table_size (capacity : Nat) (items : List (Item α)) :
    (table capacity items).size = capacity+1 := by
  induction items with
  | nil => exact start_size capacity
  | cons i items ih => change (step capacity i (table capacity items)).size = _; rw [step_size,ih]

theorem table_entry (capacity : Nat) (items : List (Item α)) (j : Nat) (hj : j ≤ capacity) :
    (table capacity items)[j]? = some (select j items) := by
  induction items generalizing j with
  | nil => exact start_entry capacity j hj
  | cons i items ih =>
    change (step capacity i (table capacity items))[j]? = _
    rw [step_entry capacity i _ (table_size capacity items) j hj]
    simp only [next, read, ih j hj, Option.getD_some]
    by_cases hi : j < i.weight
    · rw [ite_eq_left hi, select, ite_eq_left hi]
    · rw [ite_eq_right hi, ih (j-i.weight) (by omega), Option.getD_some, select, ite_eq_right hi]

theorem table_read (capacity : Nat) (items : List (Item α)) (j : Nat) (hj : j ≤ capacity) :
    read (table capacity items) j = select j items := by
  rw [read,table_entry capacity items j hj]
  rfl

theorem table_read_bounds (capacity : Nat) (items : List (Item α)) (i : Item α)
    (j : Nat) (hj : j ≤ capacity) :
    j < (table capacity items).size ∧ j-i.weight < (table capacity items).size := by
  rw [table_size]; omega

theorem answer_eq_select (capacity : Nat) (items : List (Item α)) :
    answer capacity items = select capacity items := table_read capacity items capacity le_rfl

theorem answer_optimal (capacity : Nat) (items : List (Item α)) :
    Optimal capacity items (answer capacity items) := by
  rw [answer_eq_select]
  exact select_optimal capacity items

theorem table_entry_optimal (capacity : Nat) (items : List (Item α)) (j : Nat) (hj : j ≤ capacity) :
    Optimal j items (read (table capacity items) j) := by
  rw [table_read capacity items j hj]
  exact select_optimal j items

end Resources.Knapsack

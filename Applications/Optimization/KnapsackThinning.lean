import Applications.Optimization.Thinning
import Mathlib.Order.OrderDual

/-!
# Finite 0/1-knapsack by dominance pruning

Each input occurrence can be selected once; labels may repeat and weights may
be zero. Independent feasibility uses input sublists and checked cached fields.
This frontier reconstruction does not claim equality with the source's capacity
table or its chosen optimum on every tie. See the reconstruction record.
-/
namespace Optimization.KnapsackThinning
open Thinning
variable {α : Type}

structure Item (α : Type) where
  name : α
  value : Nat
  weight : Nat
  deriving DecidableEq

structure Selection (α : Type) where
  names : List α
  value : Nat
  weight : Nat
  deriving DecidableEq

def emptySelection : Selection α := ⟨[], 0, 0⟩

def totalValue (items : List (Item α)) : Nat := (items.map Item.value).sum

def totalWeight (items : List (Item α)) : Nat := (items.map Item.weight).sum

def summary (items : List (Item α)) : Selection α :=
  ⟨items.map Item.name, totalValue items, totalWeight items⟩

def add (i : Item α) (s : Selection α) : Selection α :=
  ⟨i.name :: s.names, i.value + s.value, i.weight + s.weight⟩

/-- The monotonicity premise used in the book's recursive derivation. -/
theorem add_value_monotone (i : Item α) (s t : Selection α) (h : s.value ≤ t.value) :
    (add i s).value ≤ (add i t).value := Nat.add_le_add_left h i.value

theorem totalValue_cons (i : Item α) (items : List (Item α)) :
    totalValue (i :: items) = i.value + totalValue items := by simp [totalValue]

theorem totalWeight_cons (i : Item α) (items : List (Item α)) :
    totalWeight (i :: items) = i.weight + totalWeight items := by simp [totalWeight]

theorem summary_nil : summary ([] : List (Item α)) = emptySelection := rfl

theorem summary_cons (i : Item α) (items : List (Item α)) :
    summary (i :: items) = add i (summary items) := by
  simp [summary, add, totalValue_cons, totalWeight_cons]

/-- Independent feasibility, including all three cached output fields. -/
def Feasible (capacity : Nat) (items : List (Item α)) (s : Selection α) : Prop :=
  ∃ chosen, chosen.Sublist items ∧ totalWeight chosen ≤ capacity ∧ summary chosen = s

/-- Global maximum over every feasible input sublist. -/
def Optimal (capacity : Nat) (items : List (Item α)) (s : Selection α) : Prop :=
  Feasible capacity items s ∧
    ∀ chosen, chosen.Sublist items → totalWeight chosen ≤ capacity → totalValue chosen ≤ s.value

theorem feasible_nil_iff (capacity : Nat) (s : Selection α) :
    Feasible capacity [] s ↔ s = emptySelection := by
  simp [Feasible, totalWeight, summary_nil, eq_comm]

theorem feasible_cons_iff (capacity : Nat) (i : Item α) (items : List (Item α))
    (s : Selection α) :
    Feasible capacity (i :: items) s ↔
      Feasible capacity items s ∨
        (i.weight ≤ capacity ∧
          ∃ t, Feasible (capacity - i.weight) items t ∧ add i t = s) := by
  constructor
  · rintro ⟨chosen, hs, hw, he⟩
    rcases List.sublist_cons_iff.mp hs with hs' | ⟨tail, rfl, ht⟩
    · exact Or.inl ⟨chosen, hs', hw, he⟩
    · rw [totalWeight_cons] at hw
      refine Or.inr ⟨by omega, summary tail, ⟨tail, ht, by omega, rfl⟩, ?_⟩
      rwa [← summary_cons]
  · rintro (h | ⟨hw, t, ⟨chosen, hs, hc, he⟩, ha⟩)
    · obtain ⟨chosen, hs, hc, he⟩ := h
      exact ⟨chosen, hs.cons i, hc, he⟩
    · refine ⟨i :: chosen, hs.cons_cons i, ?_, ?_⟩
      · rw [totalWeight_cons]
        omega
      · rw [summary_cons, he, ha]

def Dominates (s t : Selection α) : Prop := s.weight ≤ t.weight ∧ t.value ≤ s.value
instance : DecidableRel (Dominates (α := α)) := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

theorem dominates_refl (s : Selection α) : Dominates s s := ⟨le_rfl, le_rfl⟩
theorem dominates_trans (s t u : Selection α) (h : Dominates s t) (k : Dominates t u) :
    Dominates s u := ⟨le_trans h.1 k.1, le_trans k.2 h.2⟩

/-- Skip precedes take. Capacity is checked against the cached total weight. -/
def extend (capacity : Nat) (i : Item α) (s : Selection α) : List (Selection α) :=
  s :: (if (add i s).weight ≤ capacity then [add i s] else [])

def candidates (capacity : Nat) (items : List (Item α)) : List (Selection α) :=
  items.foldr (fun i ss => ss.flatMap (extend capacity i)) [emptySelection]

def frontier (capacity : Nat) (items : List (Item α)) : List (Selection α) :=
  pruneFold (fun i ss => ss.flatMap (extend capacity i)) (thinBy Dominates)
    [emptySelection] items

def objective (s : Selection α) : OrderDual Nat := s.value

def solve (capacity : Nat) (items : List (Item α)) : Option (Selection α) :=
  argmin objective (frontier capacity items)

theorem mem_extend_iff (capacity : Nat) (i : Item α) (s t : Selection α) :
    t ∈ extend capacity i s ↔ t = s ∨ (t = add i s ∧ (add i s).weight ≤ capacity) := by
  by_cases h : (add i s).weight ≤ capacity <;> simp [extend, h]

theorem extend_covers (capacity : Nat) (i : Item α) (s t : Selection α)
    (h : Dominates s t) : Covers Dominates (extend capacity i s) (extend capacity i t) := by
  intro u hu
  rcases (mem_extend_iff capacity i t u).mp hu with rfl | ⟨rfl, hw⟩
  · exact ⟨s, by simp [extend], h⟩
  · have hs : (add i s).weight ≤ capacity := le_trans (Nat.add_le_add_left h.1 _) hw
    refine ⟨add i s, (mem_extend_iff capacity i s _).mpr (Or.inr ⟨rfl, hs⟩), ?_⟩
    exact ⟨Nat.add_le_add_left h.1 _, Nat.add_le_add_left h.2 _⟩

theorem frontier_refinement (capacity : Nat) (items : List (Item α)) :
    Represents Dominates (candidates capacity items) (frontier capacity items) :=
  pruneFold_refinement Dominates dominates_refl dominates_trans
    (fun i ss => ss.flatMap (extend capacity i)) (thinBy Dominates)
    (fun i _ _ h => represents_flatMap _ (extend_covers capacity i) h)
    (fun ss => (thinBy_correct Dominates dominates_refl dominates_trans ss).represents)
    [emptySelection] items

/-- Enumeration is complete for feasible sublists, independently of thinning. -/
theorem mem_candidates_iff (capacity : Nat) (items : List (Item α)) (s : Selection α) :
    s ∈ candidates capacity items ↔ Feasible capacity items s := by
  induction items generalizing s with
  | nil => simp [candidates, feasible_nil_iff]
  | cons i items ih =>
    change s ∈ (candidates capacity items).flatMap (extend capacity i) ↔ _
    rw [List.mem_flatMap]
    constructor
    · rintro ⟨t, ht, hs⟩
      obtain ⟨chosen, hsub, hw, rfl⟩ := (ih t).mp ht
      rcases (mem_extend_iff capacity i (summary chosen) s).mp hs with rfl | ⟨rfl, hw'⟩
      · exact ⟨chosen, hsub.cons i, hw, rfl⟩
      · exact ⟨i :: chosen, hsub.cons_cons i, hw', summary_cons i chosen⟩
    · rintro ⟨chosen, hsub, hw, rfl⟩
      rcases List.sublist_cons_iff.mp hsub with hskip | ⟨tail, rfl, ht⟩
      · exact ⟨summary chosen, (ih _).mpr ⟨chosen, hskip, hw, rfl⟩,
          (mem_extend_iff capacity i _ _).mpr (Or.inl rfl)⟩
      · have hw' : totalWeight tail ≤ capacity := by rw [totalWeight_cons] at hw; omega
        refine ⟨summary tail, (ih _).mpr ⟨tail, ht, hw', rfl⟩, ?_⟩
        apply (mem_extend_iff capacity i _ _).mpr
        exact Or.inr ⟨summary_cons i tail, hw⟩

theorem solve_optimal (capacity : Nat) (items : List (Item α)) (s : Selection α)
    (hs : solve capacity items = some s) : Optimal capacity items s := by
  have hm := minimizer_of_represents (frontier_refinement capacity items) objective
    (fun _ _ _ _ h => h.2) (argmin_correct objective _ s hs)
  refine ⟨(mem_candidates_iff capacity items s).mp hm.1, ?_⟩
  intro chosen hsub hw
  exact hm.2 ((mem_candidates_iff capacity items _).mpr ⟨chosen, hsub, hw, rfl⟩)

theorem solve_ne_none (capacity : Nat) (items : List (Item α)) : solve capacity items ≠ none := by
  intro h
  have he := (argmin_eq_none_iff objective _).mp h
  have hc := (represents_empty_iff (frontier_refinement capacity items)).mp he
  have hm : emptySelection ∈ candidates capacity items :=
    (mem_candidates_iff capacity items _).mpr ⟨[], List.nil_sublist _, by simp [totalWeight], rfl⟩
  simp [hc] at hm

/-- Empty input is feasible and returns the empty selection at every capacity. -/
theorem empty_optimal (capacity : Nat) : Optimal capacity ([] : List (Item α)) emptySelection :=
  solve_optimal capacity [] emptySelection rfl

def sampleItems : List (Item Nat) := [⟨1, 6, 4⟩, ⟨2, 4, 3⟩, ⟨3, 5, 2⟩]

theorem sample_solution : solve 5 sampleItems = some ⟨[2, 3], 9, 5⟩ := by decide

theorem sample_optimal : Optimal 5 sampleItems ⟨[2, 3], 9, 5⟩ :=
  solve_optimal 5 sampleItems _ sample_solution

/-- Taking a zero-value zero-weight item ties with skipping it; skip wins here. -/
theorem zero_item_tie : solve 0 [Item.mk 7 0 0] = some emptySelection := by decide

theorem zero_item_optimal : Optimal 0 [Item.mk 7 0 0] emptySelection :=
  solve_optimal 0 _ _ zero_item_tie

end Optimization.KnapsackThinning

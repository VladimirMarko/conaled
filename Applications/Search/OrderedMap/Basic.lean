import Applications.Search.OrderedMap.Interface
import Applications.Search.OrderedTree.Basic

/-!
# Unbalanced ordered finite maps

PFDS Exercise 2.6 is realized by Mathlib trees of key/value pairs. `OrderedBy`
constrains only keys. The independent observation `observe` examines both
subtrees; the implementation `lookup` follows the ordered search path.

These are value-level laws. Heap allocation, physical subtree sharing and
runtime complexity require the separate shared-tree realization.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedMap
universe u
variable {κ ν : Type u}
open Search.OrderedTree (All OrderedBy Contains entries)

section Equality
variable [DecidableEq κ]

/-- Independent whole-tree meaning, with the root then left child taking
precedence in a possibly unordered tree. Ordered trees have unique keys. -/
def observe : BinaryTree (κ × ν) → Meaning κ ν
  | .nil => fun _ => none
  | .node binding left right => fun query =>
      if query = binding.1 then some binding.2
      else observe left query <|> observe right query

theorem observe_none_of_all_ne {query : κ} {t : BinaryTree (κ × ν)}
    (h : All (fun binding => query ≠ binding.1) t) : observe t query = none := by
  induction t with
  | nil => rfl
  | node binding left right ihl ihr =>
      simp [observe, h.1, ihl h.2.1, ihr h.2.2]

end Equality

section LinearOrder
variable [LinearOrder κ]

/-- Ordered-key search; missing bindings retain an explicit failure result. -/
def lookup (query : κ) : BinaryTree (κ × ν) → Option ν
  | .nil => none
  | .node binding left right =>
      if query < binding.1 then lookup query left
      else if binding.1 < query then lookup query right
      else some binding.2

/-- Matching keys replace their payload, and every other branch retains the
original binding. Values need neither equality nor ordering. -/
def bind (key : κ) (value : ν) : BinaryTree (κ × ν) → BinaryTree (κ × ν)
  | .nil => .node (key, value) .nil .nil
  | .node binding left right =>
      if key < binding.1 then .node binding (bind key value left) right
      else if binding.1 < key then .node binding left (bind key value right)
      else .node (key, value) left right

theorem all_bind {P : κ × ν → Prop} {t : BinaryTree (κ × ν)}
    (h : All P t) (key : κ) (value : ν) (new : P (key, value)) :
    All P (bind key value t) := by
  induction t with
  | nil => exact ⟨new, trivial, trivial⟩
  | node binding left right ihl ihr =>
      simp only [bind]
      split
      · exact ⟨h.1, ihl h.2.1, h.2.2⟩
      · split
        · exact ⟨h.1, h.2.1, ihr h.2.2⟩
        · exact ⟨new, h.2.1, h.2.2⟩

theorem ordered_bind {t : BinaryTree (κ × ν)} (ordered : OrderedBy Prod.fst t)
    (key : κ) (value : ν) : OrderedBy Prod.fst (bind key value t) := by
  induction t with
  | nil => exact ⟨trivial, trivial, trivial, trivial⟩
  | node binding left right ihl ihr =>
      by_cases kl : key < binding.1
      · rw [bind, if_pos kl]
        exact ⟨ihl ordered.1, ordered.2.1,
          all_bind ordered.2.2.1 key value kl, ordered.2.2.2⟩
      · by_cases kr : binding.1 < key
        · rw [bind, if_neg kl, if_pos kr]
          exact ⟨ordered.1, ihr ordered.2.1, ordered.2.2.1,
            all_bind ordered.2.2.2 key value kr⟩
        · have eq : key = binding.1 := le_antisymm (le_of_not_gt kr) (le_of_not_gt kl)
          rw [bind, if_neg kl, if_neg kr]
          exact ⟨ordered.1, ordered.2.1, by simpa only [eq] using ordered.2.2.1,
            by simpa only [eq] using ordered.2.2.2⟩

theorem lookup_correct {t : BinaryTree (κ × ν)} (ordered : OrderedBy Prod.fst t)
    (query : κ) : lookup query t = observe t query := by
  induction t with
  | nil => rfl
  | node binding left right ihl ihr =>
      by_cases ql : query < binding.1
      · have absent : observe right query = none := observe_none_of_all_ne
          (ordered.2.2.2.mono fun _ hb => ne_of_lt (lt_trans ql hb))
        simp [lookup, ql, observe, ne_of_lt ql, absent, ihl ordered.1]
      · by_cases qr : binding.1 < query
        · have absent : observe left query = none := observe_none_of_all_ne
            (ordered.2.2.1.mono fun _ hb => ne_of_gt (lt_trans hb qr))
          simp [lookup, ql, qr, observe, ne_of_gt qr, absent, ihr ordered.2.1]
        · have eq : query = binding.1 := le_antisymm (le_of_not_gt qr) (le_of_not_gt ql)
          simp [lookup, ql, qr, observe, eq]

/-- The directed lookup/update law holds even before imposing the independent
ordering invariant. Orderedness is needed to identify that lookup with the
whole-tree observation, not for the update algebra itself. -/
theorem lookup_bind (key : κ) (value : ν) (query : κ) (t : BinaryTree (κ × ν)) :
    lookup query (bind key value t) =
      if query = key then some value else lookup query t := by
  induction t with
  | nil =>
      rcases lt_trichotomy query key with h | h | h
      · simp [bind, lookup, h, ne_of_lt h]
      · simp [bind, lookup, h]
      · simp [bind, lookup, h, not_lt_of_gt h, ne_of_gt h]
  | node binding left right ihl ihr =>
      by_cases kl : key < binding.1
      · by_cases ql : query < binding.1
        · simpa [bind, lookup, kl, ql] using ihl
        · by_cases qr : binding.1 < query
          · have qk : query ≠ key := ne_of_gt (lt_trans kl qr)
            simp [bind, lookup, kl, ql, qr, qk]
          · have qk : query ≠ key := fun eq => ql (eq ▸ kl)
            simp [bind, lookup, kl, ql, qr, qk]
      · by_cases kr : binding.1 < key
        · by_cases ql : query < binding.1
          · have qk : query ≠ key := ne_of_lt (lt_trans ql kr)
            simp [bind, lookup, kl, kr, ql, qk]
          · by_cases qr : binding.1 < query
            · simpa [bind, lookup, kl, kr, ql, qr] using ihr
            · have qk : query ≠ key := fun eq => qr (eq ▸ kr)
              simp [bind, lookup, kl, kr, ql, qr, qk]
        · have eq : key = binding.1 := le_antisymm (le_of_not_gt kr) (le_of_not_gt kl)
          rcases lt_trichotomy query binding.1 with h | h | h
          · simp [bind, lookup, kl, kr, eq, h, ne_of_lt h]
          · simp [bind, lookup, kl, kr, eq, h]
          · simp [bind, lookup, kl, kr, eq, h, not_lt_of_gt h, ne_of_gt h]

theorem lookup_some_contains {query : κ} {value : ν} {t : BinaryTree (κ × ν)}
    (found : lookup query t = some value) : Contains (query, value) t := by
  induction t with
  | nil => cases found
  | node binding left right ihl ihr =>
      by_cases ql : query < binding.1
      · exact Or.inr (Or.inl (ihl (by simpa [lookup, ql] using found)))
      · by_cases qr : binding.1 < query
        · exact Or.inr (Or.inr (ihr (by simpa [lookup, ql, qr] using found)))
        · have eq : query = binding.1 := le_antisymm (le_of_not_gt qr) (le_of_not_gt ql)
          have valueEq : value = binding.2 := (Option.some.inj
            (by simpa [lookup, ql, qr] using found)).symm
          exact Or.inl (Prod.ext eq valueEq)

/-- Every successful key occurs in an explicit finite list of node keys. -/
theorem lookup_finite_domain (t : BinaryTree (κ × ν)) :
    ∃ keys : List κ, ∀ query value, lookup query t = some value → query ∈ keys := by
  refine ⟨(entries t).map Prod.fst, ?_⟩
  intro query value found
  apply List.mem_map.mpr
  exact ⟨(query, value), (Search.OrderedTree.contains_iff_mem_entries _ _).mp
    (lookup_some_contains found), rfl⟩

abbrev Tree (κ ν : Type u) [LinearOrder κ] :=
  {t : BinaryTree (κ × ν) // OrderedBy Prod.fst t}

def trees (κ ν : Type u) [LinearOrder κ] : Ops κ ν (Tree κ ν) where
  empty := ⟨.nil, trivial⟩
  bind key value t := ⟨bind key value t.1, ordered_bind t.2 key value⟩
  lookup key t := lookup key t.1

def decode (t : Tree κ ν) : Meaning κ ν := observe t.1

theorem trees_laws : Laws (trees κ ν) decode where
  empty := rfl
  bind key value t := by
    funext query
    change observe (bind key value t.1) query = write key value (observe t.1) query
    rw [← lookup_correct (ordered_bind t.2 key value), lookup_bind, lookup_correct t.2]
    rfl
  lookup key t := lookup_correct t.2 key

theorem trees_finite_domain (t : Tree κ ν) :
    ∃ keys : List κ, ∀ query value,
      (trees κ ν).lookup query t = some value → query ∈ keys :=
  lookup_finite_domain t.1

end LinearOrder
end Search.OrderedMap

import Applications.Search.OrderedMap.Basic
import Applications.Search.OrderedTree.Contents

/-!
# Ordered-map enumeration and source list insertion

The existing inorder `entries` retains every occurrence in a raw tree.
Successful directed lookup implies entry membership without an invariant;
the converse and unique, increasing keys require `OrderedBy Prod.fst`.

The accumulator traversal is a suffix-function specialization of `Trees.fold`.
Its equations describe values for every suffix and every raw tree. Resource
counts belong to the separate measured realization. Sorted-list insertion
retains the source's two strict tests and same-key payload replacement.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedMap

universe u v
variable {κ : Type u} {ν : Type v}
open Search.OrderedTree (All OrderedBy Contains entries)

/-- All-node predicates transport to every inorder occurrence, including
occurrences that directed search cannot reach in a malformed tree. -/
theorem all_entries {P : κ × ν → Prop} {t : BinaryTree (κ × ν)} (h : All P t) :
    ∀ binding ∈ entries t, P binding :=
  fun binding member => h.of_contains
    ((Search.OrderedTree.contains_iff_mem_entries binding t).mpr member)

/-- Reuse the ordinary tree fold at function-valued summaries. -/
def fastEntriesAcc (t : BinaryTree (κ × ν)) : List (κ × ν) → List (κ × ν) :=
  Trees.fold id (fun left binding right suffix => left (binding :: right suffix)) t

@[simp] theorem fastEntriesAcc_nil (suffix : List (κ × ν)) :
    fastEntriesAcc .nil suffix = suffix := rfl

theorem fastEntriesAcc_node (binding : κ × ν) (left right : BinaryTree (κ × ν))
    (suffix : List (κ × ν)) :
    fastEntriesAcc (.node binding left right) suffix =
      fastEntriesAcc left (binding :: fastEntriesAcc right suffix) := rfl

/-- The untouched suffix is arbitrary; ordering and finite-map validity are
irrelevant to this traversal equality. -/
theorem fastEntriesAcc_eq (t : BinaryTree (κ × ν)) (suffix : List (κ × ν)) :
    fastEntriesAcc t suffix = entries t ++ suffix := by
  induction t generalizing suffix with
  | nil => rfl
  | node binding left right ihl ihr =>
      rw [fastEntriesAcc_node, ihl, ihr, Search.OrderedTree.entries_node]
      simp only [List.append_assoc, List.cons_append]

def fastEntries (t : BinaryTree (κ × ν)) : List (κ × ν) := fastEntriesAcc t []

theorem fastEntries_eq (t : BinaryTree (κ × ν)) : fastEntries t = entries t := by
  simp only [fastEntries, fastEntriesAcc_eq, List.append_nil]

section Preorder
variable [Preorder κ]

/-- Project to the existing ordered-key tree and reuse its strict traversal
theorem. Payloads are never compared. -/
theorem ordered_entries_keys_pairwise {t : BinaryTree (κ × ν)}
    (ordered : OrderedBy Prod.fst t) : ((entries t).map Prod.fst).Pairwise (· < ·) := by
  have h := Search.OrderedTree.ordered_entries_pairwise
    ((Search.OrderedTree.orderedBy_iff_map Prod.fst t).mp ordered)
  simpa only [Search.OrderedTree.entries, Trees.inorder_map] using h

theorem ordered_entries_pairwise {t : BinaryTree (κ × ν)}
    (ordered : OrderedBy Prod.fst t) :
    (entries t).Pairwise (fun a b => a.1 < b.1) := by
  simpa only [List.pairwise_map] using ordered_entries_keys_pairwise ordered

theorem ordered_entries_keys_nodup {t : BinaryTree (κ × ν)}
    (ordered : OrderedBy Prod.fst t) : ((entries t).map Prod.fst).Nodup :=
  (ordered_entries_keys_pairwise ordered).nodup

end Preorder

section Comparison
variable [LT κ] [DecidableLT κ]

/-- Insert when the first strict test succeeds, traverse when the reverse
test succeeds, and otherwise replace the head. For a linear order the final
branch means equal keys. The operation is defined even on unsorted lists. -/
def kvsInsert (key : κ) (value : ν) : List (κ × ν) → List (κ × ν)
  | [] => [(key, value)]
  | binding :: rest =>
      if key < binding.1 then (key, value) :: binding :: rest
      else if binding.1 < key then binding :: kvsInsert key value rest
      else (key, value) :: rest

end Comparison

section LinearOrder
variable [LinearOrder κ]

/-- Completeness of enumeration does not require the ordering invariant. -/
theorem mem_entries_of_lookup {key : κ} {value : ν} {t : BinaryTree (κ × ν)}
    (found : lookup key t = some value) : (key, value) ∈ entries t :=
  (Search.OrderedTree.contains_iff_mem_entries _ _).mp (lookup_some_contains found)

theorem lookup_eq_some_iff_mem_entries {t : BinaryTree (κ × ν)}
    (ordered : OrderedBy Prod.fst t) (key : κ) (value : ν) :
    lookup key t = some value ↔ (key, value) ∈ entries t := by
  constructor
  · exact mem_entries_of_lookup
  · intro member
    induction t with
    | nil => cases member
    | node binding left right ihl ihr =>
        rw [Search.OrderedTree.entries_node] at member
        rcases List.mem_append.mp member with member | member
        · have smaller : key < binding.1 :=
            all_entries ordered.2.2.1 (key, value) member
          simpa only [lookup, ite_eq_left smaller] using ihl ordered.1 member
        · rcases List.mem_cons.mp member with same | member
          · cases same
            simp [lookup]
          · have larger : binding.1 < key :=
              all_entries ordered.2.2.2 (key, value) member
            simpa only [lookup, ite_eq_right (not_lt_of_gt larger), ite_eq_left larger] using
              ihr ordered.2.1 member

/-- List insertion splits at a pivot using only the left separator.
Neither list needs internal sorting or duplicate-freedom; the right suffix is arbitrary. -/
theorem kvsInsert_split_of_left (key : κ) (value : ν) (pivot : κ) (pivotValue : ν)
    (left right : List (κ × ν))
    (hl : ∀ binding ∈ left, binding.1 < pivot) :
    kvsInsert key value (left ++ (pivot, pivotValue) :: right) =
      if key < pivot then kvsInsert key value left ++ (pivot, pivotValue) :: right
      else if pivot < key then left ++ (pivot, pivotValue) :: kvsInsert key value right
      else left ++ (key, value) :: right := by
  induction left with
  | nil => simp [kvsInsert]
  | cons head tail ih =>
      have head_lt : head.1 < pivot := hl head List.mem_cons_self
      have tail_lt : ∀ binding ∈ tail, binding.1 < pivot :=
        fun binding member => hl binding (List.mem_cons_of_mem head member)
      by_cases kh : key < head.1
      · have kp : key < pivot := lt_trans kh head_lt
        simp [kvsInsert, kh, kp]
      · by_cases hk : head.1 < key
        · rw [List.cons_append, kvsInsert, ite_eq_right kh, ite_eq_left hk, ih tail_lt]
          by_cases kp : key < pivot
          · simp only [ite_eq_left kp, kvsInsert, ite_eq_right kh, ite_eq_left hk, List.cons_append]
          · by_cases pk : pivot < key
            · simp only [ite_eq_right kp, ite_eq_left pk, List.cons_append]
            · simp only [ite_eq_right kp, ite_eq_right pk, List.cons_append]
        · have same : key = head.1 := le_antisymm (le_of_not_gt hk) (le_of_not_gt kh)
          have kp : key < pivot := by simpa only [same] using head_lt
          simp [kvsInsert, kh, hk, kp]

/-- The source-facing separator contract, recovered from the weaker public law. -/
theorem kvsInsert_split (key : κ) (value : ν) (pivot : κ) (pivotValue : ν)
    (left right : List (κ × ν))
    (hl : ∀ binding ∈ left, binding.1 < pivot)
    (_hr : ∀ binding ∈ right, pivot < binding.1) :
    kvsInsert key value (left ++ (pivot, pivotValue) :: right) =
      if key < pivot then kvsInsert key value left ++ (pivot, pivotValue) :: right
      else if pivot < key then left ++ (pivot, pivotValue) :: kvsInsert key value right
      else left ++ (key, value) :: right :=
  kvsInsert_split_of_left key value pivot pivotValue left right hl

/-- Enumeration after the actual tree write is the source list insertion.
The invariant supplies subtree separators; equal keys replace payloads. -/
theorem entries_bind {t : BinaryTree (κ × ν)} (ordered : OrderedBy Prod.fst t)
    (key : κ) (value : ν) : entries (bind key value t) = kvsInsert key value (entries t) := by
  induction t with
  | nil => simp [bind, kvsInsert, Search.OrderedTree.entries_node]
  | node binding left right ihl ihr =>
      rcases binding with ⟨pivot, old⟩
      rw [Search.OrderedTree.entries_node,
        kvsInsert_split_of_left key value pivot old (entries left) (entries right)
          (all_entries ordered.2.2.1)]
      by_cases kl : key < pivot
      · simp only [bind, ite_eq_left kl, Search.OrderedTree.entries_node, ihl ordered.1]
      · by_cases kr : pivot < key
        · simp only [bind, ite_eq_right kl, ite_eq_left kr, Search.OrderedTree.entries_node,
            ihr ordered.2.1]
        · simp only [bind, ite_eq_right kl, ite_eq_right kr, Search.OrderedTree.entries_node]

end LinearOrder
end Search.OrderedMap

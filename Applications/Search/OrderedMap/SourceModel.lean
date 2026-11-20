import Applications.Search.OrderedMap.Enumeration
import Applications.Search.OrderedMap.AssociationList
import Applications.Search.OrderedMap.FunctionUpdate
import Mathlib.Data.List.Sort

/-!
# The two SearchTree map abstractions

The enumeration route uses the existing first-binding association-list
observation. The structural route independently combines child maps with the
source's symmetric, collision-removing union and then writes the root binding.
Its search and update proofs use subtree separators directly; they do not use
the later agreement theorem between the two routes.

Both decoders have finite observed support on each finite input. `Meaning`
itself remains the unrestricted function type. No order, equality decision,
or distinguished default is required of payloads.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedMap.SourceModel

open Search.OrderedTree (All OrderedBy Contains entries)

universe u v
variable {κ : Type u} {ν : Type v}

theorem in_keys_of_mem {bindings : List (κ × ν)} {key : κ} {value : ν}
    (member : (key, value) ∈ bindings) : key ∈ bindings.map Prod.fst :=
  List.mem_map.mpr ⟨(key, value), member, rfl⟩

section DecidableKeys
variable [DecidableEq κ]

@[simp] theorem listObserve_nil : listObserve ([] : List (κ × ν)) = fun _ => none := rfl

/-- The head binding wins, exactly as in the source `map_of_list` recurrence. -/
theorem listObserve_cons (binding : κ × ν) (rest : List (κ × ν)) :
    listObserve (binding :: rest) = write binding.1 binding.2 (listObserve rest) := by
  cases binding
  rfl

theorem mem_of_listObserve_some {bindings : List (κ × ν)} {key : κ} {value : ν}
    (found : listObserve bindings key = some value) : (key, value) ∈ bindings := by
  induction bindings with
  | nil => simp [listObserve, listLookup] at found
  | cons binding rest ih =>
      by_cases same : key = binding.1
      · have payload : binding.2 = value := Option.some.inj
          (by simpa [listObserve, listLookup, same] using found)
        exact List.mem_cons.mpr (Or.inl (Prod.ext same payload.symm))
      · apply List.mem_cons.mpr
        exact Or.inr (ih (by simpa [listObserve, listLookup, same] using found))

theorem listObserve_none_iff (bindings : List (κ × ν)) (key : κ) :
    listObserve bindings key = none ↔ key ∉ bindings.map Prod.fst := by
  induction bindings with
  | nil => simp [listObserve, listLookup]
  | cons binding rest ih =>
      change (if key = binding.1 then some binding.2 else listObserve rest key) = none ↔
        key ∉ binding.1 :: rest.map Prod.fst
      by_cases same : key = binding.1 <;> simp [same, ih]

theorem listObserve_none_of_not_mem {bindings : List (κ × ν)} {key : κ}
    (absent : key ∉ bindings.map Prod.fst) : listObserve bindings key = none :=
  (listObserve_none_iff bindings key).mpr absent

theorem listObserve_eq_some_of_mem {bindings : List (κ × ν)} {key : κ} {value : ν}
    (unique : (bindings.map Prod.fst).Nodup) (member : (key, value) ∈ bindings) :
    listObserve bindings key = some value := by
  induction bindings with
  | nil => simp at member
  | cons binding rest ih =>
      change (binding.1 :: rest.map Prod.fst).Nodup at unique
      rcases List.nodup_cons.mp unique with ⟨fresh, uniqueRest⟩
      rcases List.mem_cons.mp member with same | member
      · rw [← same, listObserve_cons]
        simp [write]
      · have different : key ≠ binding.1 := fun same => fresh (same ▸ in_keys_of_mem member)
        rw [listObserve_cons]
        change (if key = binding.1 then some binding.2 else listObserve rest key) = some value
        rw [ite_eq_right different]
        exact ih uniqueRest member

theorem listObserve_some_iff {bindings : List (κ × ν)}
    (unique : (bindings.map Prod.fst).Nodup) (key : κ) (value : ν) :
    listObserve bindings key = some value ↔ (key, value) ∈ bindings :=
  ⟨mem_of_listObserve_some, listObserve_eq_some_of_mem unique⟩

theorem listObserve_finite_support (bindings : List (κ × ν)) :
    ∃ keys : List κ, ∀ key value, listObserve bindings key = some value → key ∈ keys :=
  ⟨bindings.map Prod.fst, fun _ _ found => in_keys_of_mem (mem_of_listObserve_some found)⟩

/-- First abstraction route: decode the actual inorder enumeration. -/
def enumAbs (t : BinaryTree (κ × ν)) : Meaning κ ν := listObserve (entries t)

@[simp] theorem enumAbs_empty : enumAbs (.nil : BinaryTree (κ × ν)) = fun _ => none := rfl

theorem enumAbs_elements (t : BinaryTree (κ × ν)) : listObserve (entries t) = enumAbs t := rfl

theorem enumAbs_finite_support (t : BinaryTree (κ × ν)) :
    ∃ keys : List κ, ∀ key value, enumAbs t key = some value → key ∈ keys :=
  listObserve_finite_support (entries t)

end DecidableKeys

/-- The source union discards every collision, including equal-valued ones. -/
def collisionUnion (left right : Meaning κ ν) : Meaning κ ν :=
  fun key => match left key, right key with
    | none, none => none
    | none, some value => some value
    | some value, none => some value
    | some _, some _ => none

theorem collisionUnion_left (left right : Meaning κ ν) (key : κ)
    (absent : right key = none) : collisionUnion left right key = left key := by
  unfold collisionUnion
  rw [absent]
  cases left key <;> rfl

theorem collisionUnion_right (left right : Meaning κ ν) (key : κ)
    (absent : left key = none) : collisionUnion left right key = right key := by
  unfold collisionUnion
  rw [absent]
  cases right key <;> rfl

theorem collisionUnion_both (left right : Meaning κ ν) (key : κ) (first second : ν)
    (hl : left key = some first) (hr : right key = some second) :
    collisionUnion left right key = none := by
  simp [collisionUnion, hl, hr]

theorem collisionUnion_some_iff (left right : Meaning κ ν) (key : κ) (value : ν) :
    collisionUnion left right key = some value ↔
      (left key = some value ∧ right key = none) ∨
      (left key = none ∧ right key = some value) := by
  unfold collisionUnion
  cases left key <;> cases right key <;> simp

theorem collisionUnion_comm (left right : Meaning κ ν) :
    collisionUnion left right = collisionUnion right left := by
  funext key
  unfold collisionUnion
  cases left key <;> cases right key <;> rfl

@[simp] theorem collisionUnion_empty_left (m : Meaning κ ν) :
    collisionUnion (fun _ => none) m = m :=
  funext fun key => collisionUnion_right _ _ key rfl

@[simp] theorem collisionUnion_empty_right (m : Meaning κ ν) :
    collisionUnion m (fun _ => none) = m :=
  funext fun key => collisionUnion_left _ _ key rfl

/-- Cancellation applies to all present bindings, not merely unequal payloads. -/
theorem collisionUnion_self (m : Meaning κ ν) :
    collisionUnion m m = fun _ => none := by
  funext key
  unfold collisionUnion
  cases m key <;> rfl

section DecidableKeys
variable [DecidableEq κ]

theorem collisionUnion_write_right (left right : Meaning κ ν) (key : κ) (value : ν)
    (absent : left key = none) :
    write key value (collisionUnion left right) = collisionUnion left (write key value right) := by
  funext query
  by_cases same : query = key
  · subst query
    simp [write, collisionUnion, absent]
  · simp [write, collisionUnion, same]

theorem collisionUnion_write_left (left right : Meaning κ ν) (key : κ) (value : ν)
    (absent : right key = none) :
    write key value (collisionUnion left right) = collisionUnion (write key value left) right := by
  funext query
  by_cases same : query = key
  · subst query
    simp [write, collisionUnion, absent]
  · simp [write, collisionUnion, same]

/-- Direct source recursion, defined independently of inorder enumeration. -/
def mapOfTree : BinaryTree (κ × ν) → Meaning κ ν
  | .nil => fun _ => none
  | .node binding left right =>
      write binding.1 binding.2 (collisionUnion (mapOfTree left) (mapOfTree right))

@[simp] theorem mapOfTree_empty : mapOfTree (.nil : BinaryTree (κ × ν)) = fun _ => none := rfl

theorem mapOfTree_node (binding : κ × ν) (left right : BinaryTree (κ × ν)) :
    mapOfTree (.node binding left right) =
      write binding.1 binding.2 (collisionUnion (mapOfTree left) (mapOfTree right)) := rfl

/-- Every binding that survives the direct decoder satisfies every all-node property. -/
theorem mapOfTree_prop {P : κ × ν → Prop} {t : BinaryTree (κ × ν)} (all : All P t)
    (key : κ) (value : ν) (found : mapOfTree t key = some value) : P (key, value) := by
  induction t with
  | nil => simp [mapOfTree] at found
  | node binding left right ihl ihr =>
      by_cases same : key = binding.1
      · have payload : binding.2 = value := Option.some.inj
          (by simpa [mapOfTree, write, same] using found)
        have pair : (key, value) = binding := Prod.ext same payload.symm
        exact pair.symm ▸ all.1
      · have children : collisionUnion (mapOfTree left) (mapOfTree right) key = some value :=
          by simpa [mapOfTree, write, same] using found
        rcases (collisionUnion_some_iff _ _ key value).mp children with ⟨hl, _⟩ | ⟨_, hr⟩
        · exact ihl all.2.1 hl
        · exact ihr all.2.2 hr

theorem mapOfTree_some_contains {t : BinaryTree (κ × ν)} {key : κ} {value : ν}
    (found : mapOfTree t key = some value) : Contains (key, value) t :=
  mapOfTree_prop ((Search.OrderedTree.all_iff (fun binding => Contains binding t) t).mpr
    (fun _ member => member)) key value found

theorem mapOfTree_finite_support (t : BinaryTree (κ × ν)) :
    ∃ keys : List κ, ∀ key value, mapOfTree t key = some value → key ∈ keys := by
  refine ⟨(entries t).map Prod.fst, ?_⟩
  intro key value found
  exact in_keys_of_mem ((Search.OrderedTree.contains_iff_mem_entries (key, value) t).mp
    (mapOfTree_some_contains found))

theorem mapOfTree_none_of_all_ne {t : BinaryTree (κ × ν)} {key : κ}
    (all : All (fun binding => key ≠ binding.1) t) : mapOfTree t key = none := by
  cases found : mapOfTree t key with
  | none => rfl
  | some value => exact False.elim (mapOfTree_prop all key value found rfl)

/-- Disjointness concerns the two projected key sets. Each operand may itself
contain repetitions and shadowed payloads. -/
theorem listObserve_append_of_disjoint (left right : List (κ × ν))
    (apart : List.Disjoint (left.map Prod.fst) (right.map Prod.fst)) :
    listObserve (left ++ right) = collisionUnion (listObserve left) (listObserve right) := by
  induction left with
  | nil => simp
  | cons binding rest ih =>
      change List.Disjoint (binding.1 :: rest.map Prod.fst) (right.map Prod.fst) at apart
      rcases List.disjoint_cons_left.mp apart with ⟨fresh, apartRest⟩
      rw [List.cons_append, listObserve_cons, ih apartRest, listObserve_cons]
      exact collisionUnion_write_left _ _ binding.1 binding.2
        (listObserve_none_of_not_mem fresh)

end DecidableKeys

section LinearOrder
variable [LinearOrder κ]

theorem enumAbs_eq_lookup {t : BinaryTree (κ × ν)} (ordered : OrderedBy Prod.fst t)
    (key : κ) : enumAbs t key = lookup key t := by
  cases found : lookup key t with
  | none =>
      cases decoded : enumAbs t key with
      | none => rfl
      | some value =>
          have member : (key, value) ∈ entries t := mem_of_listObserve_some decoded
          have found' := (lookup_eq_some_iff_mem_entries ordered key value).mpr member
          simp [found] at found'
  | some value =>
      exact listObserve_eq_some_of_mem (ordered_entries_keys_nodup ordered)
        ((lookup_eq_some_iff_mem_entries ordered key value).mp found)

theorem enumAbs_bound {t : BinaryTree (κ × ν)} (ordered : OrderedBy Prod.fst t)
    (key : κ) : hasBinding (enumAbs t) key = (lookup key t).isSome :=
  congrArg Option.isSome (enumAbs_eq_lookup ordered key)

theorem enumAbs_default {t : BinaryTree (κ × ν)} (ordered : OrderedBy Prod.fst t)
    (default : ν) (key : κ) : withDefault default (enumAbs t) key = (lookup key t).getD default :=
  congrArg (fun result => result.getD default) (enumAbs_eq_lookup ordered key)

/-- Source list insertion has the same map update on every raw list. -/
theorem listObserve_kvsInsert (key : κ) (value : ν) (bindings : List (κ × ν)) :
    listObserve (kvsInsert key value bindings) = write key value (listObserve bindings) := by
  induction bindings with
  | nil => simp [kvsInsert, listObserve_cons]
  | cons binding rest ih =>
      by_cases before : key < binding.1
      · simp only [kvsInsert, ite_eq_left before, listObserve_cons]
      · by_cases after : binding.1 < key
        · simp only [kvsInsert, ite_eq_right before, ite_eq_left after, listObserve_cons, ih]
          exact write_comm (listObserve rest) key binding.1 value binding.2 (ne_of_gt after)
        · have same : key = binding.1 := le_antisymm (le_of_not_gt after) (le_of_not_gt before)
          simp only [kvsInsert, ite_eq_right before, ite_eq_right after, listObserve_cons]
          rw [← same]
          exact (write_shadow (listObserve rest) key binding.2 value).symm

theorem enumAbs_bind {t : BinaryTree (κ × ν)} (ordered : OrderedBy Prod.fst t)
    (key : κ) (value : ν) : enumAbs (bind key value t) = write key value (enumAbs t) := by
  unfold enumAbs
  rw [entries_bind ordered key value, listObserve_kvsInsert]

/-- The primed search correspondence follows the actual tree recursion and
uses separator absence on the discarded child. -/
theorem mapOfTree_eq_lookup {t : BinaryTree (κ × ν)} (ordered : OrderedBy Prod.fst t)
    (key : κ) : mapOfTree t key = lookup key t := by
  induction t with
  | nil => rfl
  | node binding left right ihl ihr =>
      by_cases before : key < binding.1
      · have absent : mapOfTree right key = none := mapOfTree_none_of_all_ne
          (ordered.2.2.2.mono fun _ greater => ne_of_lt (lt_trans before greater))
        rw [mapOfTree, write, ite_eq_right (ne_of_lt before),
          collisionUnion_left _ _ key absent, lookup, ite_eq_left before]
        exact ihl ordered.1
      · by_cases after : binding.1 < key
        · have absent : mapOfTree left key = none := mapOfTree_none_of_all_ne
            (ordered.2.2.1.mono fun _ lesser => ne_of_gt (lt_trans lesser after))
          rw [mapOfTree, write, ite_eq_right (ne_of_gt after),
            collisionUnion_right _ _ key absent, lookup, ite_eq_right before, ite_eq_left after]
          exact ihr ordered.2.1
        · have same : key = binding.1 := le_antisymm (le_of_not_gt after) (le_of_not_gt before)
          simp [lookup, mapOfTree, write, same]

theorem mapOfTree_bound {t : BinaryTree (κ × ν)} (ordered : OrderedBy Prod.fst t)
    (key : κ) : hasBinding (mapOfTree t) key = (lookup key t).isSome :=
  congrArg Option.isSome (mapOfTree_eq_lookup ordered key)

theorem mapOfTree_default {t : BinaryTree (κ × ν)} (ordered : OrderedBy Prod.fst t)
    (default : ν) (key : κ) : withDefault default (mapOfTree t) key = (lookup key t).getD default :=
  congrArg (fun result => result.getD default) (mapOfTree_eq_lookup ordered key)

/-- The primed update law is structural: absence moves a write into the
chosen union operand, and distinct root writes commute on the recursive return. -/
theorem mapOfTree_bind {t : BinaryTree (κ × ν)} (ordered : OrderedBy Prod.fst t)
    (key : κ) (value : ν) : mapOfTree (bind key value t) = write key value (mapOfTree t) := by
  induction t with
  | nil => simp [bind, mapOfTree]
  | node binding left right ihl ihr =>
      by_cases before : key < binding.1
      · have absent : mapOfTree right key = none := mapOfTree_none_of_all_ne
          (ordered.2.2.2.mono fun _ greater => ne_of_lt (lt_trans before greater))
        rw [bind, ite_eq_left before]
        change write binding.1 binding.2
            (collisionUnion (mapOfTree (bind key value left)) (mapOfTree right)) =
          write key value (write binding.1 binding.2
            (collisionUnion (mapOfTree left) (mapOfTree right)))
        rw [ihl ordered.1, ← collisionUnion_write_left _ _ key value absent]
        exact write_comm _ key binding.1 value binding.2 (ne_of_lt before)
      · by_cases after : binding.1 < key
        · have absent : mapOfTree left key = none := mapOfTree_none_of_all_ne
            (ordered.2.2.1.mono fun _ lesser => ne_of_gt (lt_trans lesser after))
          rw [bind, ite_eq_right before, ite_eq_left after]
          change write binding.1 binding.2
              (collisionUnion (mapOfTree left) (mapOfTree (bind key value right))) =
            write key value (write binding.1 binding.2
              (collisionUnion (mapOfTree left) (mapOfTree right)))
          rw [ihr ordered.2.1, ← collisionUnion_write_right _ _ key value absent]
          exact write_comm _ key binding.1 value binding.2 (ne_of_gt after)
        · have same : key = binding.1 := le_antisymm (le_of_not_gt after) (le_of_not_gt before)
          rw [bind, ite_eq_right before, ite_eq_right after]
          change write key value (collisionUnion (mapOfTree left) (mapOfTree right)) =
            write key value (write binding.1 binding.2
              (collisionUnion (mapOfTree left) (mapOfTree right)))
          rw [← same]
          exact (write_shadow _ key binding.2 value).symm

/-- Both independently specified abstractions agree on valid search trees.
The proof reconstructs the direct node map using disjoint inorder key sets. -/
theorem enumAbs_eq_mapOfTree {t : BinaryTree (κ × ν)} (ordered : OrderedBy Prod.fst t) :
    enumAbs t = mapOfTree t := by
  induction t with
  | nil => rfl
  | node binding left right ihl ihr =>
      have apart : List.Disjoint ((entries left).map Prod.fst)
          ((binding :: entries right).map Prod.fst) := by
        intro key hl hr
        rcases List.mem_map.mp hl with ⟨a, ha, akey⟩
        have lesser : key < binding.1 := akey ▸ all_entries ordered.2.2.1 a ha
        simp only [List.map_cons, List.mem_cons] at hr
        rcases hr with same | hr
        · exact (ne_of_lt lesser) same
        · rcases List.mem_map.mp hr with ⟨b, hb, bkey⟩
          have greater : binding.1 < key := bkey ▸ all_entries ordered.2.2.2 b hb
          exact lt_asymm lesser greater
      have absent : mapOfTree left binding.1 = none := mapOfTree_none_of_all_ne
        (ordered.2.2.1.mono fun _ lesser => ne_of_gt lesser)
      change listObserve (entries left ++ binding :: entries right) =
        write binding.1 binding.2 (collisionUnion (mapOfTree left) (mapOfTree right))
      rw [listObserve_append_of_disjoint _ _ apart, listObserve_cons]
      change collisionUnion (enumAbs left) (write binding.1 binding.2 (enumAbs right)) = _
      rw [ihl ordered.1, ihr ordered.2.1]
      exact (collisionUnion_write_right _ _ binding.1 binding.2 absent).symm

end LinearOrder

section Preorder
variable [Preorder κ] [DecidableEq κ]

/-- Equal partial meanings determine the canonical inorder list under strict
key ordering. Tree shape and payload order are irrelevant. -/
theorem entries_eq_of_enumAbs_eq {left right : BinaryTree (κ × ν)}
    (hl : OrderedBy Prod.fst left) (hr : OrderedBy Prod.fst right)
    (same : enumAbs left = enumAbs right) : entries left = entries right := by
  let rel : κ × ν → κ × ν → Prop := fun a b => a.1 < b.1
  let : Std.Antisymm rel := ⟨fun _ _ hab hba => False.elim (lt_asymm hab hba)⟩
  let : Std.Irrefl rel := ⟨fun a => lt_irrefl a.1⟩
  apply List.Pairwise.eq_of_mem_iff
    (r := rel) (ordered_entries_pairwise hl) (ordered_entries_pairwise hr)
  rintro ⟨key, value⟩
  calc
    (key, value) ∈ entries left ↔ enumAbs left key = some value :=
      (listObserve_some_iff (ordered_entries_keys_nodup hl) key value).symm
    _ ↔ enumAbs right key = some value := by rw [same]
    _ ↔ (key, value) ∈ entries right :=
      listObserve_some_iff (ordered_entries_keys_nodup hr) key value

end Preorder

section LinearOrder
variable [LinearOrder κ]

theorem entries_eq_of_lookup_eq {left right : BinaryTree (κ × ν)}
    (hl : OrderedBy Prod.fst left) (hr : OrderedBy Prod.fst right)
    (same : ∀ key, lookup key left = lookup key right) : entries left = entries right := by
  apply entries_eq_of_enumAbs_eq hl hr
  funext key
  rw [enumAbs_eq_lookup hl, enumAbs_eq_lookup hr, same key]

theorem entries_eq_of_mapOfTree_eq {left right : BinaryTree (κ × ν)}
    (hl : OrderedBy Prod.fst left) (hr : OrderedBy Prod.fst right)
    (same : mapOfTree left = mapOfTree right) : entries left = entries right := by
  apply entries_eq_of_enumAbs_eq hl hr
  rw [enumAbs_eq_mapOfTree hl, enumAbs_eq_mapOfTree hr, same]

end LinearOrder
end Search.OrderedMap.SourceModel

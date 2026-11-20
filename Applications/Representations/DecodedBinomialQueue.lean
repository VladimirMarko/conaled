import Applications.Search.BinomialQueue.Contents
import Applications.Representations.SignedComparison
import Applications.Sorting.SourceSelection
import Applications.Search.ListMaximumQueue

/-!
Label transport for the actual dense binomial-queue recursions. A comparator
agreement hypothesis preserves the exact branch choices and raw tree shape,
including ties, holes and malformed fallbacks. The maps below are mathematical
observations; executable machine-key operations use the original carrier.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Representations.DecodedBinomialQueue

open Search.BinomialQueue

universe u v
variable {K : Type u} {L : Type v}

abbrev mapQueue (label : K → L) (queue : Queue K) : Queue L :=
  queue.map (BinaryTree.map label)

@[simp] theorem mapQueue_nil (label : K → L) : mapQueue label [] = [] := rfl

@[simp] theorem mapQueue_cons (label : K → L) (tree : BinaryTree K) (queue : Queue K) :
    mapQueue label (tree :: queue) = tree.map label :: mapQueue label queue := rfl

theorem map_empty (label : K → L) : mapQueue label empty = empty := rfl

theorem map_smash (label : K → L) (greater : K → K → Bool)
    (other : L → L → Bool)
    (agree : ∀ x y, other (label x) (label y) = greater x y)
    (left right : BinaryTree K) :
    (smash greater left right).map label =
      smash other (left.map label) (right.map label) := by
  cases left with
  | nil => cases right <;> rfl
  | node x a b =>
    cases b with
    | node _ _ _ => cases right <;> rfl
    | nil =>
      cases right with
      | nil => rfl
      | node y c d =>
        cases d with
        | node _ _ _ => rfl
        | nil =>
          by_cases h : greater x y = true <;>
            simp [smash, BinaryTree.map, agree, h]

theorem map_carry (label : K → L) (greater : K → K → Bool)
    (other : L → L → Bool)
    (agree : ∀ x y, other (label x) (label y) = greater x y)
    (queue : Queue K) (tree : BinaryTree K) :
    mapQueue label (carry greater queue tree) =
      carry other (mapQueue label queue) (tree.map label) := by
  induction queue generalizing tree with
  | nil => cases tree <;> rfl
  | cons head tail ih =>
    cases head <;> cases tree <;>
      simp [carry, mapQueue, BinaryTree.map, ih, map_smash label greater other agree]

theorem map_insert (label : K → L) (greater : K → K → Bool)
    (other : L → L → Bool)
    (agree : ∀ x y, other (label x) (label y) = greater x y)
    (key : K) (queue : Queue K) :
    mapQueue label (insert greater key queue) =
      insert other (label key) (mapQueue label queue) := by
  simpa only [Search.BinomialQueue.insert, BinaryTree.map] using
    map_carry label greater other agree queue (.node key .nil .nil)

theorem map_join (label : K → L) (greater : K → K → Bool)
    (other : L → L → Bool)
    (agree : ∀ x y, other (label x) (label y) = greater x y)
    (left right : Queue K) (carryTree : BinaryTree K) :
    mapQueue label (join greater left right carryTree) =
      join other (mapQueue label left) (mapQueue label right) (carryTree.map label) := by
  induction left generalizing right carryTree with
  | nil => simpa only [join_nil_left, mapQueue_nil] using
      map_carry label greater other agree right carryTree
  | cons head tail ih =>
    cases right with
    | nil => simpa only [join_nil_right, mapQueue_nil] using
        map_carry label greater other agree (head :: tail) carryTree
    | cons otherHead otherTail =>
      cases head <;> cases otherHead <;> cases carryTree <;>
        simp [join, mapQueue, BinaryTree.map, ih, map_smash label greater other agree]

theorem map_unzip (label : K → L) (tree : BinaryTree K)
    (cont : Queue K → Queue K) (otherCont : Queue L → Queue L)
    (agree : ∀ queue, mapQueue label (cont queue) = otherCont (mapQueue label queue)) :
    mapQueue label (unzip tree cont) = unzip (tree.map label) otherCont := by
  induction tree generalizing cont otherCont with
  | nil => simpa only [unzip, BinaryTree.map, mapQueue_nil] using agree []
  | node key left right _ ihr =>
    simp only [unzip, BinaryTree.map]
    apply ihr
    intro queue
    simpa only [mapQueue_cons, BinaryTree.map] using
      congrArg (List.cons (.node (label key) (left.map label) .nil)) (agree queue)

theorem map_heapDeleteMax (label : K → L) (tree : BinaryTree K) :
    mapQueue label (heapDeleteMax tree) = heapDeleteMax (tree.map label) := by
  cases tree with
  | nil => rfl
  | node key left right =>
    cases right with
    | node _ _ _ => rfl
    | nil =>
      simpa only [heapDeleteMax, BinaryTree.map] using
        map_unzip label left id id (fun _ => rfl)

theorem map_findMaxAux (label : K → L) (greater : K → K → Bool)
    (other : L → L → Bool)
    (agree : ∀ x y, other (label x) (label y) = greater x y)
    (current : K) (queue : Queue K) :
    label (findMaxAux greater current queue) =
      findMaxAux other (label current) (mapQueue label queue) := by
  induction queue generalizing current with
  | nil => rfl
  | cons head tail ih =>
    cases head with
    | nil => simpa only [findMaxAux, mapQueue_cons, BinaryTree.map] using ih current
    | node key left right =>
      by_cases h : greater key current = true <;>
        simp [findMaxAux, mapQueue, BinaryTree.map, agree, h, ih]

theorem map_findMax (label : K → L) (greater : K → K → Bool)
    (other : L → L → Bool)
    (agree : ∀ x y, other (label x) (label y) = greater x y)
    (queue : Queue K) :
    (findMax greater queue).map label = findMax other (mapQueue label queue) := by
  induction queue with
  | nil => rfl
  | cons head tail ih =>
    cases head <;>
      simp [findMax, mapQueue, BinaryTree.map, ih,
        map_findMaxAux label greater other agree]

theorem map_merge (label : K → L) (greater : K → K → Bool)
    (other : L → L → Bool)
    (agree : ∀ x y, other (label x) (label y) = greater x y)
    (left right : Queue K) :
    mapQueue label (merge greater left right) =
      merge other (mapQueue label left) (mapQueue label right) := by
  simpa only [merge, BinaryTree.map] using
    map_join label greater other agree left right .nil

theorem map_deleteMaxAux (label : K → L) (greater : K → K → Bool)
    (other : L → L → Bool)
    (agree : ∀ x y, other (label x) (label y) = greater x y)
    (threshold : K) (queue : Queue K) :
    (mapQueue label (deleteMaxAux greater threshold queue).1,
      mapQueue label (deleteMaxAux greater threshold queue).2) =
      deleteMaxAux other (label threshold) (mapQueue label queue) := by
  induction queue with
  | nil => rfl
  | cons head tail ih =>
    cases head with
    | nil =>
      simpa only [deleteMaxAux, mapQueue_cons, BinaryTree.map] using
        congrArg (fun result : Queue L × Queue L => (.nil :: result.1, result.2)) ih
    | node key left right =>
      cases right with
      | node _ _ _ => rfl
      | nil =>
        by_cases h : greater threshold key = true <;>
          simp [deleteMaxAux, mapQueue, BinaryTree.map, agree, h, ← ih,
            map_heapDeleteMax]

theorem map_deleteMax (label : K → L) (greater : K → K → Bool)
    (other : L → L → Bool)
    (agree : ∀ x y, other (label x) (label y) = greater x y)
    (queue : Queue K) :
    (deleteMax greater queue).map (fun result => (label result.1, mapQueue label result.2)) =
      deleteMax other (mapQueue label queue) := by
  have find := map_findMax label greater other agree queue
  cases selected : findMax greater queue with
  | none => simp [deleteMax, ← find, selected]
  | some key =>
    have aux := map_deleteMaxAux label greater other agree key queue
    simp [deleteMax, ← find, selected, ← aux]
    exact map_join label greater other agree _ _ .nil

/-! The runtime keeps native signed comparisons on the original key carrier.
These equalities describe its branches without inserting decoding into them. -/

def int64Greater (x y : Int64) : Bool := SignedComparison.int64Ltb y x

theorem decode_greater (x y : Int64) :
    SignedComparison.intGtb x.toInt y.toInt = int64Greater x y := by
  apply Bool.eq_iff_iff.mpr
  simp only [SignedComparison.intGtb_true_iff, int64Greater,
    SignedComparison.int64Ltb_true_iff]

theorem nat_int_greater (x y : Nat) :
    SignedComparison.intGtb (x : Int) (y : Int) = natGreater x y := by
  apply Bool.eq_iff_iff.mpr
  simp [SignedComparison.intGtb_true_iff, natGreater]

theorem decode_smash (left right : BinaryTree Int64) :
    (smash int64Greater left right).map Int64.toInt =
      smash SignedComparison.intGtb (left.map Int64.toInt) (right.map Int64.toInt) :=
  map_smash _ _ _ decode_greater left right

theorem decode_carry (queue : Queue Int64) (tree : BinaryTree Int64) :
    mapQueue Int64.toInt (carry int64Greater queue tree) =
      carry SignedComparison.intGtb (mapQueue Int64.toInt queue) (tree.map Int64.toInt) :=
  map_carry _ _ _ decode_greater queue tree

theorem decode_insert (key : Int64) (queue : Queue Int64) :
    mapQueue Int64.toInt (insert int64Greater key queue) =
      insert SignedComparison.intGtb key.toInt (mapQueue Int64.toInt queue) :=
  map_insert _ _ _ decode_greater key queue

theorem decode_join (left right : Queue Int64) (tree : BinaryTree Int64) :
    mapQueue Int64.toInt (join int64Greater left right tree) =
      join SignedComparison.intGtb (mapQueue Int64.toInt left)
        (mapQueue Int64.toInt right) (tree.map Int64.toInt) :=
  map_join _ _ _ decode_greater left right tree

theorem decode_unzip (tree : BinaryTree Int64) (cont : Queue Int64 → Queue Int64)
    (otherCont : Queue Int → Queue Int)
    (agree : ∀ queue, mapQueue Int64.toInt (cont queue) =
      otherCont (mapQueue Int64.toInt queue)) :
    mapQueue Int64.toInt (unzip tree cont) = unzip (tree.map Int64.toInt) otherCont :=
  map_unzip _ tree cont otherCont agree

theorem decode_heapDeleteMax (tree : BinaryTree Int64) :
    mapQueue Int64.toInt (heapDeleteMax tree) = heapDeleteMax (tree.map Int64.toInt) :=
  map_heapDeleteMax _ tree

theorem decode_findMaxAux (current : Int64) (queue : Queue Int64) :
    (findMaxAux int64Greater current queue).toInt =
      findMaxAux SignedComparison.intGtb current.toInt (mapQueue Int64.toInt queue) :=
  map_findMaxAux _ _ _ decode_greater current queue

theorem decode_findMax (queue : Queue Int64) :
    (findMax int64Greater queue).map Int64.toInt =
      findMax SignedComparison.intGtb (mapQueue Int64.toInt queue) :=
  map_findMax _ _ _ decode_greater queue

theorem decode_deleteMaxAux (threshold : Int64) (queue : Queue Int64) :
    (mapQueue Int64.toInt (deleteMaxAux int64Greater threshold queue).1,
      mapQueue Int64.toInt (deleteMaxAux int64Greater threshold queue).2) =
      deleteMaxAux SignedComparison.intGtb threshold.toInt (mapQueue Int64.toInt queue) :=
  map_deleteMaxAux _ _ _ decode_greater threshold queue

theorem decode_deleteMax (queue : Queue Int64) :
    (deleteMax int64Greater queue).map
        (fun result => (result.1.toInt, mapQueue Int64.toInt result.2)) =
      deleteMax SignedComparison.intGtb (mapQueue Int64.toInt queue) :=
  map_deleteMax _ _ _ decode_greater queue

theorem decode_merge (left right : Queue Int64) :
    mapQueue Int64.toInt (merge int64Greater left right) =
      merge SignedComparison.intGtb (mapQueue Int64.toInt left) (mapQueue Int64.toInt right) :=
  map_merge _ _ _ decode_greater left right

/-! The list comparison uses the already accepted source selector. Its exact
remainder order and tie branch are transported along with the selected key. -/

theorem map_select (label : K → L) (rel : K → K → Prop) [DecidableRel rel]
    (otherRel : L → L → Prop) [DecidableRel otherRel]
    (agree : ∀ x y, otherRel (label x) (label y) ↔ rel x y)
    (seed : K) (tail : List K) :
    (label (Applications.Sorting.SourceSelection.select rel seed tail).1,
      (Applications.Sorting.SourceSelection.select rel seed tail).2.map label) =
      Applications.Sorting.SourceSelection.select otherRel (label seed) (tail.map label) := by
  induction tail generalizing seed with
  | nil => rfl
  | cons head tail ih =>
    simp only [Applications.Sorting.SourceSelection.select_cons, List.map_cons]
    by_cases h : rel seed head
    · have hh := (agree seed head).mpr h
      simp only [h, hh, ↓reduceIte]
      rw [← ih seed]
      rfl
    · have hh : ¬ otherRel (label seed) (label head) := fun he => h ((agree seed head).mp he)
      simp only [h, hh, ↓reduceIte]
      rw [← ih head]
      rfl

def listDeleteMax (leq : K → K → Bool) : List K → Option (K × List K)
  | [] => none
  | seed :: tail => some (Applications.Sorting.SourceSelection.select
      (fun candidate head => leq head candidate = true) seed tail)

theorem map_listDeleteMax (label : K → L) (leq : K → K → Bool)
    (other : L → L → Bool)
    (agree : ∀ x y, other (label x) (label y) = leq x y) (queue : List K) :
    (listDeleteMax leq queue).map (fun result => (label result.1, result.2.map label)) =
      listDeleteMax other (queue.map label) := by
  cases queue with
  | nil => rfl
  | cons seed tail =>
    apply congrArg some
    exact map_select label _ _ (fun x y => by rw [agree]) seed tail

theorem decode_leq (x y : Int64) :
    SignedComparison.intLeb x.toInt y.toInt = SignedComparison.int64Leb x y := by
  apply Bool.eq_iff_iff.mpr
  simp only [SignedComparison.intLeb_true_iff, SignedComparison.int64Leb_true_iff]

theorem decode_listDeleteMax (queue : List Int64) :
    (listDeleteMax SignedComparison.int64Leb queue).map
        (fun result => (result.1.toInt, result.2.map Int64.toInt)) =
      listDeleteMax SignedComparison.intLeb (queue.map Int64.toInt) :=
  map_listDeleteMax _ _ _ decode_leq queue

theorem nat_listDeleteMax (queue : List Nat) :
    listDeleteMax (fun x y : Nat => decide (x ≤ y)) queue =
      Search.ListMaximumQueue.deleteMax queue := by
  cases queue with
  | nil => rfl
  | cons seed tail =>
    simp [listDeleteMax, Search.ListMaximumQueue.deleteMax, Search.ListMaximumQueue.selectMax]

/-- Conversion is checked before running operations. This accepts the full
signed carrier; the textbook's Nat specialization uses the narrower guard below. -/
def checkedInt64 (key : Int) : Option Int64 :=
  if -(2 : Int) ^ 63 ≤ key ∧ key < (2 : Int) ^ 63 then some (Int64.ofInt key) else none

def checkedNat64 (key : Nat) : Option Int64 :=
  if key < 2 ^ 63 then some (Int64.ofInt key) else none

theorem checkedInt64_decode (key : Int) :
    (checkedInt64 key).map Int64.toInt =
      if -(2 : Int) ^ 63 ≤ key ∧ key < (2 : Int) ^ 63 then some key else none := by
  by_cases h : -(2 : Int) ^ 63 ≤ key ∧ key < (2 : Int) ^ 63
  · simp only [checkedInt64, ite_eq_left h, Option.map_some]
    exact congrArg some (SignedComparison.int64_ofInt_toInt key h.1 h.2)
  · simp only [checkedInt64, ite_eq_right h, Option.map_none]

theorem checkedNat64_decode (key : Nat) :
    (checkedNat64 key).map Int64.toInt = if key < 2 ^ 63 then some (key : Int) else none := by
  by_cases h : key < 2 ^ 63
  · simp only [checkedNat64, ite_eq_left h, Option.map_some]
    exact congrArg some (SignedComparison.int64_ofNat_toInt key h)
  · simp only [checkedNat64, ite_eq_right h, Option.map_none]

theorem checkedInt64_none (key : Int) :
    checkedInt64 key = none ↔ key < -(2 : Int) ^ 63 ∨ (2 : Int) ^ 63 ≤ key := by
  simp [checkedInt64]
  omega

theorem checkedNat64_none (key : Nat) : checkedNat64 key = none ↔ 2 ^ 63 ≤ key := by
  simp [checkedNat64]

abbrev NatBounded (queue : Queue Nat) : Prop := ∀ key ∈ contents queue, key < 2 ^ 63

theorem decode_encode_tree (tree : BinaryTree Nat)
    (bounded : ∀ key ∈ treeContents tree, key < 2 ^ 63) :
    (tree.map (fun key : Nat => Int64.ofInt key)).map Int64.toInt =
      tree.map (fun key : Nat => (key : Int)) := by
  induction tree with
  | nil => rfl
  | node key left right ihl ihr =>
    have hk : key < 2 ^ 63 := bounded key (by simp [treeContents])
    have hl : ∀ x ∈ treeContents left, x < 2 ^ 63 :=
      fun x hx => bounded x (by simp [treeContents] at hx ⊢; exact Or.inr (Or.inl hx))
    have hr : ∀ x ∈ treeContents right, x < 2 ^ 63 :=
      fun x hx => bounded x (by simp [treeContents] at hx ⊢; exact Or.inr (Or.inr hx))
    simp only [BinaryTree.map, SignedComparison.int64_ofNat_toInt key hk, ihl hl, ihr hr]

theorem decode_encode_queue (queue : Queue Nat) (bounded : NatBounded queue) :
    mapQueue Int64.toInt (mapQueue (fun key : Nat => Int64.ofInt key) queue) =
      mapQueue (fun key : Nat => (key : Int)) queue := by
  induction queue with
  | nil => rfl
  | cons tree tail ih =>
    have ht : ∀ key ∈ treeContents tree, key < 2 ^ 63 :=
      fun key hk => bounded key (by simp [contents_cons, hk])
    have htail : NatBounded tail := fun key hk => bounded key (by simp [contents_cons, hk])
    simp only [mapQueue_cons, decode_encode_tree tree ht, ih htail]

theorem nat_insert_transport (key : Nat) (queue : Queue Nat)
    (keyBound : key < 2 ^ 63) (bounded : NatBounded queue) :
    mapQueue Int64.toInt
        (insert int64Greater (Int64.ofInt key) (mapQueue (fun n : Nat => Int64.ofInt n) queue)) =
      mapQueue (fun n : Nat => (n : Int)) (insert natGreater key queue) := by
  rw [decode_insert, decode_encode_queue queue bounded,
    SignedComparison.int64_ofNat_toInt key keyBound]
  exact (map_insert (fun n : Nat => (n : Int)) _ _ nat_int_greater key queue).symm

theorem nat_merge_transport (left right : Queue Nat)
    (leftBound : NatBounded left) (rightBound : NatBounded right) :
    mapQueue Int64.toInt (merge int64Greater
        (mapQueue (fun n : Nat => Int64.ofInt n) left)
        (mapQueue (fun n : Nat => Int64.ofInt n) right)) =
      mapQueue (fun n : Nat => (n : Int)) (merge natGreater left right) := by
  rw [decode_merge, decode_encode_queue left leftBound, decode_encode_queue right rightBound]
  exact (map_merge (fun n : Nat => (n : Int)) _ _ nat_int_greater left right).symm

theorem nat_findMax_transport (queue : Queue Nat) (bounded : NatBounded queue) :
    (findMax int64Greater (mapQueue (fun n : Nat => Int64.ofInt n) queue)).map Int64.toInt =
      (findMax natGreater queue).map (fun n : Nat => (n : Int)) := by
  rw [decode_findMax, decode_encode_queue queue bounded]
  exact (map_findMax (fun n : Nat => (n : Int)) _ _ nat_int_greater queue).symm

theorem nat_deleteMax_transport (queue : Queue Nat) (bounded : NatBounded queue) :
    (deleteMax int64Greater (mapQueue (fun n : Nat => Int64.ofInt n) queue)).map
        (fun result => (result.1.toInt, mapQueue Int64.toInt result.2)) =
      (deleteMax natGreater queue).map
        (fun result => ((result.1 : Int), mapQueue (fun n : Nat => (n : Int)) result.2)) := by
  rw [decode_deleteMax, decode_encode_queue queue bounded]
  exact (map_deleteMax (fun n : Nat => (n : Int)) _ _ nat_int_greater queue).symm

theorem nat_list_delete_transport (queue : List Nat) (bounded : ∀ key ∈ queue, key < 2 ^ 63) :
    (listDeleteMax SignedComparison.int64Leb
        (queue.map (fun n : Nat => Int64.ofInt n))).map
        (fun result => (result.1.toInt, result.2.map Int64.toInt)) =
      (Search.ListMaximumQueue.deleteMax queue).map
        (fun result => ((result.1 : Int), result.2.map (fun n : Nat => (n : Int)))) := by
  rw [decode_listDeleteMax]
  have roundtrip : (queue.map (fun n : Nat => Int64.ofInt n)).map Int64.toInt =
      queue.map (fun n : Nat => (n : Int)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro n hn
    exact SignedComparison.int64_ofNat_toInt n (bounded n hn)
  rw [roundtrip, ← nat_listDeleteMax]
  symm
  apply map_listDeleteMax
  intro x y
  apply Bool.eq_iff_iff.mpr
  simp [SignedComparison.intLeb_true_iff]

end Representations.DecodedBinomialQueue

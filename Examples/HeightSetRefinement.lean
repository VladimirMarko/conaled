import Applications.Trees.AVL.SetRefinement
import Examples.HeightUpdates

/-!
# Connected cached Set-refinement cases

S01–S08 use the independently worked expectations retained in the Set preparation
paper. Closed computations establish literal premises and shapes; the public
refinement, Set laws and mixed-history clients supply their semantic connection.
Universal histories keep payload and annotation universes independent.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.HeightSetRefinement
open Trees
open Search.AbstractSet
open HeightUpdates (HTree payloads heightNode heightSingleton)
universe u v w
variable {α : Type u} {σ : Type v} {τ : Type w}

/-! Constructive local decision procedures serve only the finite fixtures.
No annotation equality premise enters the public abstract history contracts. -/
private def balancedDecidable (d : Nat) :
    (t : BinaryTree α) → Decidable (HeightBalance.BalancedD d t)
  | .nil => isTrue trivial
  | .node _ l r => by
      letI := balancedDecidable d l
      letI := balancedDecidable d r
      exact inferInstanceAs (Decidable
        (HeightBalance.BalancedD d l ∧ HeightBalance.BalancedD d r ∧
          l.height ≤ r.height + d ∧ r.height ≤ l.height + d))

private def cacheDecidable [DecidableEq σ] (ann : HeightBalance.HeightAnnotation α σ) :
    (t : BinaryTree (α × σ)) → Decidable (HeightBalance.CacheValid ann t)
  | .nil => isTrue (HeightBalance.cacheValid_nil ann)
  | .node (a, s) l r => by
      letI := cacheDecidable ann l
      letI := cacheDecidable ann r
      exact inferInstanceAs (Decidable
        (HeightBalance.CacheValid ann l ∧ HeightBalance.CacheValid ann r ∧
          s = ann.combine (Cached.read ann.empty l) a (Cached.read ann.empty r)))

local instance (d : Nat) (t : BinaryTree α) :
    Decidable (HeightBalance.BalancedD d t) := balancedDecidable d t
local instance [DecidableEq σ] (ann : HeightBalance.HeightAnnotation α σ)
    (t : BinaryTree (α × σ)) : Decidable (HeightBalance.CacheValid ann t) :=
  cacheDecidable ann t
local instance [DecidableEq σ] (ann : HeightBalance.HeightAnnotation α σ) (d : Nat)
    (t : BinaryTree (α × σ)) : Decidable (HeightBalance.ValidD ann d t) :=
  inferInstanceAs (Decidable
    (HeightBalance.BalancedD d (Cached.erase t) ∧ HeightBalance.CacheValid ann t))
local instance (t : BinaryTree (α × Nat)) : Decidable (AVL.CacheValid t) :=
  cacheDecidable AVL.heightAnnotation t
local instance (t : BinaryTree (α × Nat)) : Decidable (AVL.Valid t) :=
  decidable_of_iff (HeightBalance.ValidD AVL.heightAnnotation 1 t) (AVL.validD_one_iff t)
local instance [LT α] [DecidableLT α] (xs : List α) :
    Decidable (Search.OrderedList.Strict xs) :=
  inferInstanceAs (Decidable (xs.Pairwise (· < ·)))
local instance [LT α] [DecidableLT α] [DecidableEq σ]
    (ann : HeightBalance.HeightAnnotation α σ) (d : Nat) (t : BinaryTree (α × σ)) :
    Decidable (HeightBalance.SetValid ann d t) :=
  inferInstanceAs (Decidable
    (HeightBalance.ValidD ann d t ∧ Search.OrderedList.Strict (payloads t)))
local instance [LT α] [DecidableLT α] (t : BinaryTree (α × Nat)) :
    Decidable (AVL.SetValid t) :=
  inferInstanceAs (Decidable (AVL.Valid t ∧ Search.OrderedList.Strict (payloads t)))

/-- The ordinary adapter supplies the same arbitrary-word consumers directly. -/
theorem ordinary_history_contract [LinearOrder α]
    (updates : List (Update α)) (t : BinaryTree (α × Nat)) (ht : AVL.SetValid t) :
    payloads (execute AVL.deleteOps updates t) =
        execute Search.OrderedList.ops updates (payloads t) ∧
      AVL.SetValid (execute AVL.deleteOps updates t) ∧
      (∀ n, AVL.SetValid (execute AVL.deleteOps (updates.take n) t)) ∧
      Trees.setTree (Cached.erase (execute AVL.deleteOps updates t)) =
        updates.foldl meaningStep (Trees.setTree (Cached.erase t)) ∧
      (∀ x, Search.OrderedMap.containsKey x (execute AVL.deleteOps updates t) =
        Search.OrderedList.ops.member x
          (execute Search.OrderedList.ops updates (payloads t))) ∧
      (∀ x, Search.OrderedMap.containsKey x (execute AVL.deleteOps updates t) = true ↔
        (updates.foldl meaningStep (Trees.setTree (Cached.erase t))) x) :=
  ⟨AVL.inorderRefinement.execute Search.OrderedList.laws updates ht,
    AVL.setLaws.execute_valid updates ht,
    fun n => AVL.setLaws.prefix_valid updates n ht,
    AVL.setLaws.execute_observe updates ht,
    fun x => AVL.inorderRefinement.member_execute Search.OrderedList.laws updates ht x,
    fun x => AVL.setLaws.member_execute updates ht x⟩

/-- Symbolic mixed histories preserve full validity and both independent observations. -/
theorem generic_history_contract [LinearOrder α]
    (ann : HeightBalance.HeightAnnotation α σ) (d : Nat) (hd : 1 ≤ d)
    (updates : List (Update α)) (t : BinaryTree (α × σ))
    (ht : HeightBalance.SetValid ann d t) :
    payloads (execute (HeightBalance.deleteOps ann d) updates t) =
        execute Search.OrderedList.ops updates (payloads t) ∧
      HeightBalance.SetValid ann d (execute (HeightBalance.deleteOps ann d) updates t) ∧
      (∀ n, HeightBalance.SetValid ann d
        (execute (HeightBalance.deleteOps ann d) (updates.take n) t)) ∧
      Trees.setTree (Cached.erase (execute (HeightBalance.deleteOps ann d) updates t)) =
        updates.foldl meaningStep (Trees.setTree (Cached.erase t)) ∧
      (∀ x, Search.OrderedMap.containsKey x
          (execute (HeightBalance.deleteOps ann d) updates t) =
        Search.OrderedList.ops.member x
          (execute Search.OrderedList.ops updates (payloads t))) ∧
      (∀ x, Search.OrderedMap.containsKey x
          (execute (HeightBalance.deleteOps ann d) updates t) = true ↔
        (updates.foldl meaningStep (Trees.setTree (Cached.erase t))) x) :=
  ⟨(HeightBalance.inorderRefinement ann d hd).execute Search.OrderedList.laws updates ht,
    (HeightBalance.setLaws ann d hd).execute_valid updates ht,
    fun n => (HeightBalance.setLaws ann d hd).prefix_valid updates n ht,
    (HeightBalance.setLaws ann d hd).execute_observe updates ht,
    fun x => (HeightBalance.inorderRefinement ann d hd).member_execute
      Search.OrderedList.laws updates ht x,
    fun x => (HeightBalance.setLaws ann d hd).member_execute updates ht x⟩

/-- Different annotation universes and tolerances share exact ordered observations. -/
theorem independent_representations [LinearOrder α]
    (leftAnn : HeightBalance.HeightAnnotation α σ)
    (rightAnn : HeightBalance.HeightAnnotation α τ)
    (d e : Nat) (hd : 1 ≤ d) (he : 1 ≤ e) (updates : List (Update α))
    (left : BinaryTree (α × σ)) (right : BinaryTree (α × τ))
    (hl : HeightBalance.SetValid leftAnn d left)
    (hr : HeightBalance.SetValid rightAnn e right)
    (same : payloads left = payloads right) :
    payloads (execute (HeightBalance.deleteOps leftAnn d) updates left) =
        payloads (execute (HeightBalance.deleteOps rightAnn e) updates right) ∧
      ∀ x, Search.OrderedMap.containsKey x
          (execute (HeightBalance.deleteOps leftAnn d) updates left) =
        Search.OrderedMap.containsKey x
          (execute (HeightBalance.deleteOps rightAnn e) updates right) :=
  ⟨HeightBalance.inorder_execute_eq leftAnn rightAnn d e hd he updates hl hr same,
    fun x => HeightBalance.member_execute_eq leftAnn rightAnn d e hd he updates hl hr same x⟩

/-- Positive integer tolerance transports exactly, for every history and every prefix. -/
theorem integer_history_contract [LinearOrder α]
    (ann : HeightBalance.HeightAnnotation α σ) (D : Int) (hD : 1 ≤ D)
    (updates : List (Update α)) (t : BinaryTree (α × σ))
    (ht : HeightBalance.SetValid ann D.toNat t) :
    (D.toNat : Int) = D ∧
      HeightBalance.SetValid ann D.toNat
        (execute (HeightBalance.deleteOps ann D.toNat) updates t) ∧
      (∀ n, HeightBalance.SetValid ann D.toNat
        (execute (HeightBalance.deleteOps ann D.toNat) (updates.take n) t)) ∧
      payloads (execute (HeightBalance.deleteOps ann D.toNat) updates t) =
        execute Search.OrderedList.ops updates (payloads t) ∧
      (∀ x, Search.OrderedMap.containsKey x
          (execute (HeightBalance.deleteOps ann D.toNat) updates t) =
        Search.OrderedList.ops.member x
          (execute Search.OrderedList.ops updates (payloads t))) := by
  have hd := (HeightBalance.int_tolerance_toNat D hD).1
  exact ⟨(HeightBalance.int_tolerance_toNat D hD).2,
    (HeightBalance.setLaws ann D.toNat hd).execute_valid updates ht,
    fun n => (HeightBalance.setLaws ann D.toNat hd).prefix_valid updates n ht,
    (HeightBalance.inorderRefinement ann D.toNat hd).execute
      Search.OrderedList.laws updates ht,
    fun x => (HeightBalance.inorderRefinement ann D.toNat hd).member_execute
      Search.OrderedList.laws updates ht x⟩

/-! S01: the actual mixed word, including duplicate insertion and absent deletion. -/
def mixedWord : List (Update Nat) :=
  [.insert 3, .insert 1, .insert 2, .insert 2, .delete 9, .delete 1]

def mixedExpected : Nat → List Nat
  | 0 => []
  | 1 => [3]
  | 2 => [1, 3]
  | 3 => [1, 2, 3]
  | 4 => [1, 2, 3]
  | 5 => [1, 2, 3]
  | _ => [2, 3]

def ordinaryRun : HTree := execute AVL.deleteOps mixedWord .nil
def genericRun (d : Nat) : HTree :=
  execute (HeightBalance.deleteOps AVL.heightAnnotation d) mixedWord .nil

theorem mixed_target_prefix (n : Nat) :
    execute Search.OrderedList.ops (mixedWord.take n) [] = mixedExpected n := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
        cases n with
        | zero => rfl
        | succ n =>
          cases n with
          | zero => rfl
          | succ n =>
            cases n with
            | zero => rfl
            | succ n =>
              have hlen : mixedWord.length ≤ n + 1 + 1 + 1 + 1 + 1 + 1 := by
                change 6 ≤ n + 1 + 1 + 1 + 1 + 1 + 1
                omega
              rw [List.take_of_length_le hlen]
              rfl

theorem ordinary_prefix_inorder (n : Nat) :
    payloads (execute AVL.deleteOps (mixedWord.take n) (.nil : HTree)) = mixedExpected n :=
  (AVL.inorderRefinement.execute_from_empty Search.OrderedList.laws
    (mixedWord.take n)).trans (mixed_target_prefix n)

theorem ordinary_prefix_valid (n : Nat) :
    AVL.SetValid (execute AVL.deleteOps (mixedWord.take n) (.nil : HTree)) :=
  AVL.setLaws.prefix_valid mixedWord n AVL.setLaws.empty_valid

theorem ordinary_final_inorder : payloads ordinaryRun = [2, 3] :=
  (AVL.inorderRefinement.execute_from_empty Search.OrderedList.laws mixedWord).trans rfl

theorem ordinary_final_valid : AVL.SetValid ordinaryRun :=
  AVL.setLaws.execute_valid mixedWord AVL.setLaws.empty_valid

theorem ordinary_final_query (x : Nat) :
    Search.OrderedMap.containsKey x ordinaryRun = decide (x ∈ [2, 3]) := by
  have h := AVL.inorderRefinement.member_execute Search.OrderedList.laws mixedWord
    (s := (.nil : HTree)) AVL.setValid_nil x
  exact h

theorem ordinary_final_queries :
    Search.OrderedMap.containsKey 1 ordinaryRun = false ∧
      Search.OrderedMap.containsKey 9 ordinaryRun = false ∧
      Search.OrderedMap.containsKey 2 ordinaryRun = true ∧
      Search.OrderedMap.containsKey 3 ordinaryRun = true :=
  ⟨(ordinary_final_query 1).trans (by decide),
    (ordinary_final_query 9).trans (by decide),
    (ordinary_final_query 2).trans (by decide),
    (ordinary_final_query 3).trans (by decide)⟩

theorem ordinary_final_set (x : Nat) :
    x ∈ Trees.setTree (Cached.erase ordinaryRun) ↔ x = 2 ∨ x = 3 := by
  have h := AVL.setLaws.execute_from_empty mixedWord
  change Trees.setTree (Cached.erase ordinaryRun) =
    mixedWord.foldl meaningStep (fun _ => False) at h
  rw [h]
  change (x ≠ 1 ∧ x ≠ 9 ∧ (x = 2 ∨ x = 2 ∨ x = 1 ∨ x = 3 ∨ False)) ↔
    x = 2 ∨ x = 3
  constructor
  · rintro ⟨hne, _, hx⟩
    rcases hx with hx | hx | hx | hx | hx
    · exact Or.inl hx
    · exact Or.inl hx
    · exact (hne hx).elim
    · exact Or.inr hx
    · exact hx.elim
  · rintro (rfl | rfl) <;> decide

/-! S02: refinement agreement permits distinct valid concrete representations. -/
def firstThree : List (Update Nat) := [.insert 3, .insert 1, .insert 2]
def descendingWord : List (Update Nat) := [.insert 4, .insert 3, .insert 2, .insert 1]

theorem first_three_shapes :
    execute AVL.deleteOps firstThree (.nil : HTree) =
        heightNode 2 (heightSingleton 1) (heightSingleton 3) ∧
      execute (HeightBalance.deleteOps AVL.heightAnnotation 2) firstThree (.nil : HTree) =
        heightNode 3 (heightNode 1 .nil (heightSingleton 2)) .nil ∧
      (execute AVL.deleteOps firstThree (.nil : HTree)).height = 2 ∧
      (execute (HeightBalance.deleteOps AVL.heightAnnotation 2) firstThree
        (.nil : HTree)).height = 3 := by decide

theorem first_three_validity_separator :
    AVL.SetValid (execute AVL.deleteOps firstThree (.nil : HTree)) ∧
      HeightBalance.SetValid AVL.heightAnnotation 2
        (execute (HeightBalance.deleteOps AVL.heightAnnotation 2) firstThree .nil) ∧
      ¬ AVL.SetValid
        (execute (HeightBalance.deleteOps AVL.heightAnnotation 2) firstThree .nil) := by
  refine ⟨AVL.setLaws.execute_valid firstThree AVL.setLaws.empty_valid,
    (HeightBalance.setLaws AVL.heightAnnotation 2 (by decide)).execute_valid firstThree
      (HeightBalance.setValid_nil _ 2), ?_⟩
  intro h
  exact (by decide : ¬ AVL.Valid
    (execute (HeightBalance.deleteOps AVL.heightAnnotation 2) firstThree (.nil : HTree))) h.1

theorem mixed_distinct_shapes :
    ordinaryRun = heightNode 2 .nil (heightSingleton 3) ∧
      genericRun 2 = heightNode 3 (heightSingleton 2) .nil ∧
      ordinaryRun ≠ genericRun 2 := by decide

theorem generic_mixed_valid (d : Nat) (hd : 1 ≤ d) :
    HeightBalance.SetValid AVL.heightAnnotation d (genericRun d) :=
  (HeightBalance.setLaws AVL.heightAnnotation d hd).execute_valid mixedWord
    (HeightBalance.setValid_nil AVL.heightAnnotation d)

theorem generic_mixed_inorder (d : Nat) (hd : 1 ≤ d) :
    payloads (genericRun d) = [2, 3] :=
  ((HeightBalance.inorderRefinement AVL.heightAnnotation d hd).execute_from_empty
    Search.OrderedList.laws mixedWord).trans rfl

theorem mixed_representations_agree :
    payloads ordinaryRun = payloads (genericRun 2) ∧
      ∀ x, Search.OrderedMap.containsKey x ordinaryRun =
        Search.OrderedMap.containsKey x (genericRun 2) :=
  independent_representations AVL.heightAnnotation AVL.heightAnnotation 1 2
    (by decide) (by decide) mixedWord (.nil : HTree) .nil
    (HeightBalance.setValid_nil _ 1) (HeightBalance.setValid_nil _ 2) rfl

theorem descending_shapes :
    execute (HeightBalance.deleteOps AVL.heightAnnotation 3) descendingWord (.nil : HTree) =
        heightNode 4 (heightNode 3 (heightNode 2 (heightSingleton 1) .nil) .nil) .nil ∧
      execute (HeightBalance.deleteOps AVL.heightAnnotation 2) descendingWord (.nil : HTree) =
        HeightUpdates.insertD2SingleLeftOutput ∧
      (execute (HeightBalance.deleteOps AVL.heightAnnotation 3) descendingWord
        (.nil : HTree)).height = 4 ∧
      (execute (HeightBalance.deleteOps AVL.heightAnnotation 2) descendingWord
        (.nil : HTree)).height = 3 := by decide

theorem descending_valid_and_agree :
    HeightBalance.SetValid AVL.heightAnnotation 3
        (execute (HeightBalance.deleteOps AVL.heightAnnotation 3) descendingWord .nil) ∧
      HeightBalance.SetValid AVL.heightAnnotation 2
        (execute (HeightBalance.deleteOps AVL.heightAnnotation 2) descendingWord .nil) ∧
      payloads (execute (HeightBalance.deleteOps AVL.heightAnnotation 3) descendingWord .nil) =
        payloads (execute (HeightBalance.deleteOps AVL.heightAnnotation 2) descendingWord .nil) :=
  ⟨(HeightBalance.setLaws AVL.heightAnnotation 3 (by decide)).execute_valid descendingWord
      (HeightBalance.setValid_nil _ 3),
    (HeightBalance.setLaws AVL.heightAnnotation 2 (by decide)).execute_valid descendingWord
      (HeightBalance.setValid_nil _ 2),
    HeightBalance.inorder_execute_eq AVL.heightAnnotation AVL.heightAnnotation 3 2
      (by decide) (by decide) descendingWord
      (HeightBalance.setValid_nil _ 3) (HeightBalance.setValid_nil _ 2) rfl⟩

/-! S03: correct height/cache data cannot substitute for the ordering premise. -/
theorem unordered_membership_separator :
    AVL.Valid HeightUpdates.unordered ∧
      Search.OrderedMap.containsKey 9 HeightUpdates.unordered = false ∧
      9 ∈ Trees.setTree (Cached.erase HeightUpdates.unordered) ∧
      ¬ AVL.SetValid HeightUpdates.unordered := by
  refine ⟨HeightUpdates.unordered_still_valid.1, by decide, ?_, ?_⟩
  · exact (Trees.mem_inorder_iff_mem_setTree 9 _).mp (by decide)
  · intro h
    exact (by decide : ¬ Search.OrderedList.Strict (payloads HeightUpdates.unordered)) h.2

/-! S04: search/list correctness does not silently repair or validate a stored cache. -/
theorem stale_height_query :
    Search.OrderedList.Strict (payloads HeightUpdates.rawDuplicate) ∧
      Search.OrderedMap.containsKey 5 HeightUpdates.rawDuplicate = true ∧
      ¬ AVL.CacheValid HeightUpdates.rawDuplicate ∧
      ¬ AVL.SetValid HeightUpdates.rawDuplicate := by
  refine ⟨by decide, ?_, by decide, ?_⟩
  · exact (HeightBalance.member_inorder 5 HeightUpdates.rawDuplicate (by decide)).trans
      (by decide)
  · intro h
    exact (by decide : ¬ AVL.CacheValid HeightUpdates.rawDuplicate) h.1.2

theorem ordered_chain_balance_separator :
    Search.OrderedList.Strict (payloads (HeightUpdates.leftChain 1 3)) ∧
      AVL.CacheValid (HeightUpdates.leftChain 1 3) ∧
      HeightBalance.SetValid AVL.heightAnnotation 2 (HeightUpdates.leftChain 1 3) ∧
      ¬ AVL.SetValid (HeightUpdates.leftChain 1 3) := by
  refine ⟨HeightUpdates.strict_leftChain 1 3, HeightUpdates.cache_leftChain 1 3,
    ⟨HeightUpdates.valid_leftChain 2 1 3 (by decide), HeightUpdates.strict_leftChain 1 3⟩, ?_⟩
  intro h
  exact (by decide : ¬ AVL.Valid (HeightUpdates.leftChain 1 3)) h.1

/-! S05: nonstrict ordering admits duplicate keys and breaks deletion-as-set-removal. -/
def duplicateKeys : HTree := heightNode 1 (heightSingleton 1) .nil

theorem duplicate_key_shape_and_order :
    AVL.Valid duplicateKeys ∧ (payloads duplicateKeys).Pairwise (· ≤ ·) ∧
      ¬ Search.OrderedList.Strict (payloads duplicateKeys) ∧
      AVL.delete 1 duplicateKeys = heightSingleton 1 ∧
      Search.OrderedList.delete 1 (payloads duplicateKeys) = [1] := by decide

theorem duplicate_key_set_removal_fails :
    ¬ AVL.SetValid duplicateKeys ∧
      ¬ (1 ∈ Trees.setTree (Cached.erase (AVL.delete 1 duplicateKeys)) ↔
        remove 1 (Trees.setTree (Cached.erase duplicateKeys)) 1) := by
  constructor
  · intro h
    exact duplicate_key_shape_and_order.2.2.1 h.2
  · intro h
    have hm : 1 ∈ Trees.setTree (Cached.erase (AVL.delete 1 duplicateKeys)) :=
      (Trees.mem_inorder_iff_mem_setTree 1 _).mp (by decide)
    exact (h.mp hm).1 rfl

/-! S06: zero tolerance retains raw programs and observations, not full update closure. -/
theorem zero_tolerance_insert_separator :
    HeightBalance.SetValid AVL.heightAnnotation 0 (heightSingleton 2) ∧
      HeightBalance.CacheValid AVL.heightAnnotation
        ((HeightBalance.deleteOps AVL.heightAnnotation 0).insert 1 (heightSingleton 2)) ∧
      payloads ((HeightBalance.deleteOps AVL.heightAnnotation 0).insert 1 (heightSingleton 2)) =
        Search.OrderedList.insert 1 (payloads (heightSingleton 2)) ∧
      ¬ HeightBalance.SetValid AVL.heightAnnotation 0
        ((HeightBalance.deleteOps AVL.heightAnnotation 0).insert 1 (heightSingleton 2)) := by
  refine ⟨⟨HeightUpdates.zero_insert_separator.1, by decide⟩,
    HeightUpdates.zero_insert_separator.2.1, HeightUpdates.zero_insert_separator.2.2.1, ?_⟩
  intro h
  exact HeightUpdates.zero_insert_separator.2.2.2 h.1

theorem zero_tolerance_delete_separator :
    HeightBalance.SetValid AVL.heightAnnotation 0 HeightUpdates.three ∧
      ¬ HeightBalance.SetValid AVL.heightAnnotation 0
        ((HeightBalance.deleteOps AVL.heightAnnotation 0).delete 3 HeightUpdates.three) := by
  refine ⟨⟨HeightUpdates.zero_delete_separator.1, by decide⟩, ?_⟩
  intro h
  exact HeightUpdates.zero_delete_separator.2.2.2 h.1

theorem zero_tolerance_member (x : Nat) :
    (HeightBalance.deleteOps AVL.heightAnnotation 0).member x (heightSingleton 2) =
      decide (x ∈ [2]) :=
  HeightBalance.member_inorder x (heightSingleton 2) (by decide)

theorem negative_tolerance_has_no_positive_bridge :
    (-1 : Int).toNat = 0 ∧ ¬ 1 ≤ (-1 : Int).toNat ∧
      ¬ |(0 : Int) - (0 : Int)| ≤ (-1 : Int) :=
  ⟨HeightUpdates.negative_integer_is_not_a_natural_invariant.2.1, by decide,
    HeightUpdates.negative_integer_is_not_a_natural_invariant.1⟩

/-! S07: the Set history supplies full cache correctness to independent readers. -/
def annotationWord : List (Update Nat) := [.insert 7, .delete 7]

theorem maximum_base_set_valid :
    HeightBalance.SetValid HeightUpdates.maximumAnnotation 1 HeightUpdates.maximumBase :=
  ⟨HeightUpdates.same_height_maximum_delete.2.1, by decide⟩

theorem word_base_set_valid :
    HeightBalance.SetValid (HeightUpdates.wordAnnotation Nat) 1 HeightUpdates.wordBase :=
  ⟨HeightUpdates.same_height_word_delete.2.1, by decide⟩

theorem maximum_update_full_validity :
    HeightBalance.SetValid HeightUpdates.maximumAnnotation 1 HeightUpdates.maximumWithSeven ∧
      HeightBalance.SetValid HeightUpdates.maximumAnnotation 1 HeightUpdates.maximumBase := by
  have hi := (HeightBalance.setLaws HeightUpdates.maximumAnnotation 1 (by decide)).insert_valid
    7 HeightUpdates.maximumBase maximum_base_set_valid
  change HeightBalance.SetValid HeightUpdates.maximumAnnotation 1
    (HeightBalance.insert HeightUpdates.maximumAnnotation 1 7 HeightUpdates.maximumBase) at hi
  rw [HeightUpdates.same_height_maximum_insert.1] at hi
  have hd := (HeightBalance.setLaws HeightUpdates.maximumAnnotation 1 (by decide)).delete_valid
    7 HeightUpdates.maximumWithSeven hi
  change HeightBalance.SetValid HeightUpdates.maximumAnnotation 1
    (HeightBalance.delete HeightUpdates.maximumAnnotation 1 7 HeightUpdates.maximumWithSeven) at hd
  rw [HeightUpdates.same_height_maximum_delete.1] at hd
  exact ⟨hi, hd⟩

theorem word_update_full_validity :
    HeightBalance.SetValid (HeightUpdates.wordAnnotation Nat) 1 HeightUpdates.wordWithSeven ∧
      HeightBalance.SetValid (HeightUpdates.wordAnnotation Nat) 1 HeightUpdates.wordBase := by
  have hi := (HeightBalance.setLaws (HeightUpdates.wordAnnotation Nat) 1 (by decide)).insert_valid
    7 HeightUpdates.wordBase word_base_set_valid
  change HeightBalance.SetValid (HeightUpdates.wordAnnotation Nat) 1
    (HeightBalance.insert (HeightUpdates.wordAnnotation Nat) 1 7 HeightUpdates.wordBase) at hi
  rw [HeightUpdates.same_height_word_insert.1] at hi
  have hd := (HeightBalance.setLaws (HeightUpdates.wordAnnotation Nat) 1 (by decide)).delete_valid
    7 HeightUpdates.wordWithSeven hi
  change HeightBalance.SetValid (HeightUpdates.wordAnnotation Nat) 1
    (HeightBalance.delete (HeightUpdates.wordAnnotation Nat) 1 7 HeightUpdates.wordWithSeven) at hd
  rw [HeightUpdates.same_height_word_delete.1] at hd
  exact ⟨hi, hd⟩

theorem annotation_prefixes (n : Nat) :
    HeightBalance.SetValid HeightUpdates.maximumAnnotation 1
        (execute (HeightBalance.deleteOps HeightUpdates.maximumAnnotation 1)
          (annotationWord.take n) HeightUpdates.maximumBase) ∧
      HeightBalance.SetValid (HeightUpdates.wordAnnotation Nat) 1
        (execute (HeightBalance.deleteOps (HeightUpdates.wordAnnotation Nat) 1)
          (annotationWord.take n) HeightUpdates.wordBase) :=
  ⟨(HeightBalance.setLaws HeightUpdates.maximumAnnotation 1 (by decide)).prefix_valid
      annotationWord n maximum_base_set_valid,
    (HeightBalance.setLaws (HeightUpdates.wordAnnotation Nat) 1 (by decide)).prefix_valid
      annotationWord n word_base_set_valid⟩

theorem annotation_round_trip :
    execute (HeightBalance.deleteOps HeightUpdates.maximumAnnotation 1)
        annotationWord HeightUpdates.maximumBase = HeightUpdates.maximumBase ∧
      execute (HeightBalance.deleteOps (HeightUpdates.wordAnnotation Nat) 1)
        annotationWord HeightUpdates.wordBase = HeightUpdates.wordBase := by
  constructor
  · change HeightBalance.delete HeightUpdates.maximumAnnotation 1 7
      (HeightBalance.insert HeightUpdates.maximumAnnotation 1 7 HeightUpdates.maximumBase) =
      HeightUpdates.maximumBase
    rw [HeightUpdates.same_height_maximum_insert.1, HeightUpdates.same_height_maximum_delete.1]
  · change HeightBalance.delete (HeightUpdates.wordAnnotation Nat) 1 7
      (HeightBalance.insert (HeightUpdates.wordAnnotation Nat) 1 7 HeightUpdates.wordBase) =
      HeightUpdates.wordBase
    rw [HeightUpdates.same_height_word_insert.1, HeightUpdates.same_height_word_delete.1]

theorem maximum_history_reader (updates : List (Update Nat)) (n : Nat) :
    (Cached.read HeightUpdates.maximumAnnotation.empty
      (execute (HeightBalance.deleteOps HeightUpdates.maximumAnnotation 1)
        (updates.take n) HeightUpdates.maximumBase)).2 =
      (payloads (execute (HeightBalance.deleteOps HeightUpdates.maximumAnnotation 1)
        (updates.take n) HeightUpdates.maximumBase)).max? :=
  HeightRebalance.maximum_reader_eq_list_maximum _
    ((HeightBalance.setLaws HeightUpdates.maximumAnnotation 1 (by decide)).prefix_valid
      updates n maximum_base_set_valid).1.2

theorem word_history_reader [LinearOrder α] (d : Nat) (hd : 1 ≤ d)
    (updates : List (Update α)) (n : Nat)
    (t : BinaryTree (α × (Nat × List α)))
    (ht : HeightBalance.SetValid (HeightUpdates.wordAnnotation α) d t) :
    (Cached.read (HeightUpdates.wordAnnotation α).empty
      (execute (HeightBalance.deleteOps (HeightUpdates.wordAnnotation α) d)
        (updates.take n) t)).2 =
      payloads (execute (HeightBalance.deleteOps (HeightUpdates.wordAnnotation α) d)
        (updates.take n) t) :=
  HeightRebalance.word_reader_eq_inorder _
    ((HeightBalance.setLaws (HeightUpdates.wordAnnotation α) d hd).prefix_valid
      updates n ht).1.2

theorem annotation_insert_set (x : Nat) :
    (x ∈ Trees.setTree (Cached.erase HeightUpdates.maximumWithSeven) ↔
        x = 7 ∨ x ∈ Trees.setTree (Cached.erase HeightUpdates.maximumBase)) ∧
      (x ∈ Trees.setTree (Cached.erase HeightUpdates.wordWithSeven) ↔
        x = 7 ∨ x ∈ Trees.setTree (Cached.erase HeightUpdates.wordBase)) := by
  have hm := (HeightBalance.setLaws HeightUpdates.maximumAnnotation 1 (by decide)).insert
    7 HeightUpdates.maximumBase maximum_base_set_valid x
  have hw := (HeightBalance.setLaws (HeightUpdates.wordAnnotation Nat) 1 (by decide)).insert
    7 HeightUpdates.wordBase word_base_set_valid x
  change (x ∈ Trees.setTree (Cached.erase
    (HeightBalance.insert HeightUpdates.maximumAnnotation 1 7 HeightUpdates.maximumBase)) ↔
    x = 7 ∨ x ∈ Trees.setTree (Cached.erase HeightUpdates.maximumBase)) at hm
  change (x ∈ Trees.setTree (Cached.erase
    (HeightBalance.insert (HeightUpdates.wordAnnotation Nat) 1 7 HeightUpdates.wordBase)) ↔
    x = 7 ∨ x ∈ Trees.setTree (Cached.erase HeightUpdates.wordBase)) at hw
  rw [HeightUpdates.same_height_maximum_insert.1] at hm
  rw [HeightUpdates.same_height_word_insert.1] at hw
  exact ⟨hm, hw⟩

theorem annotation_delete_set (x : Nat) :
    (x ∈ Trees.setTree (Cached.erase HeightUpdates.maximumBase) ↔
        x ≠ 7 ∧ x ∈ Trees.setTree (Cached.erase HeightUpdates.maximumWithSeven)) ∧
      (x ∈ Trees.setTree (Cached.erase HeightUpdates.wordBase) ↔
        x ≠ 7 ∧ x ∈ Trees.setTree (Cached.erase HeightUpdates.wordWithSeven)) := by
  have hm := (HeightBalance.setLaws HeightUpdates.maximumAnnotation 1 (by decide)).delete
    7 HeightUpdates.maximumWithSeven maximum_update_full_validity.1 x
  have hw := (HeightBalance.setLaws (HeightUpdates.wordAnnotation Nat) 1 (by decide)).delete
    7 HeightUpdates.wordWithSeven word_update_full_validity.1 x
  change (x ∈ Trees.setTree (Cached.erase
    (HeightBalance.delete HeightUpdates.maximumAnnotation 1 7 HeightUpdates.maximumWithSeven)) ↔
    x ≠ 7 ∧ x ∈ Trees.setTree (Cached.erase HeightUpdates.maximumWithSeven)) at hm
  change (x ∈ Trees.setTree (Cached.erase
    (HeightBalance.delete (HeightUpdates.wordAnnotation Nat) 1 7 HeightUpdates.wordWithSeven)) ↔
    x ≠ 7 ∧ x ∈ Trees.setTree (Cached.erase HeightUpdates.wordWithSeven)) at hw
  rw [HeightUpdates.same_height_maximum_delete.1] at hm
  rw [HeightUpdates.same_height_word_delete.1] at hw
  exact ⟨hm, hw⟩

theorem same_height_complete_summaries :
    HeightUpdates.maximumBase.height = 3 ∧ HeightUpdates.maximumWithSeven.height = 3 ∧
      Cached.read HeightUpdates.maximumAnnotation.empty HeightUpdates.maximumBase = (3, some 6) ∧
      Cached.read HeightUpdates.maximumAnnotation.empty HeightUpdates.maximumWithSeven = (3, some 7) ∧
      Cached.read (HeightUpdates.wordAnnotation Nat).empty HeightUpdates.wordBase =
        (3, [2, 4, 5, 6]) ∧
      Cached.read (HeightUpdates.wordAnnotation Nat).empty HeightUpdates.wordWithSeven =
        (3, [2, 4, 5, 6, 7]) :=
  HeightUpdates.same_height_insert_readers

theorem maximum_word_histories_agree (updates : List (Update Nat)) :
    payloads (execute (HeightBalance.deleteOps HeightUpdates.maximumAnnotation 1)
        updates HeightUpdates.maximumBase) =
      payloads (execute (HeightBalance.deleteOps (HeightUpdates.wordAnnotation Nat) 1)
        updates HeightUpdates.wordBase) ∧
      ∀ x, Search.OrderedMap.containsKey x
          (execute (HeightBalance.deleteOps HeightUpdates.maximumAnnotation 1)
            updates HeightUpdates.maximumBase) =
        Search.OrderedMap.containsKey x
          (execute (HeightBalance.deleteOps (HeightUpdates.wordAnnotation Nat) 1)
            updates HeightUpdates.wordBase) :=
  independent_representations HeightUpdates.maximumAnnotation (HeightUpdates.wordAnnotation Nat)
    1 1 (by decide) (by decide) updates HeightUpdates.maximumBase HeightUpdates.wordBase
    maximum_base_set_valid word_base_set_valid (by decide)

theorem stale_summary_set_agreement_is_insufficient :
    Trees.setTree (Cached.erase HeightUpdates.staleMaximumAfterInsert) =
        Trees.setTree (Cached.erase HeightUpdates.maximumWithSeven) ∧
      Trees.setTree (Cached.erase HeightUpdates.staleWordAfterInsert) =
        Trees.setTree (Cached.erase HeightUpdates.wordWithSeven) ∧
      ¬ HeightBalance.SetValid HeightUpdates.maximumAnnotation 1
        HeightUpdates.staleMaximumAfterInsert ∧
      ¬ HeightBalance.SetValid (HeightUpdates.wordAnnotation Nat) 1
        HeightUpdates.staleWordAfterInsert :=
  ⟨congrArg Trees.setTree HeightUpdates.stale_update_shapes_and_heights.2.2.1,
    congrArg Trees.setTree HeightUpdates.stale_update_shapes_and_heights.2.2.2.1,
    fun h => HeightUpdates.stale_maximum_insert_rejected h.1.2,
    fun h => HeightUpdates.stale_word_insert_rejected h.1.2⟩

/-! S08: a supplied algebra over PEmpty requires no fabricated payload or query. -/
theorem empty_independent_annotation_refinement
    (ann : HeightBalance.HeightAnnotation PEmpty.{u + 1} σ) (d : Nat) (hd : 1 ≤ d) :
    (HeightBalance.deleteOps ann d).empty =
        (.nil : BinaryTree (PEmpty.{u + 1} × σ)) ∧
      HeightBalance.SetValid ann d (HeightBalance.deleteOps ann d).empty ∧
      Refinement (HeightBalance.deleteOps ann d) Search.OrderedList.ops
        (fun t => Trees.inorder (Cached.erase t)) (HeightBalance.ValidD ann d)
        Search.OrderedList.Strict :=
  ⟨rfl, HeightBalance.setValid_nil ann d, HeightBalance.inorderRefinement ann d hd⟩

theorem empty_carrier_prefixes
    (ann : HeightBalance.HeightAnnotation PEmpty.{u + 1} σ) (d : Nat) (hd : 1 ≤ d)
    (updates : List (Update PEmpty.{u + 1})) (n : Nat) :
    HeightBalance.SetValid ann d
      (execute (HeightBalance.deleteOps ann d) (updates.take n) .nil) :=
  (HeightBalance.setLaws ann d hd).prefix_valid updates n (HeightBalance.setValid_nil ann d)

theorem ordinary_empty_carrier :
    (AVL.deleteOps : DeleteOps PEmpty.{u + 1}
      (BinaryTree (PEmpty.{u + 1} × Nat))).empty = .nil ∧
      AVL.SetValid (.nil : BinaryTree (PEmpty.{u + 1} × Nat)) ∧
      Refinement (AVL.deleteOps : DeleteOps PEmpty.{u + 1}
        (BinaryTree (PEmpty.{u + 1} × Nat))) Search.OrderedList.ops
        (fun t => Trees.inorder (Cached.erase t)) AVL.Valid Search.OrderedList.Strict :=
  ⟨rfl, AVL.setLaws.empty_valid, AVL.inorderRefinement⟩

end Examples.HeightSetRefinement

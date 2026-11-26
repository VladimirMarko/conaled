import Applications.Resources.SearchTreeWorkload
import Applications.Search.OrderedMap.DecodedKeysModels

/-!
# Measured search histories through supplied signed comparisons

The executable adapters take only a Boolean comparison. Existing measured
search and insertion execute that comparison in source order, and the common
`Resources.run` consumes their actual returned trees and optional results.
The observation is nonempty node visits and primitive comparison calls.

Decoding, injectivity and reflected order belong to the laws connecting these
operations to the ordered workload. Finite signed prefixes retain explicit
representability bounds. None of these observations measures allocation,
stack, generation, comparison internals or elapsed time.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.DecodedSearchTreeWorkload

universe u v
variable {κ : Type u} {ν : Type v}

open Search.OrderedMap (bindAll)
open Search.OrderedMap.DecodedKeys (mapKeys)
open Representations.SignedComparison

/-- One primitive charge accompanies the actual supplied Boolean answer. -/
def unitBoolRun (ltb : κ → κ → Bool) (a b : κ) : Measured Bool Nat :=
  (ltb a b, 1)

def lookupRun (ltb : κ → κ → Bool) (query : κ) (tree : BinaryTree (κ × ν)) :
    Measured (Option ν) (Nat × Nat) :=
  SearchTree.lookupWithRun (unitBoolRun ltb) query tree

def insertRun (ltb : κ → κ → Bool) (key : κ) (value : ν)
    (tree : BinaryTree (κ × ν)) : Measured (BinaryTree (κ × ν)) (Nat × Nat) :=
  SearchTree.insertWithRun (unitBoolRun ltb) key value tree

/-- Chronological writes use the existing observation-polymorphic executor. -/
def buildRun (ltb : κ → κ → Bool) (writes : List (κ × ν))
    (tree : BinaryTree (κ × ν)) : Measured (BinaryTree (κ × ν)) (Nat × Nat) :=
  Resources.run (fun binding tree => insertRun ltb binding.1 binding.2 tree) writes tree

def buildKeysRun (ltb : κ → κ → Bool) (keys : List κ) :
    Measured (BinaryTree (κ × Nat)) (Nat × Nat) :=
  buildRun ltb (Search.OrderedMap.Workload.sourceWrites keys) .nil

/-- The hit test observes the returned optional payload before adding one. -/
def queryStep (ltb : κ → κ → Bool) (tree : BinaryTree (κ × Nat))
    (query : κ) (count : Nat) : Measured Nat (Nat × Nat) :=
  bind (lookupRun ltb query tree) fun result =>
    pure (if result.getD 0 = 1 then count + 1 else count)

def queryRun (ltb : κ → κ → Bool) (queries : List κ)
    (tree : BinaryTree (κ × Nat)) : Measured Nat (Nat × Nat) :=
  Resources.run (queryStep ltb tree) queries 0

/-- Construction and the subsequent scan retain separate measured phases. -/
def sourceRun (ltb : κ → κ → Bool) (inserted queries : List κ) :
    Measured Nat (Nat × Nat) :=
  bind (buildKeysRun ltb inserted) (queryRun ltb queries)

@[simp] theorem lookupRun_empty (ltb : κ → κ → Bool) (query : κ) :
    lookupRun (ν := ν) ltb query .nil = (none, (0, 0)) := rfl

@[simp] theorem insertRun_empty (ltb : κ → κ → Bool) (key : κ) (value : ν) :
    insertRun ltb key value .nil = (.node (key, value) .nil .nil, (0, 0)) := rfl

/-- No reflection, equality decision or invariant is needed for erasure. -/
theorem lookupRun_value (ltb : κ → κ → Bool) (query : κ)
    (tree : BinaryTree (κ × ν)) :
    (lookupRun ltb query tree).1 = Search.OrderedMap.DecodedKeys.lookup? ltb query tree := by
  induction tree with
  | nil => rfl
  | node binding left right ihl ihr =>
      rw [lookupRun, SearchTree.lookupWithRun_node,
        Search.OrderedMap.DecodedKeys.lookup?_node]
      split
      · simp_all [unitBoolRun, lookupRun]
      · split <;> simp_all [unitBoolRun, lookupRun]

theorem lookupRun_default (ltb : κ → κ → Bool) (default : ν) (query : κ)
    (tree : BinaryTree (κ × ν)) :
    (lookupRun ltb query tree).1.getD default =
      Search.OrderedMap.DecodedKeys.lookup ltb default query tree :=
  congrArg (fun result => result.getD default) (lookupRun_value ltb query tree)

theorem lookupRun_bound (ltb : κ → κ → Bool) (query : κ)
    (tree : BinaryTree (κ × ν)) :
    (lookupRun ltb query tree).1.isSome = Search.OrderedMap.DecodedKeys.bound ltb query tree :=
  congrArg Option.isSome (lookupRun_value ltb query tree)

theorem insertRun_value (ltb : κ → κ → Bool) (key : κ) (value : ν)
    (tree : BinaryTree (κ × ν)) :
    (insertRun ltb key value tree).1 = Search.OrderedMap.DecodedKeys.insert ltb key value tree := by
  induction tree with
  | nil => rfl
  | node binding left right ihl ihr =>
      rw [insertRun, SearchTree.insertWithRun_node,
        Search.OrderedMap.DecodedKeys.insert_node]
      split
      · simp_all [unitBoolRun, insertRun]
      · split <;> simp_all [unitBoolRun, insertRun]

/-- The actual measured return erases to the existing raw Boolean operation record. -/
theorem buildRun_value (ltb : κ → κ → Bool) (writes : List (κ × ν))
    (tree : BinaryTree (κ × ν)) :
    (buildRun ltb writes tree).1 =
      bindAll (Search.OrderedMap.DecodedKeys.ops ltb) writes tree := by
  induction writes generalizing tree with
  | nil => rfl
  | cons binding rest ih =>
      change (buildRun ltb rest (insertRun ltb binding.1 binding.2 tree).1).1 = _
      rw [ih, insertRun_value]
      rfl

theorem buildKeysRun_value (ltb : κ → κ → Bool) (keys : List κ) :
    (buildKeysRun ltb keys).1 = bindAll (Search.OrderedMap.DecodedKeys.ops ltb)
      (Search.OrderedMap.Workload.sourceWrites keys) .nil :=
  buildRun_value ltb _ _

/-- Even without comparison laws, the scan counts its actual default-valued results. -/
theorem queryRun_value (ltb : κ → κ → Bool) (queries : List κ)
    (tree : BinaryTree (κ × Nat)) :
    (queryRun ltb queries tree).1 = queries.foldl
      (fun count query =>
        if Search.OrderedMap.DecodedKeys.lookup ltb 0 query tree = 1 then count + 1 else count) 0 := by
  rw [queryRun, Resources.run_state]
  congr 1
  funext count query
  simp only [queryStep, bind_value, pure, lookupRun_value, Search.OrderedMap.DecodedKeys.lookup]
  rfl

theorem sourceRun_value (ltb : κ → κ → Bool) (inserted queries : List κ) :
    (sourceRun ltb inserted queries).1 = queries.foldl
      (fun count query =>
        if Search.OrderedMap.DecodedKeys.lookup ltb 0 query
            (bindAll (Search.OrderedMap.DecodedKeys.ops ltb)
              (Search.OrderedMap.Workload.sourceWrites inserted) .nil) = 1
        then count + 1 else count) 0 := by
  rw [sourceRun, bind_value, queryRun_value, buildKeysRun_value]

theorem sourceRun_work (ltb : κ → κ → Bool) (inserted queries : List κ) :
    (sourceRun ltb inserted queries).2 = (buildKeysRun ltb inserted).2 +
      (queryRun ltb queries (buildKeysRun ltb inserted).1).2 := rfl

def encodedBuildRun (ltb : κ → κ → Bool) (encode : Nat → κ) (n : Nat) :
    Measured (BinaryTree (κ × Nat)) (Nat × Nat) :=
  buildKeysRun ltb (SearchTreeWorkload.encodedKeys encode n)

/-- The scan receives the actual measured build result. -/
def encodedQueryRun (ltb : κ → κ → Bool) (encode : Nat → κ) (n : Nat) :
    Measured Nat (Nat × Nat) :=
  queryRun ltb (SearchTreeWorkload.encodedKeys encode n) (encodedBuildRun ltb encode n).1

def encodedSourceRun (ltb : κ → κ → Bool) (encode : Nat → κ) (n : Nat) :
    Measured Nat (Nat × Nat) :=
  sourceRun ltb (SearchTreeWorkload.encodedKeys encode n) (SearchTreeWorkload.encodedKeys encode n)

section ReflectedOrder
variable (decode : κ → Int) (ltb : κ → κ → Bool)
variable (hinj : Function.Injective decode)
variable (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
include hinj hlt

/-- The exact supplied decision field, rather than a freshly inferred decision. -/
theorem unitBoolRun_eq_ordered :
    unitBoolRun ltb = fun a b =>
      (@decide (decode a < decode b)
        ((linearOrderOfStrict decode ltb hinj hlt).toDecidableLT a b), 1) := by
  funext a b
  exact Prod.ext (linearOrderOfStrict_decide_lt decode ltb hinj hlt a b).symm rfl

theorem lookupRun_eq_ordered (query : κ) (tree : BinaryTree (κ × ν)) :
    lookupRun ltb query tree =
      @SearchTree.lookupRun κ ν (linearOrderOfStrict decode ltb hinj hlt) query tree := by
  change SearchTree.lookupWithRun (unitBoolRun ltb) query tree =
    SearchTree.lookupWithRun
      (fun a b => (@decide (decode a < decode b)
        ((linearOrderOfStrict decode ltb hinj hlt).toDecidableLT a b), 1)) query tree
  rw [unitBoolRun_eq_ordered decode ltb hinj hlt]

theorem insertRun_eq_ordered (key : κ) (value : ν) (tree : BinaryTree (κ × ν)) :
    insertRun ltb key value tree =
      @SearchTree.insertRun κ ν (linearOrderOfStrict decode ltb hinj hlt) key value tree := by
  change SearchTree.insertWithRun (unitBoolRun ltb) key value tree =
    SearchTree.insertWithRun
      (fun a b => (@decide (decode a < decode b)
        ((linearOrderOfStrict decode ltb hinj hlt).toDecidableLT a b), 1)) key value tree
  rw [unitBoolRun_eq_ordered decode ltb hinj hlt]

theorem buildRun_eq_ordered (writes : List (κ × ν)) (tree : BinaryTree (κ × ν)) :
    buildRun ltb writes tree =
      @SearchTreeWorkload.buildRun κ ν (linearOrderOfStrict decode ltb hinj hlt) writes tree := by
  unfold buildRun SearchTreeWorkload.buildRun
  exact congrArg (fun step => Resources.run step writes tree)
    (funext fun binding => funext fun state =>
      insertRun_eq_ordered decode ltb hinj hlt binding.1 binding.2 state)

theorem buildKeysRun_eq_ordered (keys : List κ) :
    buildKeysRun ltb keys =
      @SearchTreeWorkload.buildKeysRun κ (linearOrderOfStrict decode ltb hinj hlt) keys :=
  buildRun_eq_ordered decode ltb hinj hlt _ _

theorem queryStep_eq_ordered (tree : BinaryTree (κ × Nat)) (query : κ) (count : Nat) :
    queryStep ltb tree query count =
      @SearchTreeWorkload.queryStep κ (linearOrderOfStrict decode ltb hinj hlt) tree query count := by
  unfold queryStep SearchTreeWorkload.queryStep
  rw [lookupRun_eq_ordered decode ltb hinj hlt]

theorem queryRun_eq_ordered (queries : List κ) (tree : BinaryTree (κ × Nat)) :
    queryRun ltb queries tree =
      @SearchTreeWorkload.queryRun κ (linearOrderOfStrict decode ltb hinj hlt) queries tree := by
  unfold queryRun SearchTreeWorkload.queryRun
  exact congrArg (fun step => Resources.run step queries 0)
    (funext fun query => funext fun count =>
      queryStep_eq_ordered decode ltb hinj hlt tree query count)

theorem sourceRun_eq_ordered (inserted queries : List κ) :
    sourceRun ltb inserted queries =
      @SearchTreeWorkload.sourceRun κ (linearOrderOfStrict decode ltb hinj hlt) inserted queries := by
  unfold sourceRun SearchTreeWorkload.sourceRun
  rw [buildKeysRun_eq_ordered decode ltb hinj hlt]
  exact congrArg
    (bind (@SearchTreeWorkload.buildKeysRun κ (linearOrderOfStrict decode ltb hinj hlt) inserted))
    (funext fun tree => queryRun_eq_ordered decode ltb hinj hlt queries tree)

/-- The checker uses only membership in the original insertion list. -/
theorem sourceRun_independent_count (inserted queries : List κ) :
    letI := linearOrderOfStrict decode ltb hinj hlt
    (sourceRun ltb inserted queries).1 = Search.OrderedMap.Workload.expectedHits inserted queries := by
  let _ : LinearOrder κ := linearOrderOfStrict decode ltb hinj hlt
  rw [sourceRun_eq_ordered decode ltb hinj hlt]
  exact SearchTreeWorkload.sourceRun_independent_count inserted queries

theorem encodedBuildRun_eq_ordered (encode : Nat → κ) (n : Nat) :
    encodedBuildRun ltb encode n =
      @SearchTreeWorkload.encodedBuildRun κ (linearOrderOfStrict decode ltb hinj hlt) encode n :=
  buildKeysRun_eq_ordered decode ltb hinj hlt _

theorem encodedQueryRun_eq_ordered (encode : Nat → κ) (n : Nat) :
    encodedQueryRun ltb encode n =
      @SearchTreeWorkload.encodedQueryRun κ (linearOrderOfStrict decode ltb hinj hlt) encode n := by
  let _ : LinearOrder κ := linearOrderOfStrict decode ltb hinj hlt
  unfold encodedQueryRun
  rw [queryRun_eq_ordered decode ltb hinj hlt, encodedBuildRun_eq_ordered decode ltb hinj hlt,
    SearchTreeWorkload.encodedBuildRun, SearchTreeWorkload.buildKeysRun_value]
  rfl

/-- Decode the actual returned tree and retain its entire observation pair. -/
theorem encodedBuildRun_transport (encode : Nat → κ) (n : Nat)
    (representable : ∀ k, k < n → decode (encode k) = (k : Int)) :
    (mapKeys decode (encodedBuildRun ltb encode n).1, (encodedBuildRun ltb encode n).2) =
      (mapKeys (fun k : Nat => (k : Int)) (SearchTree.rightSpine 1 0 n),
        (SearchTreeWorkload.consecutiveBuildRun n).2) := by
  let _ : LinearOrder κ := linearOrderOfStrict decode ltb hinj hlt
  simpa only [encodedBuildRun_eq_ordered decode ltb hinj hlt] using
    SearchTreeWorkload.encodedBuildRun_transport decode (fun _ _ => Iff.rfl) encode n representable

theorem encodedBuildRun_counts (encode : Nat → κ) (n : Nat)
    (representable : ∀ k, k < n → decode (encode k) = (k : Int)) :
    2 * (encodedBuildRun ltb encode n).2.1 = n * (n - 1) ∧
      (encodedBuildRun ltb encode n).2.2 = n * (n - 1) := by
  have work := congrArg Prod.snd (encodedBuildRun_transport decode ltb hinj hlt encode n representable)
  change (encodedBuildRun ltb encode n).2 = (SearchTreeWorkload.consecutiveBuildRun n).2 at work
  rw [work]
  exact ⟨SearchTreeWorkload.consecutiveBuildRun_double_visits n,
    SearchTreeWorkload.consecutiveBuildRun_comparisons n⟩

theorem encodedQueryRun_transport (encode : Nat → κ) (n : Nat)
    (representable : ∀ k, k < n → decode (encode k) = (k : Int)) :
    encodedQueryRun ltb encode n = SearchTreeWorkload.consecutiveQueryRun n := by
  let _ : LinearOrder κ := linearOrderOfStrict decode ltb hinj hlt
  rw [encodedQueryRun_eq_ordered decode ltb hinj hlt]
  exact SearchTreeWorkload.encodedQueryRun_transport decode (fun _ _ => Iff.rfl) encode n representable

theorem encodedQueryRun_counts (encode : Nat → κ) (n : Nat)
    (representable : ∀ k, k < n → decode (encode k) = (k : Int)) :
    (encodedQueryRun ltb encode n).1 = n ∧
      2 * (encodedQueryRun ltb encode n).2.1 = n * (n + 1) ∧
      (encodedQueryRun ltb encode n).2.2 = n * (n + 1) := by
  rw [encodedQueryRun_transport decode ltb hinj hlt encode n representable]
  exact ⟨SearchTreeWorkload.consecutiveQueryRun_value n,
    SearchTreeWorkload.consecutiveQueryRun_double_visits n,
    SearchTreeWorkload.consecutiveQueryRun_comparisons n⟩

theorem encoded_successful_query (encode : Nat → κ) (n : Nat)
    (representable : ∀ k, k < n → decode (encode k) = (k : Int))
    (k : Nat) (inside : k < n) :
    lookupRun ltb (encode k) (encodedBuildRun ltb encode n).1 =
      (some 1, (k + 1, 2 * (k + 1))) := by
  let _ : LinearOrder κ := linearOrderOfStrict decode ltb hinj hlt
  rw [lookupRun_eq_ordered decode ltb hinj hlt, encodedBuildRun_eq_ordered decode ltb hinj hlt,
    SearchTreeWorkload.encodedBuildRun, SearchTreeWorkload.buildKeysRun_value]
  exact SearchTreeWorkload.encoded_successful_query decode (fun _ _ => Iff.rfl)
    encode n representable k inside

/-- Representing the first absent upper key is separate from representing the prefix. -/
theorem encoded_upper_missing_query (encode : Nat → κ) (n : Nat)
    (representable : ∀ k, k < n → decode (encode k) = (k : Int))
    (query_representable : decode (encode n) = (n : Int)) :
    lookupRun ltb (encode n) (encodedBuildRun ltb encode n).1 = (none, (n, 2 * n)) := by
  let _ : LinearOrder κ := linearOrderOfStrict decode ltb hinj hlt
  rw [lookupRun_eq_ordered decode ltb hinj hlt, encodedBuildRun_eq_ordered decode ltb hinj hlt,
    SearchTreeWorkload.encodedBuildRun, SearchTreeWorkload.buildKeysRun_value]
  exact SearchTreeWorkload.encoded_upper_missing_query decode (fun _ _ => Iff.rfl)
    encode n representable query_representable

theorem encoded_last_query (encode : Nat → κ) (n : Nat)
    (representable : ∀ k, k < n → decode (encode k) = (k : Int)) (positive : 0 < n) :
    lookupRun ltb (encode (n - 1)) (encodedBuildRun ltb encode n).1 =
      (some 1, (n, 2 * n)) := by
  let _ : LinearOrder κ := linearOrderOfStrict decode ltb hinj hlt
  rw [lookupRun_eq_ordered decode ltb hinj hlt, encodedBuildRun_eq_ordered decode ltb hinj hlt,
    SearchTreeWorkload.encodedBuildRun, SearchTreeWorkload.buildKeysRun_value]
  exact SearchTreeWorkload.encoded_last_query decode (fun _ _ => Iff.rfl)
    encode n representable positive

theorem encodedSourceRun_exact (encode : Nat → κ) (n : Nat)
    (representable : ∀ k, k < n → decode (encode k) = (k : Int)) :
    encodedSourceRun ltb encode n = (n, (n * n, 2 * (n * n))) := by
  let _ : LinearOrder κ := linearOrderOfStrict decode ltb hinj hlt
  rw [encodedSourceRun, sourceRun_eq_ordered decode ltb hinj hlt]
  exact SearchTreeWorkload.sourceRun_encodedKeys_exact decode (fun _ _ => Iff.rfl)
    encode n representable

theorem encoded_source_schedule (encode : Nat → κ) (n : Nat)
    (representable : ∀ k, k < n → decode (encode k) = (k : Int)) :
    sourceRun ltb ((Search.OrderedMap.Workload.sourceIndices n).map (fun j => encode (n - j)))
      ((Search.OrderedMap.Workload.sourceIndices n).map (fun j => encode (n - j))) =
      (n, (n * n, 2 * (n * n))) := by
  have schedule : (Search.OrderedMap.Workload.sourceIndices n).map (fun j => encode (n - j)) =
      SearchTreeWorkload.encodedKeys encode n := by
    simpa only [List.map_map, Function.comp_def, SearchTreeWorkload.encodedKeys] using
      congrArg (List.map encode) (Search.OrderedMap.Workload.sourceIndices_consecutive n)
  rw [schedule]
  exact encodedSourceRun_exact decode ltb hinj hlt encode n representable

end ReflectedOrder

/-- Width zero remains a singleton-key case, independent of conversion bounds. -/
theorem zero_width_lookup_after_insert (key query : BitVec 0) (value : ν)
    (tree : BinaryTree (BitVec 0 × ν)) :
    lookupRun wordLtb query (insertRun wordLtb key value tree).1 = (some value, (1, 2)) := by
  have comparisons : ∀ a b : BitVec 0, wordLtb a b = false :=
    fun a b => (word_zero_width_comparisons a b).1
  cases tree <;> simp [lookupRun, insertRun, SearchTree.lookupWithRun,
    SearchTree.insertWithRun, unitBoolRun, comparisons, bind, reweight]

def wordKeys (w n : Nat) : List (BitVec w) :=
  SearchTreeWorkload.encodedKeys (BitVec.ofNat w) n

def wordBuildRun (w n : Nat) : Measured (BinaryTree (BitVec w × Nat)) (Nat × Nat) :=
  encodedBuildRun wordLtb (BitVec.ofNat w) n

def wordQueryRun (w n : Nat) : Measured Nat (Nat × Nat) :=
  encodedQueryRun wordLtb (BitVec.ofNat w) n

def wordSourceRun (w n : Nat) : Measured Nat (Nat × Nat) :=
  encodedSourceRun wordLtb (BitVec.ofNat w) n

/-- The largest encoded key is n-1, so the prefix bound is non-strict. -/
theorem word_prefix_representable (w n : Nat) (positive_width : 0 < w)
    (bound : n ≤ 2 ^ (w - 1)) :
    ∀ k, k < n → (BitVec.ofNat w k).toInt = (k : Int) :=
  fun k inside => word_ofNat_toInt positive_width k (lt_of_lt_of_le inside bound)

/-- Distinct encoded keys follow from prefix decoding, not an assumed infinite word family. -/
theorem wordKeys_nodup (w n : Nat) (positive_width : 0 < w)
    (bound : n ≤ 2 ^ (w - 1)) : (wordKeys w n).Nodup :=
  SearchTreeWorkload.encodedKeys_nodup BitVec.toInt (BitVec.ofNat w) n
    (word_prefix_representable w n positive_width bound)

theorem wordBuildRun_transport (w n : Nat) (positive_width : 0 < w)
    (bound : n ≤ 2 ^ (w - 1)) :
    (mapKeys BitVec.toInt (wordBuildRun w n).1, (wordBuildRun w n).2) =
      (mapKeys (fun k : Nat => (k : Int)) (SearchTree.rightSpine 1 0 n),
        (SearchTreeWorkload.consecutiveBuildRun n).2) :=
  encodedBuildRun_transport BitVec.toInt wordLtb (word_decode_injective w) wordLtb_true_iff
    (BitVec.ofNat w) n (word_prefix_representable w n positive_width bound)

theorem wordBuildRun_counts (w n : Nat) (positive_width : 0 < w)
    (bound : n ≤ 2 ^ (w - 1)) :
    2 * (wordBuildRun w n).2.1 = n * (n - 1) ∧
      (wordBuildRun w n).2.2 = n * (n - 1) :=
  encodedBuildRun_counts BitVec.toInt wordLtb (word_decode_injective w) wordLtb_true_iff
    (BitVec.ofNat w) n (word_prefix_representable w n positive_width bound)

theorem wordQueryRun_counts (w n : Nat) (positive_width : 0 < w)
    (bound : n ≤ 2 ^ (w - 1)) :
    (wordQueryRun w n).1 = n ∧
      2 * (wordQueryRun w n).2.1 = n * (n + 1) ∧
      (wordQueryRun w n).2.2 = n * (n + 1) :=
  encodedQueryRun_counts BitVec.toInt wordLtb (word_decode_injective w) wordLtb_true_iff
    (BitVec.ofNat w) n (word_prefix_representable w n positive_width bound)

theorem wordSourceRun_exact (w n : Nat) (positive_width : 0 < w)
    (bound : n ≤ 2 ^ (w - 1)) :
    wordSourceRun w n = (n, (n * n, 2 * (n * n))) :=
  encodedSourceRun_exact BitVec.toInt wordLtb (word_decode_injective w) wordLtb_true_iff
    (BitVec.ofNat w) n (word_prefix_representable w n positive_width bound)

theorem word_successful_query (w n : Nat) (positive_width : 0 < w)
    (bound : n ≤ 2 ^ (w - 1)) (k : Nat) (inside : k < n) :
    lookupRun wordLtb (BitVec.ofNat w k) (wordBuildRun w n).1 =
      (some 1, (k + 1, 2 * (k + 1))) :=
  encoded_successful_query BitVec.toInt wordLtb (word_decode_injective w) wordLtb_true_iff
    (BitVec.ofNat w) n (word_prefix_representable w n positive_width bound) k inside

/-- The absent query n itself must fit, making this bound strictly stronger. -/
theorem word_upper_missing_query (w n : Nat) (positive_width : 0 < w)
    (bound : n < 2 ^ (w - 1)) :
    lookupRun wordLtb (BitVec.ofNat w n) (wordBuildRun w n).1 = (none, (n, 2 * n)) :=
  encoded_upper_missing_query BitVec.toInt wordLtb (word_decode_injective w) wordLtb_true_iff
    (BitVec.ofNat w) n (word_prefix_representable w n positive_width (le_of_lt bound))
    (word_ofNat_toInt positive_width n bound)

/-- The last successful query still witnesses the full path at the prefix endpoint. -/
theorem word_last_query (w n : Nat) (positive_width : 0 < w)
    (bound : n ≤ 2 ^ (w - 1)) (positive : 0 < n) :
    lookupRun wordLtb (BitVec.ofNat w (n - 1)) (wordBuildRun w n).1 =
      (some 1, (n, 2 * n)) :=
  encoded_last_query BitVec.toInt wordLtb (word_decode_injective w) wordLtb_true_iff
    (BitVec.ofNat w) n (word_prefix_representable w n positive_width bound) positive

theorem word_source_schedule (w n : Nat) (positive_width : 0 < w)
    (bound : n ≤ 2 ^ (w - 1)) :
    sourceRun wordLtb
      ((Search.OrderedMap.Workload.sourceIndices n).map (fun j => BitVec.ofNat w (n - j)))
      ((Search.OrderedMap.Workload.sourceIndices n).map (fun j => BitVec.ofNat w (n - j))) =
      (n, (n * n, 2 * (n * n))) :=
  encoded_source_schedule BitVec.toInt wordLtb (word_decode_injective w) wordLtb_true_iff
    (BitVec.ofNat w) n (word_prefix_representable w n positive_width bound)

theorem wordBuildRun_63_transport (n : Nat) (bound : n ≤ 2 ^ 62) :
    (mapKeys BitVec.toInt (wordBuildRun 63 n).1, (wordBuildRun 63 n).2) =
      (mapKeys (fun k : Nat => (k : Int)) (SearchTree.rightSpine 1 0 n),
        (SearchTreeWorkload.consecutiveBuildRun n).2) :=
  wordBuildRun_transport 63 n (by decide) bound

theorem wordBuildRun_63_counts (n : Nat) (bound : n ≤ 2 ^ 62) :
    2 * (wordBuildRun 63 n).2.1 = n * (n - 1) ∧
      (wordBuildRun 63 n).2.2 = n * (n - 1) :=
  wordBuildRun_counts 63 n (by decide) bound

theorem wordQueryRun_63_counts (n : Nat) (bound : n ≤ 2 ^ 62) :
    (wordQueryRun 63 n).1 = n ∧
      2 * (wordQueryRun 63 n).2.1 = n * (n + 1) ∧
      (wordQueryRun 63 n).2.2 = n * (n + 1) :=
  wordQueryRun_counts 63 n (by decide) bound

theorem wordSourceRun_63_exact (n : Nat) (bound : n ≤ 2 ^ 62) :
    wordSourceRun 63 n = (n, (n * n, 2 * (n * n))) :=
  wordSourceRun_exact 63 n (by decide) bound

def int64Keys (n : Nat) : List Int64 :=
  SearchTreeWorkload.encodedKeys (fun k : Nat => Int64.ofInt (k : Int)) n

def int64BuildRun (n : Nat) : Measured (BinaryTree (Int64 × Nat)) (Nat × Nat) :=
  encodedBuildRun int64Ltb (fun k : Nat => Int64.ofInt (k : Int)) n

def int64QueryRun (n : Nat) : Measured Nat (Nat × Nat) :=
  encodedQueryRun int64Ltb (fun k : Nat => Int64.ofInt (k : Int)) n

def int64SourceRun (n : Nat) : Measured Nat (Nat × Nat) :=
  encodedSourceRun int64Ltb (fun k : Nat => Int64.ofInt (k : Int)) n

theorem int64_prefix_representable (n : Nat) (bound : n ≤ 2 ^ 63) :
    ∀ k, k < n → (Int64.ofInt (k : Int)).toInt = (k : Int) :=
  fun k inside => int64_ofNat_toInt k (lt_of_lt_of_le inside bound)

theorem int64Keys_nodup (n : Nat) (bound : n ≤ 2 ^ 63) : (int64Keys n).Nodup :=
  SearchTreeWorkload.encodedKeys_nodup Int64.toInt (fun k : Nat => Int64.ofInt (k : Int)) n
    (int64_prefix_representable n bound)

theorem int64BuildRun_transport (n : Nat) (bound : n ≤ 2 ^ 63) :
    (mapKeys Int64.toInt (int64BuildRun n).1, (int64BuildRun n).2) =
      (mapKeys (fun k : Nat => (k : Int)) (SearchTree.rightSpine 1 0 n),
        (SearchTreeWorkload.consecutiveBuildRun n).2) :=
  encodedBuildRun_transport Int64.toInt int64Ltb int64_decode_injective int64Ltb_true_iff
    (fun k : Nat => Int64.ofInt (k : Int)) n (int64_prefix_representable n bound)

theorem int64BuildRun_counts (n : Nat) (bound : n ≤ 2 ^ 63) :
    2 * (int64BuildRun n).2.1 = n * (n - 1) ∧
      (int64BuildRun n).2.2 = n * (n - 1) :=
  encodedBuildRun_counts Int64.toInt int64Ltb int64_decode_injective int64Ltb_true_iff
    (fun k : Nat => Int64.ofInt (k : Int)) n (int64_prefix_representable n bound)

theorem int64QueryRun_counts (n : Nat) (bound : n ≤ 2 ^ 63) :
    (int64QueryRun n).1 = n ∧
      2 * (int64QueryRun n).2.1 = n * (n + 1) ∧
      (int64QueryRun n).2.2 = n * (n + 1) :=
  encodedQueryRun_counts Int64.toInt int64Ltb int64_decode_injective int64Ltb_true_iff
    (fun k : Nat => Int64.ofInt (k : Int)) n (int64_prefix_representable n bound)

theorem int64SourceRun_exact (n : Nat) (bound : n ≤ 2 ^ 63) :
    int64SourceRun n = (n, (n * n, 2 * (n * n))) :=
  encodedSourceRun_exact Int64.toInt int64Ltb int64_decode_injective int64Ltb_true_iff
    (fun k : Nat => Int64.ofInt (k : Int)) n (int64_prefix_representable n bound)

theorem int64_successful_query (n : Nat) (bound : n ≤ 2 ^ 63) (k : Nat) (inside : k < n) :
    lookupRun int64Ltb (Int64.ofInt (k : Int)) (int64BuildRun n).1 =
      (some 1, (k + 1, 2 * (k + 1))) :=
  encoded_successful_query Int64.toInt int64Ltb int64_decode_injective int64Ltb_true_iff
    (fun k : Nat => Int64.ofInt (k : Int)) n (int64_prefix_representable n bound) k inside

theorem int64_upper_missing_query (n : Nat) (bound : n < 2 ^ 63) :
    lookupRun int64Ltb (Int64.ofInt (n : Int)) (int64BuildRun n).1 = (none, (n, 2 * n)) :=
  encoded_upper_missing_query Int64.toInt int64Ltb int64_decode_injective int64Ltb_true_iff
    (fun k : Nat => Int64.ofInt (k : Int)) n (int64_prefix_representable n (le_of_lt bound))
    (int64_ofNat_toInt n bound)

theorem int64_last_query (n : Nat) (bound : n ≤ 2 ^ 63) (positive : 0 < n) :
    lookupRun int64Ltb (Int64.ofInt ((n - 1 : Nat) : Int)) (int64BuildRun n).1 =
      (some 1, (n, 2 * n)) :=
  encoded_last_query Int64.toInt int64Ltb int64_decode_injective int64Ltb_true_iff
    (fun k : Nat => Int64.ofInt (k : Int)) n (int64_prefix_representable n bound) positive

theorem int64_source_schedule (n : Nat) (bound : n ≤ 2 ^ 63) :
    sourceRun int64Ltb
      ((Search.OrderedMap.Workload.sourceIndices n).map (fun j => Int64.ofInt ((n - j : Nat) : Int)))
      ((Search.OrderedMap.Workload.sourceIndices n).map (fun j => Int64.ofInt ((n - j : Nat) : Int))) =
      (n, (n * n, 2 * (n * n))) :=
  encoded_source_schedule Int64.toInt int64Ltb int64_decode_injective int64Ltb_true_iff
    (fun k : Nat => Int64.ofInt (k : Int)) n (int64_prefix_representable n bound)

end Resources.DecodedSearchTreeWorkload

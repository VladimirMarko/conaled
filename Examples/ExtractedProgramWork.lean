import Applications.Resources.SearchTreeWorkload
import Applications.Resources.DecodedSearchTreeWorkload
import Applications.Resources.UnaryComparison
import Examples.ExtractedTrees

/-!
# Values and abstract work of the extracted tree workload

These clients observe the actual completed measured build, query results and
the pair `(nonempty visits, strict-comparator calls)`. Construction and query
work remain separate; their sum is not the companion program's query timer.
The independent finite write model, decoded traversal and actual returned
trees connect the resource statements to the accepted source interfaces.

Nil inspection, key generation, counter arithmetic, allocation, stack and
clock time are outside this pair. Executable timing is a separate obligation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.ExtractedProgramWork

universe u v
variable {κ : Type u} {ν : Type v}
open Resources
open Resources.SearchTree
open Resources.SearchTreeWorkload
open Search.OrderedMap
open Representations.SignedComparison

/-- The optional results come from the tree returned by the measured build;
the expected results come from the independently reversed write history. -/
theorem measured_history_queries [LinearOrder κ] (writes : List (κ × ν))
    (queries : List κ) :
    queries.map (fun query => (lookupRun query (buildRun writes .nil).1).1) =
      queries.map (Workload.model writes) := by
  simp only [lookupRun_value, buildRun_value]
  change queries.map (fun query => lookup query (Workload.build writes)) = _
  simp only [Workload.build_lookup]

/-- Arbitrary-suffix enumeration and the actual measured count pair commute
with decoding the executed write history. No payload observation is changed. -/
theorem measured_decoded_history [LinearOrder κ] (decode : κ → Int)
    (compatible : ∀ a b, a < b ↔ decode a < decode b)
    (writes : List (κ × ν)) (tree : BinaryTree (κ × ν)) (suffix : List (κ × ν)) :
    ((DecodedKeys.elementsAux (buildRun writes tree).1 suffix).map
        (fun binding => (decode binding.1, binding.2)), (buildRun writes tree).2) =
      (DecodedKeys.elementsAux
        (buildRun (writes.map (fun binding => (decode binding.1, binding.2)))
          (DecodedKeys.mapKeys decode tree)).1
        (suffix.map (fun binding => (decode binding.1, binding.2))),
        (buildRun (writes.map (fun binding => (decode binding.1, binding.2)))
          (DecodedKeys.mapKeys decode tree)).2) := by
  have transport := buildRun_mapKeys decode compatible writes tree
  apply Prod.ext
  · change (DecodedKeys.elementsAux (buildRun writes tree).1 suffix).map
      (fun binding => (decode binding.1, binding.2)) = _
    rw [DecodedKeys.map_elementsAux]
    exact congrArg (fun result => DecodedKeys.elementsAux result
      (suffix.map (fun binding => (decode binding.1, binding.2))))
      (congrArg Prod.fst transport)
  · exact congrArg
      (fun result : BinaryTree (Int × ν) × (Nat × Nat) => result.2) transport

theorem empty_workload : sourceRun ([] : List Nat) [] = (0, (0, 0)) := rfl

theorem empty_with_queries : sourceRun ([] : List Nat) [0, 0, 7] = (0, (0, 0)) := by
  decide

theorem singleton_workload : sourceRun ([0] : List Nat) [0] = (1, (1, 2)) := by
  simpa using sourceRun_consecutive 1

theorem consecutive_four_build :
    (consecutiveBuildRun 4).1 = rightSpine 1 0 4 ∧
      (consecutiveBuildRun 4).2 = (6, 12) := by
  constructor
  · exact consecutiveBuildRun_value 4
  · have visits := consecutiveBuildRun_double_visits 4
    have comparisons := consecutiveBuildRun_comparisons 4
    apply Prod.ext <;> omega

theorem consecutive_four_query : consecutiveQueryRun 4 = (4, (10, 20)) := by
  have result := consecutiveQueryRun_value 4
  have visits := consecutiveQueryRun_double_visits 4
  have comparisons := consecutiveQueryRun_comparisons 4
  apply Prod.ext
  · exact result
  · apply Prod.ext
    · change (consecutiveQueryRun 4).2.1 = 10
      omega
    · change (consecutiveQueryRun 4).2.2 = 20
      exact comparisons

theorem consecutive_four_total :
    sourceRun (List.range 4) (List.range 4) = (4, (16, 32)) := by
  simpa using sourceRun_consecutive 4

theorem consecutive_four_found :
    lookupRun 2 (consecutiveBuildRun 4).1 = (some 1, (3, 6)) := by
  rw [consecutiveBuildRun_value]
  simpa using lookupRun_rightSpine_present 1 0 4 2 (by decide)

theorem consecutive_four_missing :
    lookupRun 4 (Workload.buildKeys (List.range 4)) = (none, (4, 8)) := by
  simpa using upper_missing_consecutive_query 4

theorem consecutive_last_path (n : Nat) (positive : 0 < n) :
    lookupRun (n - 1) (Workload.buildKeys (List.range n)) = (some 1, (n, 2 * n)) :=
  last_consecutive_query n positive

/-- Duplicate writes replace a binding, duplicate queries count separately,
and keys 2 and 7 miss. The build and query still execute their actual paths. -/
theorem duplicate_and_missing_workload :
    sourceRun ([3, 1, 3] : List Nat) [3, 2, 1, 3, 7] = (3, (9, 15)) := by
  apply Prod.ext
  · rw [sourceRun_independent_count]
    decide
  · decide

theorem signed_workload :
    sourceRun ([-3, 0, 4, -3] : List Int) [-3, -1, 4, 0, 4] = (4, (15, 29)) := by
  apply Prod.ext
  · rw [sourceRun_independent_count]
    decide
  · decide

/-- The same measured tree distinguishes stored zero from absence before a
caller chooses default zero. The source hit test intentionally counts neither. -/
theorem measured_stored_default :
    let tree := (buildRun ([(2, 5), (2, 0)] : List (Int × Nat)) .nil).1
    (lookupRun 2 tree).1 = some 0 ∧ (lookupRun 4 tree).1 = none ∧
      (lookupRun 2 tree).1.getD 0 = (lookupRun 4 tree).1.getD 0 ∧
      (queryRun [2, 4] tree).1 = 0 := by
  decide

/-- Measured insertion can return types themselves as payloads. Only the
actual value projection is observed, without payload equality or order. -/
theorem measured_type_payload (first last : Type v) :
    (lookupRun (2 : Int) (buildRun [(2, first), (2, last)] .nil).1).1 = some last := by
  rw [lookupRun_value, buildRun_value]
  change lookup (2 : Int) (Workload.build [(2, first), (2, last)]) = some last
  rw [Workload.build_lookup]
  rfl

theorem measured_malformed_miss :
    let tree : BinaryTree (Int × Nat) := .node (0, 0) (.node (1, 7) .nil .nil) .nil
    lookupRun 1 tree = (none, (1, 2)) ∧ (1, 7) ∈ DecodedKeys.elements tree := by
  decide

/-- This connects the measured family to the source's descending loop order,
not just to a convenient independently generated list. -/
theorem source_schedule_work (n : Nat) :
    sourceRun ((Workload.sourceIndices n).map (fun j => n - j))
      ((Workload.sourceIndices n).map (fun j => n - j)) =
      (n, (n * n, 2 * (n * n))) := sourceRun_schedule n

/-- All three source observations erase on arbitrary raw trees and arbitrary
Boolean comparisons. No ordering law is being inferred from this equation. -/
theorem measured_boolean_observations (ltb : κ → κ → Bool) (default : ν)
    (query : κ) (tree : BinaryTree (κ × ν)) :
    (DecodedSearchTreeWorkload.lookupRun ltb query tree).1 =
        DecodedKeys.lookup? ltb query tree ∧
      (DecodedSearchTreeWorkload.lookupRun ltb query tree).1.getD default =
        DecodedKeys.lookup ltb default query tree ∧
      (DecodedSearchTreeWorkload.lookupRun ltb query tree).1.isSome =
        DecodedKeys.bound ltb query tree :=
  ⟨DecodedSearchTreeWorkload.lookupRun_value ltb query tree,
    DecodedSearchTreeWorkload.lookupRun_default ltb default query tree,
    DecodedSearchTreeWorkload.lookupRun_bound ltb query tree⟩

theorem measured_boolean_history (ltb : κ → κ → Bool) (writes : List (κ × ν))
    (queries : List κ) :
    queries.map (fun query =>
      (DecodedSearchTreeWorkload.lookupRun ltb query
        (DecodedSearchTreeWorkload.buildRun ltb writes .nil).1).1) =
      queries.map (fun query =>
        DecodedKeys.lookup? ltb query (bindAll (DecodedKeys.ops ltb) writes .nil)) := by
  simp only [DecodedSearchTreeWorkload.lookupRun_value,
    DecodedSearchTreeWorkload.buildRun_value]

/-- The Boolean execution, decoded enumeration and whole observation pair
share the same returned build, including an arbitrary starting tree and suffix. -/
theorem measured_boolean_decoded_history (decode : κ → Int) (ltb : κ → κ → Bool)
    (hinj : Function.Injective decode)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
    (writes : List (κ × ν)) (tree : BinaryTree (κ × ν)) (suffix : List (κ × ν)) :
    ((DecodedKeys.elementsAux (DecodedSearchTreeWorkload.buildRun ltb writes tree).1 suffix).map
        (fun binding => (decode binding.1, binding.2)),
        (DecodedSearchTreeWorkload.buildRun ltb writes tree).2) =
      (DecodedKeys.elementsAux
        (buildRun (writes.map (fun binding => (decode binding.1, binding.2)))
          (DecodedKeys.mapKeys decode tree)).1
        (suffix.map (fun binding => (decode binding.1, binding.2))),
        (buildRun (writes.map (fun binding => (decode binding.1, binding.2)))
          (DecodedKeys.mapKeys decode tree)).2) := by
  let _ : LinearOrder κ := linearOrderOfStrict decode ltb hinj hlt
  rw [DecodedSearchTreeWorkload.buildRun_eq_ordered decode ltb hinj hlt]
  exact measured_decoded_history decode (fun _ _ => Iff.rfl) writes tree suffix

/-- Type-valued payloads also pass through the actual Boolean measured insert.
Irreflexivity suffices for this same-key raw-tree law. -/
theorem measured_boolean_type_payload (ltb : κ → κ → Bool)
    (irrefl : ∀ key, ltb key key = false) (key : κ) (value : Type v)
    (tree : BinaryTree (κ × Type v)) :
    (DecodedSearchTreeWorkload.lookupRun ltb key
      (DecodedSearchTreeWorkload.insertRun ltb key value tree).1).1 = some value := by
  rw [DecodedSearchTreeWorkload.lookupRun_value, DecodedSearchTreeWorkload.insertRun_value]
  exact DecodedKeys.lookup?_insert_self_of_irrefl ltb irrefl key value tree

theorem measured_boolean_signed_workload :
    DecodedSearchTreeWorkload.sourceRun intLtb
      [-3, 0, 4, -3] [-3, -1, 4, 0, 4] = (4, (15, 29)) := by
  apply Prod.ext
  · rw [DecodedSearchTreeWorkload.sourceRun_independent_count id intLtb
      int_decode_injective intLtb_true_iff]
    decide
  · decide

/-- Erasure alone cannot supply membership correctness for an unlawful
comparison. Even the stored key misses when every comparison answers true. -/
theorem unlawful_boolean_counterexample :
    DecodedSearchTreeWorkload.sourceRun (fun _ _ : Int => true) [1] [1] =
        (0, (1, 1)) ∧ Workload.expectedHits ([1] : List Int) [1] = 1 := by
  decide

/-- The full nonnegative four-bit prefix still has a valid successful last
query. Separate phase counts are retained alongside the combined observation. -/
theorem four_bit_full_prefix :
    (DecodedSearchTreeWorkload.wordBuildRun 4 8).2 = (28, 56) ∧
      DecodedSearchTreeWorkload.wordQueryRun 4 8 = (8, (36, 72)) ∧
      DecodedSearchTreeWorkload.wordSourceRun 4 8 = (8, (64, 128)) ∧
      DecodedSearchTreeWorkload.lookupRun wordLtb (BitVec.ofNat 4 7)
        (DecodedSearchTreeWorkload.wordBuildRun 4 8).1 = (some 1, (8, 16)) := by
  have build := DecodedSearchTreeWorkload.wordBuildRun_counts 4 8 (by decide) (by decide)
  have query := DecodedSearchTreeWorkload.wordQueryRun_counts 4 8 (by decide) (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Prod.ext <;> omega
  · apply Prod.ext
    · exact query.1
    · apply Prod.ext
      · change (DecodedSearchTreeWorkload.wordQueryRun 4 8).2.1 = 36
        omega
      · exact query.2.2
  · simpa using DecodedSearchTreeWorkload.wordSourceRun_exact 4 8 (by decide) (by decide)
  · simpa using DecodedSearchTreeWorkload.word_last_query 4 8
      (by decide) (by decide) (by decide)

theorem four_bit_represented_missing :
    DecodedSearchTreeWorkload.lookupRun wordLtb (BitVec.ofNat 4 4)
      (DecodedSearchTreeWorkload.wordBuildRun 4 4).1 = (none, (4, 8)) := by
  simpa using DecodedSearchTreeWorkload.word_upper_missing_query 4 4 (by decide) (by decide)

/-- At the full prefix, encoding 8 gives -8. Its miss takes the first left
branch, so the upper-missing full-path formula would be false without its guard. -/
theorem four_bit_wrapped_missing :
    (BitVec.ofNat 4 8).toInt = -8 ∧
      DecodedSearchTreeWorkload.lookupRun wordLtb (BitVec.ofNat 4 8)
        (DecodedSearchTreeWorkload.wordBuildRun 4 8).1 = (none, (1, 1)) := by
  decide

/-- Width zero has one possible key; repeated writes replace it and each
query succeeds. These counts do not use a positive-width prefix theorem. -/
theorem zero_width_repeated_workload :
    DecodedSearchTreeWorkload.sourceRun wordLtb
      ([0, 0, 0] : List (BitVec 0)) [0, 0, 0] = (3, (5, 10)) := by
  decide

theorem zero_width_type_payload (key query : BitVec 0) (value : Type v)
    (tree : BinaryTree (BitVec 0 × Type v)) :
    DecodedSearchTreeWorkload.lookupRun wordLtb query
      (DecodedSearchTreeWorkload.insertRun wordLtb key value tree).1 =
      (some value, (1, 2)) :=
  DecodedSearchTreeWorkload.zero_width_lookup_after_insert key query value tree

/-- The actual signed 63-bit execution retains its decoded output tree and
each phase count throughout the guarded finite family. -/
theorem word63_finite_family (n : Nat) (bound : n ≤ 2 ^ 62) :
    (DecodedKeys.mapKeys BitVec.toInt (DecodedSearchTreeWorkload.wordBuildRun 63 n).1,
        (DecodedSearchTreeWorkload.wordBuildRun 63 n).2) =
        (DecodedKeys.mapKeys (fun k : Nat => (k : Int)) (rightSpine 1 0 n),
          (consecutiveBuildRun n).2) ∧
      (2 * (DecodedSearchTreeWorkload.wordBuildRun 63 n).2.1 = n * (n - 1) ∧
        (DecodedSearchTreeWorkload.wordBuildRun 63 n).2.2 = n * (n - 1)) ∧
      ((DecodedSearchTreeWorkload.wordQueryRun 63 n).1 = n ∧
        2 * (DecodedSearchTreeWorkload.wordQueryRun 63 n).2.1 = n * (n + 1) ∧
        (DecodedSearchTreeWorkload.wordQueryRun 63 n).2.2 = n * (n + 1)) ∧
      DecodedSearchTreeWorkload.wordSourceRun 63 n = (n, (n * n, 2 * (n * n))) :=
  ⟨DecodedSearchTreeWorkload.word63BuildRun_transport n bound,
    DecodedSearchTreeWorkload.word63BuildRun_counts n bound,
    DecodedSearchTreeWorkload.word63QueryRun_counts n bound,
    DecodedSearchTreeWorkload.word63SourceRun_exact n bound⟩

theorem int64_finite_family (n : Nat) (bound : n ≤ 2 ^ 63) :
    (DecodedKeys.mapKeys Int64.toInt (DecodedSearchTreeWorkload.int64BuildRun n).1,
        (DecodedSearchTreeWorkload.int64BuildRun n).2) =
        (DecodedKeys.mapKeys (fun k : Nat => (k : Int)) (rightSpine 1 0 n),
          (consecutiveBuildRun n).2) ∧
      (2 * (DecodedSearchTreeWorkload.int64BuildRun n).2.1 = n * (n - 1) ∧
        (DecodedSearchTreeWorkload.int64BuildRun n).2.2 = n * (n - 1)) ∧
      ((DecodedSearchTreeWorkload.int64QueryRun n).1 = n ∧
        2 * (DecodedSearchTreeWorkload.int64QueryRun n).2.1 = n * (n + 1) ∧
        (DecodedSearchTreeWorkload.int64QueryRun n).2.2 = n * (n + 1)) ∧
      DecodedSearchTreeWorkload.int64SourceRun n = (n, (n * n, 2 * (n * n))) :=
  ⟨DecodedSearchTreeWorkload.int64BuildRun_transport n bound,
    DecodedSearchTreeWorkload.int64BuildRun_counts n bound,
    DecodedSearchTreeWorkload.int64QueryRun_counts n bound,
    DecodedSearchTreeWorkload.int64SourceRun_exact n bound⟩

theorem word63_signed_endpoints :
    let low := BitVec.ofInt 63 (-(2 : Int) ^ 62)
    let high := BitVec.ofInt 63 ((2 : Int) ^ 62 - 1)
    low.toInt = -(2 : Int) ^ 62 ∧ high.toInt = (2 : Int) ^ 62 - 1 ∧
      DecodedSearchTreeWorkload.sourceRun wordLtb [low, high] [low, high] =
        (2, (4, 8)) := by
  decide

theorem int64_signed_endpoints :
    let low := Int64.ofInt (-(2 : Int) ^ 63)
    let high := Int64.ofInt ((2 : Int) ^ 63 - 1)
    low.toInt = -(2 : Int) ^ 63 ∧ high.toInt = (2 : Int) ^ 63 - 1 ∧
      DecodedSearchTreeWorkload.sourceRun int64Ltb [low, high] [low, high] =
        (2, (4, 8)) := by
  decide

theorem word_source_schedule_work (w n : Nat) (positive_width : 0 < w)
    (bound : n ≤ 2 ^ (w - 1)) :
    DecodedSearchTreeWorkload.sourceRun wordLtb
      ((Workload.sourceIndices n).map (fun j => BitVec.ofNat w (n - j)))
      ((Workload.sourceIndices n).map (fun j => BitVec.ofNat w (n - j))) =
      (n, (n * n, 2 * (n * n))) :=
  DecodedSearchTreeWorkload.word_source_schedule w n positive_width bound

/-- The chapter's difference-only unary comparison slogan fails already on
equal inputs. This is the explicit lockstep model, not Lean's native Nat. -/
theorem unary_equal_work (n : Nat) :
    (Resources.UnaryComparison.unaryLERun n n).1 = true ∧
      (Resources.UnaryComparison.unaryLERun n n).2 = n + 1 := by
  constructor
  · rw [Resources.UnaryComparison.unaryLERun_erases,
      Resources.UnaryComparison.unaryLE_eq_decide]
    simp
  · exact Resources.UnaryComparison.equal_inputs_steps n

theorem unary_difference_obstruction (bound : Nat → Nat) :
    (¬ ∀ n m, (Resources.UnaryComparison.unaryLERun n m).2 ≤
      bound ((n - m) + (m - n))) ∧
      ∃ n m, n - m = 0 ∧ m - n = 0 ∧
        bound 0 < (Resources.UnaryComparison.unaryLERun n m).2 := by
  refine ⟨Resources.UnaryComparison.no_difference_only_bound bound, ?_⟩
  refine ⟨bound 0, bound 0, by omega, by omega, ?_⟩
  rw [Resources.UnaryComparison.equal_inputs_steps]
  omega

end Examples.ExtractedProgramWork

import Applications.Search.OrderedMap.Workload
import Applications.Resources.SearchTree
import Applications.Resources.Workload
import Applications.Search.OrderedMap.DecodedKeys

/-!
# Measured finite build/query histories for the source unbalanced tree

Observations are `(nonempty node visits, primitive strict-comparator calls)`.
The existing measured insertion reconstructs its actual returned tree. The
existing `Resources.run` threads that tree through chronological writes; query
steps inspect the actual returned optional payload before updating the count.
No cost is attached to a separately computed or unrelated result.

Nil inspection, arithmetic on the hit counter, allocation, stack use, key
generation, comparator internals and time are outside this pair. Build and
query costs are separately exposed because the companion ML timer starts after
construction. The combined run is a further mathematical observation, not a
relabeling of that source timer. No random logarithmic bound is asserted.

The final section transports whole values and count pairs under strict-order
compatibility. A finite encoding is used only on a prefix on which decoding is
proved to recover each natural key. Its distinctness is derived, not assumed
for an unbounded family of finite words. Concrete word dictionaries and their
actual executable-decision bridges belong to the representation adapter.
The equations here state abstract observations, without runtime claims.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.SearchTreeWorkload
universe u v
variable {κ : Type u} {ν : Type v}
open SearchTree

section Ordered
variable [LinearOrder κ]

def buildRun (writes : List (κ × ν)) (tree : BinaryTree (κ × ν)) :
    Measured (BinaryTree (κ × ν)) (Nat × Nat) :=
  Resources.run (fun binding tree => insertRun binding.1 binding.2 tree) writes tree

@[simp] theorem buildRun_nil (tree : BinaryTree (κ × ν)) :
    buildRun [] tree = (tree, (0, 0)) := rfl

theorem buildRun_cons (key : κ) (value : ν) (rest : List (κ × ν))
    (tree : BinaryTree (κ × ν)) :
    buildRun ((key, value) :: rest) tree = bind (insertRun key value tree) (buildRun rest) := rfl

theorem buildRun_append (first second : List (κ × ν)) (tree : BinaryTree (κ × ν)) :
    buildRun (first ++ second) tree = bind (buildRun first tree) (buildRun second) :=
  Resources.run_append _ first second tree

theorem buildRun_value (writes : List (κ × ν)) (tree : BinaryTree (κ × ν)) :
    (buildRun writes tree).1 = Search.OrderedMap.Workload.buildFrom writes tree := by
  induction writes generalizing tree with
  | nil => rfl
  | cons binding rest ih =>
      rw [buildRun_cons, bind_value, ih, insertRun_value]
      rfl

def buildKeysRun (keys : List κ) :
    Measured (BinaryTree (κ × Nat)) (Nat × Nat) :=
  buildRun (Search.OrderedMap.Workload.sourceWrites keys) .nil

theorem buildKeysRun_value (keys : List κ) :
    (buildKeysRun keys).1 = Search.OrderedMap.Workload.buildKeys keys :=
  buildRun_value _ _

theorem buildKeysRun_snoc (keys : List κ) (key : κ) :
    buildKeysRun (keys ++ [key]) = bind (buildKeysRun keys) (insertRun key 1) := by
  simp only [buildKeysRun, Search.OrderedMap.Workload.sourceWrites,
    List.map_append, List.map_cons, List.map_nil, buildRun_append]
  exact congrArg (bind (buildRun (keys.map (fun key => (key, 1))) .nil))
    (funext fun tree => bind_pure (insertRun key 1 tree))

def queryStep (tree : BinaryTree (κ × Nat)) (query : κ) (count : Nat) :
    Measured Nat (Nat × Nat) :=
  bind (lookupRun query tree) fun result =>
    pure (if result.getD 0 = 1 then count + 1 else count)

theorem queryStep_work (tree : BinaryTree (κ × Nat)) (query : κ) (count : Nat) :
    (queryStep tree query count).2 = (lookupRun query tree).2 := by
  simp [queryStep, bind, pure]

def queryRun (queries : List κ) (tree : BinaryTree (κ × Nat)) :
    Measured Nat (Nat × Nat) :=
  Resources.run (queryStep tree) queries 0

theorem queryHits_cons (query : κ) (queries : List κ) (tree : BinaryTree (κ × Nat)) :
    Search.OrderedMap.Workload.queryHits (query :: queries) tree =
      (if (Search.OrderedMap.lookup query tree).getD 0 = 1 then 1 else 0) +
        Search.OrderedMap.Workload.queryHits queries tree := by
  simp only [Search.OrderedMap.Workload.queryHits,
    Search.OrderedMap.Workload.queryValues, List.map_cons, List.count_cons]
  split <;> simp_all
  omega

theorem run_queryStep_value (queries : List κ) (tree : BinaryTree (κ × Nat)) (count : Nat) :
    (Resources.run (queryStep tree) queries count).1 =
      count + Search.OrderedMap.Workload.queryHits queries tree := by
  induction queries generalizing count with
  | nil => rfl
  | cons query queries ih =>
      simp only [Resources.run_cons, queryStep, bind, pure, lookupRun_value]
      rw [ih, queryHits_cons]
      split <;> omega

theorem queryRun_value (queries : List κ) (tree : BinaryTree (κ × Nat)) :
    (queryRun queries tree).1 = Search.OrderedMap.Workload.queryHits queries tree := by
  simpa [queryRun] using run_queryStep_value queries tree 0

theorem queryRun_work (queries : List κ) (tree : BinaryTree (κ × Nat)) :
    (queryRun queries tree).2 =
      (queries.map (fun query => (lookupRun query tree).2)).sum :=
  Resources.run_observation (queryStep tree) (fun query => (lookupRun query tree).2)
    (queryStep_work tree) queries 0

theorem queryRun_visits_le_height (queries : List κ) (tree : BinaryTree (κ × Nat)) :
    (queryRun queries tree).2.1 ≤ queries.length * tree.height := by
  rw [queryRun_work]
  induction queries with
  | nil => simp
  | cons query queries ih =>
      have bound := lookupRun_visits_le_height query tree
      simp only [List.map_cons, List.sum_cons, Prod.fst_add, List.length_cons, Nat.add_mul]
      omega

theorem queryRun_comparisons_le_height (queries : List κ) (tree : BinaryTree (κ × Nat)) :
    (queryRun queries tree).2.2 ≤ 2 * (queries.length * tree.height) := by
  rw [queryRun_work]
  induction queries with
  | nil => simp
  | cons query queries ih =>
      have bound := lookupRun_comparisons_le_height query tree
      simp only [List.map_cons, List.sum_cons, Prod.snd_add, List.length_cons, Nat.add_mul]
      nlinarith

def sourceRun (inserted queries : List κ) : Measured Nat (Nat × Nat) :=
  bind (buildKeysRun inserted) (queryRun queries)

/-- The query phase consumes the actual completed measured build state. -/
theorem sourceRun_work (inserted queries : List κ) :
    (sourceRun inserted queries).2 = (buildKeysRun inserted).2 +
      (queryRun queries (buildKeysRun inserted).1).2 := rfl

theorem sourceRun_value (inserted queries : List κ) :
    (sourceRun inserted queries).1 = Search.OrderedMap.Workload.hits inserted queries := by
  simp only [sourceRun, bind_value, queryRun_value, buildKeysRun_value]
  rfl

theorem sourceRun_independent_count (inserted queries : List κ) :
    (sourceRun inserted queries).1 = Search.OrderedMap.Workload.expectedHits inserted queries := by
  rw [sourceRun_value, Search.OrderedMap.Workload.hits_eq_expected]

end Ordered

theorem bind_rightSpine_next (value : ν) (start n : Nat) :
    Search.OrderedMap.bind (start + n) value (rightSpine value start n) =
      rightSpine value start (n + 1) := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
      change Search.OrderedMap.bind (start + (n + 1)) value
        (.node (start, value) .nil (rightSpine value (start + 1) n)) =
          .node (start, value) .nil (rightSpine value (start + 1) (n + 1))
      have left : ¬ start + (n + 1) < start := by omega
      have right : start < start + (n + 1) := by omega
      rw [Search.OrderedMap.bind, ite_eq_right left, ite_eq_left right]
      have key : start + (n + 1) = (start + 1) + n := by omega
      rw [key, ih]

theorem buildKeys_range_eq_rightSpine (n : Nat) :
    Search.OrderedMap.Workload.buildKeys (List.range n) = rightSpine 1 0 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Search.OrderedMap.Workload.build
        ((List.range (n + 1)).map (fun key => (key, 1))) = _
      rw [List.range_succ, List.map_append]
      change Search.OrderedMap.Workload.build
        (Search.OrderedMap.Workload.sourceWrites (List.range n) ++ [(n, 1)]) = _
      rw [Search.OrderedMap.Workload.build_snoc]
      change Search.OrderedMap.bind n 1
        (Search.OrderedMap.Workload.buildKeys (List.range n)) = _
      rw [ih]
      simpa only [Nat.zero_add] using bind_rightSpine_next 1 0 n

theorem lookupRun_rightSpine_present (value : ν) (start n k : Nat) (inside : k < n) :
    lookupRun (start + k) (rightSpine value start n) =
      (some value, (k + 1, 2 * (k + 1))) := by
  induction n generalizing start k with
  | zero => omega
  | succ n ih =>
      cases k with
      | zero =>
          change lookupRun start
            (.node (start, value) .nil (rightSpine value (start + 1) n)) = _
          simp [lookupRun_node]
      | succ k =>
          change lookupRun (start + (k + 1))
            (.node (start, value) .nil (rightSpine value (start + 1) n)) = _
          have left : ¬ start + (k + 1) < start := by omega
          have right : start < start + (k + 1) := by omega
          rw [lookupRun_node, ite_eq_right left, ite_eq_left right]
          have key : start + (k + 1) = (start + 1) + k := by omega
          rw [key, ih (start + 1) k (by omega)]
          simp
          omega

def consecutiveBuildRun (n : Nat) :
    Measured (BinaryTree (Nat × Nat)) (Nat × Nat) := buildKeysRun (List.range n)

theorem consecutiveBuildRun_value (n : Nat) :
    (consecutiveBuildRun n).1 = rightSpine 1 0 n := by
  rw [consecutiveBuildRun, buildKeysRun_value, buildKeys_range_eq_rightSpine]

theorem consecutiveBuildRun_succ (n : Nat) :
    consecutiveBuildRun (n + 1) =
      (rightSpine 1 0 (n + 1), (consecutiveBuildRun n).2 + (n, 2 * n)) := by
  rw [consecutiveBuildRun, List.range_succ, buildKeysRun_snoc]
  change bind (consecutiveBuildRun n) (insertRun n 1) = _
  simp only [bind, consecutiveBuildRun_value]
  have next := bind_rightSpine_next 1 0 n
  simp only [Nat.zero_add] at next
  rw [insertRun_rightSpine 1 1 0 n n (by omega), next]

theorem consecutiveBuildRun_work_add (n : Nat) :
    2 * (consecutiveBuildRun n).2.1 + n = n * n ∧
      (consecutiveBuildRun n).2.2 + n = n * n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      rw [consecutiveBuildRun_succ]
      simp only [Prod.fst_add, Prod.snd_add]
      constructor <;> nlinarith [ih.1, ih.2]

theorem consecutiveBuildRun_double_visits (n : Nat) :
    2 * (consecutiveBuildRun n).2.1 = n * (n - 1) := by
  have count := (consecutiveBuildRun_work_add n).1
  rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  omega

theorem consecutiveBuildRun_comparisons (n : Nat) :
    (consecutiveBuildRun n).2.2 = n * (n - 1) := by
  have count := (consecutiveBuildRun_work_add n).2
  rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  omega

theorem successful_consecutive_query (n k : Nat) (inside : k < n) :
    lookupRun k (Search.OrderedMap.Workload.buildKeys (List.range n)) =
      (some 1, (k + 1, 2 * (k + 1))) := by
  rw [buildKeys_range_eq_rightSpine]
  simpa only [Nat.zero_add] using lookupRun_rightSpine_present 1 0 n k inside

/-- The first absent upper key traverses the entire tree actually built from
the consecutive source history, including the empty history. -/
theorem upper_missing_consecutive_query (n : Nat) :
    lookupRun n (Search.OrderedMap.Workload.buildKeys (List.range n)) =
      (none, (n, 2 * n)) := by
  rw [buildKeys_range_eq_rightSpine]
  exact lookupRun_rightSpine 1 0 n n (by omega)

/-- A successful full path remains available at the last represented key;
it does not require representing the next absent key. -/
theorem last_consecutive_query (n : Nat) (positive : 0 < n) :
    lookupRun (n - 1) (Search.OrderedMap.Workload.buildKeys (List.range n)) =
      (some 1, (n, 2 * n)) := by
  have found := successful_consecutive_query n (n - 1) (by omega)
  simpa only [Nat.sub_add_cancel (show 1 ≤ n by omega)] using found

def consecutiveQueryRun (n : Nat) : Measured Nat (Nat × Nat) :=
  queryRun (List.range n) (Search.OrderedMap.Workload.buildKeys (List.range n))

theorem consecutiveQueryRun_value (n : Nat) : (consecutiveQueryRun n).1 = n := by
  rw [consecutiveQueryRun, queryRun_value]
  exact Search.OrderedMap.Workload.source_consecutive_hits n

theorem sum_successful_steps (n : Nat) :
    2 * ((List.range n).map (fun k => k + 1)).sum = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
      nlinarith

theorem sum_successful_work (keys : List Nat) :
    (keys.map (fun k => (k + 1, 2 * (k + 1)))).sum =
      ((keys.map (fun k => k + 1)).sum, 2 * (keys.map (fun k => k + 1)).sum) := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      simp only [Prod.add_def, Nat.mul_add]

theorem consecutiveQueryRun_work (n : Nat) :
    (consecutiveQueryRun n).2 =
      (((List.range n).map (fun k => k + 1)).sum,
        2 * ((List.range n).map (fun k => k + 1)).sum) := by
  rw [consecutiveQueryRun, queryRun_work]
  have same : (List.range n).map
      (fun query => (lookupRun query
        (Search.OrderedMap.Workload.buildKeys (List.range n))).2) =
        (List.range n).map (fun k => (k + 1, 2 * (k + 1))) := by
    apply List.map_congr_left
    intro key member
    rw [successful_consecutive_query n key (List.mem_range.mp member)]
  rw [same, sum_successful_work]

theorem consecutiveQueryRun_double_visits (n : Nat) :
    2 * (consecutiveQueryRun n).2.1 = n * (n + 1) := by
  rw [consecutiveQueryRun_work]
  exact sum_successful_steps n

theorem consecutiveQueryRun_comparisons (n : Nat) :
    (consecutiveQueryRun n).2.2 = n * (n + 1) := by
  rw [consecutiveQueryRun_work]
  exact sum_successful_steps n

theorem sourceRun_consecutive (n : Nat) :
    sourceRun (List.range n) (List.range n) = (n, (n * n, 2 * (n * n))) := by
  apply Prod.ext
  · rw [sourceRun_value]
    exact Search.OrderedMap.Workload.source_consecutive_hits n
  · change (buildKeysRun (List.range n)).2 +
      (queryRun (List.range n) (buildKeysRun (List.range n)).1).2 = _
    rw [buildKeysRun_value]
    change (consecutiveBuildRun n).2 + (consecutiveQueryRun n).2 = _
    have buildCount := consecutiveBuildRun_work_add n
    have queryVisits := consecutiveQueryRun_double_visits n
    have queryComparisons := consecutiveQueryRun_comparisons n
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;>
      nlinarith [buildCount.1, buildCount.2]

/-- The source loops visit indices `n,...,1` and generate key `n-j` at each
step. Their exact chronological key lists inherit the measured family result. -/
theorem sourceRun_schedule (n : Nat) :
    sourceRun
        ((Search.OrderedMap.Workload.sourceIndices n).map (fun j => n - j))
        ((Search.OrderedMap.Workload.sourceIndices n).map (fun j => n - j)) =
      (n, (n * n, 2 * (n * n))) := by
  rw [Search.OrderedMap.Workload.sourceIndices_consecutive]
  exact sourceRun_consecutive n

section Decode
variable [LinearOrder κ]
open Search.OrderedMap.DecodedKeys (mapKeys mapKeys_node mapKeys_bind)

theorem lookupRun_mapKeys (decode : κ → Int)
    (compatible : ∀ a b, a < b ↔ decode a < decode b)
    (query : κ) (tree : BinaryTree (κ × ν)) :
    lookupRun (decode query) (mapKeys decode tree) = lookupRun query tree := by
  induction tree with
  | nil => rfl
  | node binding left right ihl ihr =>
      by_cases before : query < binding.1
      · have before' := (compatible query binding.1).mp before
        simp only [mapKeys_node, lookupRun_node, ite_eq_left before, ite_eq_left before', ihl]
      · have before' := mt (compatible query binding.1).mpr before
        by_cases after : binding.1 < query
        · have after' := (compatible binding.1 query).mp after
          simp only [mapKeys_node, lookupRun_node, ite_eq_right before, ite_eq_right before',
            ite_eq_left after, ite_eq_left after', ihr]
        · have after' := mt (compatible binding.1 query).mpr after
          simp only [mapKeys_node, lookupRun_node, ite_eq_right before, ite_eq_right before',
            ite_eq_right after, ite_eq_right after']

theorem insertRun_mapKeys (decode : κ → Int)
    (compatible : ∀ a b, a < b ↔ decode a < decode b)
    (key : κ) (value : ν) (tree : BinaryTree (κ × ν)) :
    (mapKeys decode (insertRun key value tree).1, (insertRun key value tree).2) =
      insertRun (decode key) value (mapKeys decode tree) := by
  apply Prod.ext
  · simp only [insertRun_value, mapKeys_bind decode compatible]
  · change (insertRun key value tree).2 =
      (insertRun (decode key) value (mapKeys decode tree)).2
    rw [insertRun_work, insertRun_work, lookupRun_mapKeys decode compatible]

theorem buildRun_mapKeys (decode : κ → Int)
    (compatible : ∀ a b, a < b ↔ decode a < decode b)
    (writes : List (κ × ν)) (tree : BinaryTree (κ × ν)) :
    (mapKeys decode (buildRun writes tree).1, (buildRun writes tree).2) =
      buildRun (writes.map (fun binding => (decode binding.1, binding.2)))
        (mapKeys decode tree) := by
  induction writes generalizing tree with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      rw [buildRun_cons, List.map_cons, buildRun_cons,
        ← insertRun_mapKeys decode compatible key value tree]
      simp only [bind]
      rw [← ih (insertRun key value tree).1]

theorem buildKeysRun_mapKeys (decode : κ → Int)
    (compatible : ∀ a b, a < b ↔ decode a < decode b) (keys : List κ) :
    (mapKeys decode (buildKeysRun keys).1, (buildKeysRun keys).2) =
      buildKeysRun (keys.map decode) := by
  simpa only [buildKeysRun, Search.OrderedMap.Workload.sourceWrites, List.map_map,
    Function.comp_def, Search.OrderedMap.DecodedKeys.mapKeys_empty] using
      buildRun_mapKeys decode compatible
        (Search.OrderedMap.Workload.sourceWrites keys) .nil

theorem buildKeys_mapKeys (decode : κ → Int)
    (compatible : ∀ a b, a < b ↔ decode a < decode b) (keys : List κ) :
    mapKeys decode (Search.OrderedMap.Workload.buildKeys keys) =
      Search.OrderedMap.Workload.buildKeys (keys.map decode) := by
  simpa only [buildKeysRun_value] using
    congrArg Prod.fst (buildKeysRun_mapKeys decode compatible keys)

theorem run_queryStep_mapKeys (decode : κ → Int)
    (compatible : ∀ a b, a < b ↔ decode a < decode b)
    (queries : List κ) (tree : BinaryTree (κ × Nat)) (count : Nat) :
    Resources.run (queryStep (mapKeys decode tree)) (queries.map decode) count =
      Resources.run (queryStep tree) queries count := by
  induction queries generalizing count with
  | nil => rfl
  | cons query queries ih =>
      rw [List.map_cons, Resources.run_cons, Resources.run_cons]
      have step : queryStep (mapKeys decode tree) (decode query) count =
          queryStep tree query count := by
        simp only [queryStep, lookupRun_mapKeys decode compatible]
      rw [step, ih]

theorem queryRun_mapKeys (decode : κ → Int)
    (compatible : ∀ a b, a < b ↔ decode a < decode b)
    (queries : List κ) (tree : BinaryTree (κ × Nat)) :
    queryRun (queries.map decode) (mapKeys decode tree) = queryRun queries tree :=
  run_queryStep_mapKeys decode compatible queries tree 0

theorem sourceRun_mapKeys (decode : κ → Int)
    (compatible : ∀ a b, a < b ↔ decode a < decode b) (inserted queries : List κ) :
    sourceRun (inserted.map decode) (queries.map decode) =
      sourceRun inserted queries := by
  unfold sourceRun
  rw [← buildKeysRun_mapKeys decode compatible inserted]
  simp only [bind]
  rw [queryRun_mapKeys decode compatible]

def encodedKeys (encode : Nat → κ) (n : Nat) : List κ := (List.range n).map encode

def encodedBuildRun (encode : Nat → κ) (n : Nat) :
    Measured (BinaryTree (κ × Nat)) (Nat × Nat) :=
  buildKeysRun (encodedKeys encode n)

def encodedQueryRun (encode : Nat → κ) (n : Nat) :
    Measured Nat (Nat × Nat) :=
  queryRun (encodedKeys encode n)
    (Search.OrderedMap.Workload.buildKeys (encodedKeys encode n))

omit [LinearOrder κ] in
theorem encodedKeys_decode (decode : κ → Int) (encode : Nat → κ) (n : Nat)
    (representable : ∀ k, k < n → decode (encode k) = (k : Int)) :
    (encodedKeys encode n).map decode =
      (List.range n).map (fun k : Nat => (k : Int)) := by
  simp only [encodedKeys, List.map_map]
  apply List.map_congr_left
  intro key member
  exact representable key (List.mem_range.mp member)

omit [LinearOrder κ] in
theorem encodedKeys_nodup (decode : κ → Int) (encode : Nat → κ) (n : Nat)
    (representable : ∀ k, k < n → decode (encode k) = (k : Int)) :
    (encodedKeys encode n).Nodup := by
  apply List.Nodup.of_map decode
  rw [encodedKeys_decode decode encode n representable]
  exact List.Nodup.map (fun _ _ equal => Int.ofNat.inj equal) List.nodup_range

theorem encodedBuildRun_transport (decode : κ → Int)
    (compatible : ∀ a b, a < b ↔ decode a < decode b)
    (encode : Nat → κ) (n : Nat)
    (representable : ∀ k, k < n → decode (encode k) = (k : Int)) :
    (mapKeys decode (encodedBuildRun encode n).1, (encodedBuildRun encode n).2) =
      (mapKeys (fun k : Nat => (k : Int)) (rightSpine 1 0 n),
        (consecutiveBuildRun n).2) := by
  have encoded := buildKeysRun_mapKeys decode compatible (encodedKeys encode n)
  rw [encodedKeys_decode decode encode n representable] at encoded
  have natural := buildKeysRun_mapKeys (fun k : Nat => (k : Int))
    (fun _ _ => by omega) (List.range n)
  have same := encoded.trans natural.symm
  change (mapKeys decode (encodedBuildRun encode n).1, (encodedBuildRun encode n).2) =
    (mapKeys (fun k : Nat => (k : Int)) (consecutiveBuildRun n).1,
      (consecutiveBuildRun n).2) at same
  rw [consecutiveBuildRun_value] at same
  exact same

theorem encodedBuildRun_work (decode : κ → Int)
    (compatible : ∀ a b, a < b ↔ decode a < decode b)
    (encode : Nat → κ) (n : Nat)
    (representable : ∀ k, k < n → decode (encode k) = (k : Int)) :
    (encodedBuildRun encode n).2 = (consecutiveBuildRun n).2 :=
  congrArg Prod.snd (encodedBuildRun_transport decode compatible encode n representable)

theorem encodedQueryRun_transport (decode : κ → Int)
    (compatible : ∀ a b, a < b ↔ decode a < decode b)
    (encode : Nat → κ) (n : Nat)
    (representable : ∀ k, k < n → decode (encode k) = (k : Int)) :
    encodedQueryRun encode n = consecutiveQueryRun n := by
  have encoded := queryRun_mapKeys decode compatible (encodedKeys encode n)
    (Search.OrderedMap.Workload.buildKeys (encodedKeys encode n))
  rw [buildKeys_mapKeys decode compatible,
    encodedKeys_decode decode encode n representable] at encoded
  have natural := queryRun_mapKeys (fun k : Nat => (k : Int)) (fun _ _ => by omega)
    (List.range n) (Search.OrderedMap.Workload.buildKeys (List.range n))
  rw [buildKeys_mapKeys (fun k : Nat => (k : Int)) (fun _ _ => by omega)] at natural
  exact encoded.symm.trans natural

theorem encoded_successful_query (decode : κ → Int)
    (compatible : ∀ a b, a < b ↔ decode a < decode b)
    (encode : Nat → κ) (n : Nat)
    (representable : ∀ k, k < n → decode (encode k) = (k : Int))
    (k : Nat) (inside : k < n) :
    lookupRun (encode k)
        (Search.OrderedMap.Workload.buildKeys (encodedKeys encode n)) =
      (some 1, (k + 1, 2 * (k + 1))) := by
  have encoded := lookupRun_mapKeys decode compatible (encode k)
    (Search.OrderedMap.Workload.buildKeys (encodedKeys encode n))
  rw [representable k inside, buildKeys_mapKeys decode compatible,
    encodedKeys_decode decode encode n representable] at encoded
  have natural := lookupRun_mapKeys (fun k : Nat => (k : Int)) (fun _ _ => by omega) k
    (Search.OrderedMap.Workload.buildKeys (List.range n))
  rw [buildKeys_mapKeys (fun k : Nat => (k : Int)) (fun _ _ => by omega)] at natural
  exact (encoded.symm.trans natural).trans (successful_consecutive_query n k inside)

/-- Querying the first absent upper key additionally requires representing
that key itself; representability only on the build prefix does not suffice. -/
theorem encoded_upper_missing_query (decode : κ → Int)
    (compatible : ∀ a b, a < b ↔ decode a < decode b)
    (encode : Nat → κ) (n : Nat)
    (representable : ∀ k, k < n → decode (encode k) = (k : Int))
    (query_representable : decode (encode n) = (n : Int)) :
    lookupRun (encode n)
        (Search.OrderedMap.Workload.buildKeys (encodedKeys encode n)) =
      (none, (n, 2 * n)) := by
  have encoded := lookupRun_mapKeys decode compatible (encode n)
    (Search.OrderedMap.Workload.buildKeys (encodedKeys encode n))
  rw [query_representable, buildKeys_mapKeys decode compatible,
    encodedKeys_decode decode encode n representable] at encoded
  have natural := lookupRun_mapKeys (fun k : Nat => (k : Int)) (fun _ _ => by omega) n
    (Search.OrderedMap.Workload.buildKeys (List.range n))
  rw [buildKeys_mapKeys (fun k : Nat => (k : Int)) (fun _ _ => by omega)] at natural
  exact (encoded.symm.trans natural).trans (upper_missing_consecutive_query n)

/-- The last successful query uses only the build-prefix guard, including a
full positive finite-word prefix whose next key is not representable. -/
theorem encoded_last_query (decode : κ → Int)
    (compatible : ∀ a b, a < b ↔ decode a < decode b)
    (encode : Nat → κ) (n : Nat)
    (representable : ∀ k, k < n → decode (encode k) = (k : Int))
    (positive : 0 < n) :
    lookupRun (encode (n - 1))
        (Search.OrderedMap.Workload.buildKeys (encodedKeys encode n)) =
      (some 1, (n, 2 * n)) := by
  have found := encoded_successful_query decode compatible encode n representable
    (n - 1) (by omega)
  simpa only [Nat.sub_add_cancel (show 1 ≤ n by omega)] using found

theorem sourceRun_encodedKeys_exact (decode : κ → Int)
    (compatible : ∀ a b, a < b ↔ decode a < decode b)
    (encode : Nat → κ) (n : Nat)
    (representable : ∀ k, k < n → decode (encode k) = (k : Int)) :
    sourceRun (encodedKeys encode n) (encodedKeys encode n) =
      (n, (n * n, 2 * (n * n))) := by
  have encoded := sourceRun_mapKeys decode compatible
    (encodedKeys encode n) (encodedKeys encode n)
  rw [encodedKeys_decode decode encode n representable] at encoded
  have natural := sourceRun_mapKeys (fun k : Nat => (k : Int)) (fun _ _ => by omega)
    (List.range n) (List.range n)
  exact (encoded.symm.trans natural).trans (sourceRun_consecutive n)

end Decode
end Resources.SearchTreeWorkload

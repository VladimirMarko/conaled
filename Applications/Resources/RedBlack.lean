import Applications.Resources.RedBlackBalance
import Applications.Resources.SearchTree
import Applications.Resources.TreeEnumeration
import Applications.Search.RedBlack.Depth

/-!
# Executed source operations and their separate resource observations

The actual measured Boolean comparator supplies each branch decision. Recursive
answers feed source balancing or accumulator traversal through `Measured.bind`.
Counts retain comparisons, comparator work, visits, terminal calls, balancing,
syntactic construction and final blackening as different observations. Their
erasure and structural bounds apply to raw trees without ordering assumptions.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RedBlack

universe u v
variable {κ : Type u} {ν : Type v}

open Search.RedBlack (Tree)

/-- One abstract unit for an invocation of the supplied Boolean test. -/
def unitComparator (ltb : κ → κ → Bool) (a b : κ) : Measured Bool Nat :=
  (ltb a b, 1)

/-- Keep the actual comparator answer, its work, and its invocation count. -/
def comparisonRun (cmp : κ → κ → Measured Bool Nat) (a b : κ) :
    Measured Bool Cost :=
  reweight (fun work => tick .comparisons 1 + tick .comparatorWork work) (cmp a b)

@[simp] theorem comparisonRun_value (cmp : κ → κ → Measured Bool Nat) (a b : κ) :
    (comparisonRun cmp a b).1 = (cmp a b).1 := rfl

@[simp] theorem comparisonRun_cost (cmp : κ → κ → Measured Bool Nat) (a b : κ) :
    (comparisonRun cmp a b).2 =
      tick .comparisons 1 + tick .comparatorWork (cmp a b).2 := rfl

/-- Only the selected search child is evaluated; the second test is short-circuited. -/
def lookupRun (cmp : κ → κ → Measured Bool Nat) (query : κ) :
    Tree κ ν → Measured (Option ν) Cost
  | .nil => (none, tick .terminalNils 1)
  | .node _ left binding right =>
      bind ((), tick .visits 1) fun _ =>
        bind (comparisonRun cmp query binding.1) fun less =>
          if less then lookupRun cmp query left
          else bind (comparisonRun cmp binding.1 query) fun greater =>
            if greater then lookupRun cmp query right
            else pure (some binding.2)

/-- Actual recursive results are passed into the complete source balance. -/
def insRun (cmp : κ → κ → Measured Bool Nat) (key : κ) (value : ν) :
    Tree κ ν → Measured (Tree κ ν) Cost
  | .nil =>
      bind ((), tick .terminalNils 1) fun _ => nodeRun .red .nil (key, value) .nil
  | .node color left binding right =>
      bind ((), tick .visits 1) fun _ =>
        bind (comparisonRun cmp key binding.1) fun less =>
          if less then
            bind (insRun cmp key value left) fun result =>
              balanceRun color result binding.1 binding.2 right
          else bind (comparisonRun cmp binding.1 key) fun greater =>
            if greater then
              bind (insRun cmp key value right) fun result =>
                balanceRun color left binding.1 binding.2 result
            else nodeRun color left (key, value) right

/-- Inspect the root once and syntactically reconstruct every nonempty root. -/
def makeBlackRun (t : Tree κ ν) : Measured (Tree κ ν) Cost :=
  bind (t, tick .rootInspections 1) fun
    | .nil => pure .nil
    | .node _ left binding right => nodeRun .black left binding right

/-- Public insertion performs final blackening even for an initially empty tree. -/
def insertRun (cmp : κ → κ → Measured Bool Nat) (key : κ) (value : ν)
    (t : Tree κ ν) : Measured (Tree κ ν) Cost :=
  bind (insRun cmp key value t) makeBlackRun

/-- The right accumulator is evaluated, consed, and then passed to the left call. -/
def elementsAuxRun : Tree κ ν → List (κ × ν) → Measured (List (κ × ν)) Cost
  | .nil, suffix => (suffix, tick .enumerationCalls 1)
  | .node _ left binding right, suffix =>
      bind ((), tick .enumerationCalls 1) fun _ =>
        bind (elementsAuxRun right suffix) fun tail =>
          bind (binding :: tail, tick .consConstructions 1) fun tail =>
            elementsAuxRun left tail

/-- Source enumeration starts the same measured accumulator with the empty suffix. -/
def elementsRun (t : Tree κ ν) : Measured (List (κ × ν)) Cost :=
  elementsAuxRun t []

@[simp] theorem lookupRun_nil (cmp : κ → κ → Measured Bool Nat) (query : κ) :
    lookupRun cmp query (.nil : Tree κ ν) = (none, tick .terminalNils 1) := rfl

theorem lookupRun_node (cmp : κ → κ → Measured Bool Nat) (query : κ)
    (color : RBTree.RBColor) (left : Tree κ ν) (key : κ) (value : ν)
    (right : Tree κ ν) :
    lookupRun cmp query (.node color left (key, value) right) =
      if (cmp query key).1 then
        ((lookupRun cmp query left).1,
          tick .visits 1 + (comparisonRun cmp query key).2 + (lookupRun cmp query left).2)
      else if (cmp key query).1 then
        ((lookupRun cmp query right).1,
          tick .visits 1 + (comparisonRun cmp query key).2 +
            (comparisonRun cmp key query).2 + (lookupRun cmp query right).2)
      else (some value, tick .visits 1 + (comparisonRun cmp query key).2 +
        (comparisonRun cmp key query).2) := by
  cases hfirst : (cmp query key).1 <;> cases hsecond : (cmp key query).1 <;>
    simp [lookupRun, bind, pure, comparisonRun, hfirst, hsecond, add_assoc]

/-- Erasure uses the actually returned Boolean decisions, with no order premise. -/
theorem lookupRun_value (cmp : κ → κ → Measured Bool Nat) (query : κ) (t : Tree κ ν) :
    (lookupRun cmp query t).1 =
      Search.RedBlack.lookup? (fun a b => (cmp a b).1) query t := by
  induction t with
  | nil => rfl
  | node color left binding right ihl ihr =>
      obtain ⟨key, value⟩ := binding
      rw [lookupRun_node, Search.RedBlack.lookup?_node]
      split
      · exact ihl
      · split
        · exact ihr
        · rfl

/-- A supplied source comparator needs only agreement of its returned Booleans. -/
theorem lookupRun_value_of (cmp : κ → κ → Measured Bool Nat) (ltb : κ → κ → Bool)
    (agreement : ∀ a b, (cmp a b).1 = ltb a b) (query : κ) (t : Tree κ ν) :
    (lookupRun cmp query t).1 = Search.RedBlack.lookup? ltb query t := by
  rw [lookupRun_value]
  simp only [agreement]

/-- Applying a caller's default is an unpriced adapter of the actual optional result. -/
theorem lookupRun_getD (cmp : κ → κ → Measured Bool Nat) (default : ν)
    (query : κ) (t : Tree κ ν) :
    (lookupRun cmp query t).1.getD default =
      Search.RedBlack.lookup (fun a b => (cmp a b).1) default query t := by
  rw [lookupRun_value]
  rfl

/-- The old ordinary-tree execution receives exactly the visit/work projection. -/
theorem lookupRun_searchTree (cmp : κ → κ → Measured Bool Nat) (query : κ)
    (t : Tree κ ν) :
    reweight (fun c : Cost => (c .visits, c .comparatorWork)) (lookupRun cmp query t) =
      Resources.SearchTree.lookupWithRun cmp query (Search.RedBlack.eraseColors t) := by
  induction t with
  | nil => rfl
  | node color left binding right ihl ihr =>
      obtain ⟨key, value⟩ := binding
      rw [lookupRun_node, Search.RedBlack.eraseColors_node,
        Resources.SearchTree.lookupWithRun_node]
      split
      · simp only [reweight] at ihl ⊢
        rw [← ihl]
        simp [comparisonRun_cost, tick, Pi.add_apply, Nat.add_comm]
      · split
        · simp only [reweight] at ihr ⊢
          rw [← ihr]
          simp [comparisonRun_cost, tick, Pi.add_apply, Nat.add_comm, Nat.add_assoc]
        · simp [reweight, comparisonRun_cost, tick, Pi.add_apply]

theorem lookupRun_visits_le_height (cmp : κ → κ → Measured Bool Nat) (query : κ)
    (t : Tree κ ν) : (lookupRun cmp query t).2 .visits ≤ Search.RedBlack.height t := by
  have h := Resources.SearchTree.lookupWithRun_visits_le_height cmp query
    (Search.RedBlack.eraseColors t)
  rw [← lookupRun_searchTree, Search.RedBlack.eraseColors_height] at h
  exact h

/-- This finite-input premise bounds only comparisons against labels in this tree. -/
theorem lookupRun_comparatorWork_le_visits (cmp : κ → κ → Measured Bool Nat)
    (query : κ) (t : Tree κ ν) (K : Nat)
    (local_bound : Search.RedBlack.ForallT
      (fun key _ => (cmp query key).2 ≤ K ∧ (cmp key query).2 ≤ K) t) :
    (lookupRun cmp query t).2 .comparatorWork ≤ 2 * K * (lookupRun cmp query t).2 .visits := by
  have h := Resources.SearchTree.lookupWithRun_work_le_visits cmp query
    (Search.RedBlack.eraseColors t) K
    ((Search.RedBlack.eraseColors_forallT _ t).mpr local_bound)
  rw [← lookupRun_searchTree] at h
  exact h

theorem lookupRun_comparatorWork_le_height (cmp : κ → κ → Measured Bool Nat)
    (query : κ) (t : Tree κ ν) (K : Nat)
    (local_bound : Search.RedBlack.ForallT
      (fun key _ => (cmp query key).2 ≤ K ∧ (cmp key query).2 ≤ K) t) :
    (lookupRun cmp query t).2 .comparatorWork ≤ 2 * K * Search.RedBlack.height t :=
  (lookupRun_comparatorWork_le_visits cmp query t K local_bound).trans
    (Nat.mul_le_mul_left (2 * K) (lookupRun_visits_le_height cmp query t))

/-- There are one or two Boolean calls at each visited nonempty node. -/
theorem lookupRun_comparisons_le_twice_visits (cmp : κ → κ → Measured Bool Nat)
    (query : κ) (t : Tree κ ν) :
    (lookupRun cmp query t).2 .comparisons ≤ 2 * (lookupRun cmp query t).2 .visits := by
  induction t with
  | nil => simp [lookupRun_nil, tick]
  | node color left binding right ihl ihr =>
      obtain ⟨key, value⟩ := binding
      rw [lookupRun_node]
      split
      · simp only [Pi.add_apply, comparisonRun_cost]
        simp [tick] at *
        omega
      · split
        · simp only [Pi.add_apply, comparisonRun_cost]
          simp [tick] at *
          omega
        · simp [comparisonRun_cost, tick, Pi.add_apply]

theorem lookupRun_comparisons_le_height (cmp : κ → κ → Measured Bool Nat)
    (query : κ) (t : Tree κ ν) :
    (lookupRun cmp query t).2 .comparisons ≤ 2 * Search.RedBlack.height t :=
  (lookupRun_comparisons_le_twice_visits cmp query t).trans
    (Nat.mul_le_mul_left 2 (lookupRun_visits_le_height cmp query t))

/-- Exactly one nil is reached on a miss; a returned binding avoids that call. -/
theorem lookupRun_terminalNils (cmp : κ → κ → Measured Bool Nat) (query : κ)
    (t : Tree κ ν) :
    (lookupRun cmp query t).2 .terminalNils = if (lookupRun cmp query t).1.isNone then 1 else 0 := by
  induction t with
  | nil => rfl
  | node color left binding right ihl ihr =>
      obtain ⟨key, value⟩ := binding
      rw [lookupRun_node]
      split
      · simpa [comparisonRun_cost, tick, Pi.add_apply] using ihl
      · split
        · simpa [comparisonRun_cost, tick, Pi.add_apply] using ihr
        · simp [comparisonRun_cost, tick, Pi.add_apply]

theorem lookupRun_terminalNils_le (cmp : κ → κ → Measured Bool Nat) (query : κ)
    (t : Tree κ ν) : (lookupRun cmp query t).2 .terminalNils ≤ 1 := by
  rw [lookupRun_terminalNils]
  split <;> omega

/-- Search never constructs a node/list or performs balancing/blackening. -/
theorem lookupRun_other (cmp : κ → κ → Measured Bool Nat) (query : κ)
    (t : Tree κ ν) (metric : Metric)
    (hL : metric ≠ .visits) (hQ : metric ≠ .comparisons)
    (hM : metric ≠ .comparatorWork) (hT : metric ≠ .terminalNils) :
    (lookupRun cmp query t).2 metric = 0 := by
  induction t with
  | nil => simp [lookupRun_nil, tick, hT]
  | node color left binding right ihl ihr =>
      obtain ⟨key, value⟩ := binding
      rw [lookupRun_node]
      split
      · simp [comparisonRun_cost, Pi.add_apply, tick, hL, hQ, hM, ihl]
      · split <;> simp [comparisonRun_cost, Pi.add_apply, tick, hL, hQ, hM, ihr]

/-- A unit-price comparator really records one work unit per Boolean call. -/
theorem lookupRun_unit_comparatorWork (ltb : κ → κ → Bool) (query : κ)
    (t : Tree κ ν) :
    (lookupRun (unitComparator ltb) query t).2 .comparatorWork =
      (lookupRun (unitComparator ltb) query t).2 .comparisons := by
  induction t with
  | nil => rfl
  | node color left binding right ihl ihr =>
      obtain ⟨key, value⟩ := binding
      rw [lookupRun_node]
      split
      · simp [comparisonRun_cost, Pi.add_apply, tick, unitComparator, ihl]
      · split <;> simp [comparisonRun_cost, Pi.add_apply, tick, unitComparator, ihr]

@[simp] theorem makeBlackRun_value (t : Tree κ ν) :
    (makeBlackRun t).1 = Search.RedBlack.makeBlack t := by
  cases t <;> rfl

@[simp] theorem makeBlackRun_nil :
    makeBlackRun (.nil : Tree κ ν) = (.nil, tick .rootInspections 1) := by
  simp [makeBlackRun, bind, pure]

theorem makeBlackRun_node (color : RBTree.RBColor) (left : Tree κ ν)
    (binding : κ × ν) (right : Tree κ ν) :
    makeBlackRun (.node color left binding right) =
      (.node .black left binding right, tick .rootInspections 1 + tick .nodeConstructions 1) := rfl

@[simp] theorem elementsAuxRun_nil (suffix : List (κ × ν)) :
    elementsAuxRun (.nil : Tree κ ν) suffix = (suffix, tick .enumerationCalls 1) := rfl

theorem elementsAuxRun_node (color : RBTree.RBColor) (left : Tree κ ν)
    (binding : κ × ν) (right : Tree κ ν) (suffix : List (κ × ν)) :
    elementsAuxRun (.node color left binding right) suffix =
      ((elementsAuxRun left (binding :: (elementsAuxRun right suffix).1)).1,
        tick .enumerationCalls 1 + (elementsAuxRun right suffix).2 +
          tick .consConstructions 1 +
            (elementsAuxRun left (binding :: (elementsAuxRun right suffix).1)).2) := by
  simp [elementsAuxRun, bind, add_assoc]

/-- No ordering, balancing, or restriction on the pre-existing suffix is needed. -/
theorem elementsAuxRun_value (t : Tree κ ν) (suffix : List (κ × ν)) :
    (elementsAuxRun t suffix).1 = Search.RedBlack.elementsAux t suffix := by
  induction t generalizing suffix with
  | nil => rfl
  | node color left binding right ihl ihr =>
      obtain ⟨key, value⟩ := binding
      simp only [elementsAuxRun_node, Search.RedBlack.elementsAux_node, ihl, ihr]

theorem elementsRun_value (t : Tree κ ν) :
    (elementsRun t).1 = Search.RedBlack.elements t :=
  elementsAuxRun_value t []

/-- Project to the accepted accumulator execution, retaining its actual suffix. -/
theorem elementsAuxRun_treeEnumeration (t : Tree κ ν) (suffix : List (κ × ν)) :
    reweight (fun c : Cost => (c .enumerationCalls, c .consConstructions))
      (elementsAuxRun t suffix) =
      Resources.TreeEnumeration.accumulatorRun (Search.RedBlack.eraseColors t) suffix := by
  induction t generalizing suffix with
  | nil => rfl
  | node color left binding right ihl ihr =>
      obtain ⟨key, value⟩ := binding
      rw [elementsAuxRun_node, Search.RedBlack.eraseColors_node,
        Resources.TreeEnumeration.accumulatorRun_node]
      simp only [Resources.TreeAccumulator.nodeRun, bind]
      rw [← ihr suffix]
      simp only [reweight]
      rw [← ihl ((key, value) :: (elementsAuxRun right suffix).1)]
      simp [reweight, Pi.add_apply, tick, Nat.add_assoc, Nat.add_comm]

/-- Every internal node contributes one cons; every node and nil contributes a call. -/
theorem elementsAuxRun_counts (t : Tree κ ν) (suffix : List (κ × ν)) :
    ((elementsAuxRun t suffix).2 .enumerationCalls,
      (elementsAuxRun t suffix).2 .consConstructions) = (2 * t.size + 1, t.size) := by
  have h := Resources.TreeEnumeration.accumulatorRun_work (Search.RedBlack.eraseColors t) suffix
  rw [← elementsAuxRun_treeEnumeration, Search.RedBlack.eraseColors_numNodes] at h
  exact h

theorem elementsAuxRun_enumerationCalls (t : Tree κ ν) (suffix : List (κ × ν)) :
    (elementsAuxRun t suffix).2 .enumerationCalls = 2 * t.size + 1 :=
  congrArg Prod.fst (elementsAuxRun_counts t suffix)

theorem elementsAuxRun_consConstructions (t : Tree κ ν) (suffix : List (κ × ν)) :
    (elementsAuxRun t suffix).2 .consConstructions = t.size :=
  congrArg Prod.snd (elementsAuxRun_counts t suffix)

theorem elementsAuxRun_other (t : Tree κ ν) (suffix : List (κ × ν)) (metric : Metric)
    (hE : metric ≠ .enumerationCalls) (hC : metric ≠ .consConstructions) :
    (elementsAuxRun t suffix).2 metric = 0 := by
  induction t generalizing suffix with
  | nil => simp [elementsAuxRun_nil, tick, hE]
  | node color left binding right ihl ihr =>
      rw [elementsAuxRun_node]
      simp [Pi.add_apply, tick, hE, hC, ihl, ihr]

/-- The suffix length has no effect on either traversal count or any other metric. -/
theorem elementsAuxRun_cost_independent (t : Tree κ ν) (xs ys : List (κ × ν)) :
    (elementsAuxRun t xs).2 = (elementsAuxRun t ys).2 := by
  funext metric
  cases metric <;>
    simp [elementsAuxRun_enumerationCalls, elementsAuxRun_consConstructions,
      elementsAuxRun_other]


@[simp] theorem insRun_nil (cmp : κ → κ → Measured Bool Nat) (key : κ) (value : ν) :
    insRun cmp key value (.nil : Tree κ ν) =
      (.node .red .nil (key, value) .nil,
        tick .terminalNils 1 + tick .nodeConstructions 1) := rfl

/-- The full source balance receives the actually returned child on either descent. -/
theorem insRun_node (cmp : κ → κ → Measured Bool Nat) (key : κ) (value : ν)
    (color : RBTree.RBColor) (left : Tree κ ν) (old : κ) (previous : ν)
    (right : Tree κ ν) :
    insRun cmp key value (.node color left (old, previous) right) =
      if (cmp key old).1 then
        let balanced := balanceRun color (insRun cmp key value left).1 old previous right
        (balanced.1, tick .visits 1 + (comparisonRun cmp key old).2 +
          (insRun cmp key value left).2 + balanced.2)
      else if (cmp old key).1 then
        let balanced := balanceRun color left old previous (insRun cmp key value right).1
        (balanced.1, tick .visits 1 + (comparisonRun cmp key old).2 +
          (comparisonRun cmp old key).2 + (insRun cmp key value right).2 + balanced.2)
      else (.node color left (key, value) right,
        tick .visits 1 + (comparisonRun cmp key old).2 +
          (comparisonRun cmp old key).2 + tick .nodeConstructions 1) := by
  cases hfirst : (cmp key old).1 <;> cases hsecond : (cmp old key).1 <;>
    simp [insRun, bind, comparisonRun, hfirst, hsecond, nodeRun, add_assoc]

/-- Raw erasure is the actual source insertion, not the provider's different algorithm. -/
theorem insRun_value (cmp : κ → κ → Measured Bool Nat) (key : κ) (value : ν)
    (t : Tree κ ν) :
    (insRun cmp key value t).1 =
      Search.RedBlack.ins (fun a b => (cmp a b).1) key value t := by
  induction t with
  | nil => rfl
  | node color left binding right ihl ihr =>
      obtain ⟨old, previous⟩ := binding
      rw [insRun_node, Search.RedBlack.ins_node]
      split
      · simp only [balanceRun_value, ihl]
      · split
        · simp only [balanceRun_value, ihr]
        · rfl

theorem insRun_value_of (cmp : κ → κ → Measured Bool Nat) (ltb : κ → κ → Bool)
    (agreement : ∀ a b, (cmp a b).1 = ltb a b) (key : κ) (value : ν) (t : Tree κ ν) :
    (insRun cmp key value t).1 = Search.RedBlack.ins ltb key value t := by
  rw [insRun_value]
  simp only [agreement]

theorem insRun_ne_nil (cmp : κ → κ → Measured Bool Nat) (key : κ) (value : ν)
    (t : Tree κ ν) : (insRun cmp key value t).1 ≠ .nil := by
  rw [insRun_value]
  exact Search.RedBlack.ins_ne_nil _ key value t

/-- Every nonempty root, including an already-black one, is reconstructed once. -/
theorem makeBlackRun_cost_of_ne_nil {t : Tree κ ν} (nonempty : t ≠ .nil) :
    (makeBlackRun t).2 = tick .rootInspections 1 + tick .nodeConstructions 1 := by
  cases t with
  | nil => exact False.elim (nonempty rfl)
  | node color left binding right => rfl

theorem insertRun_value (cmp : κ → κ → Measured Bool Nat) (key : κ) (value : ν)
    (t : Tree κ ν) :
    (insertRun cmp key value t).1 =
      Search.RedBlack.insert (fun a b => (cmp a b).1) key value t := by
  rw [insertRun, bind_value, makeBlackRun_value, insRun_value]
  rfl

theorem insertRun_value_of (cmp : κ → κ → Measured Bool Nat) (ltb : κ → κ → Bool)
    (agreement : ∀ a b, (cmp a b).1 = ltb a b) (key : κ) (value : ν) (t : Tree κ ν) :
    (insertRun cmp key value t).1 = Search.RedBlack.insert ltb key value t := by
  rw [insertRun_value]
  simp only [agreement]

theorem insertRun_ne_nil (cmp : κ → κ → Measured Bool Nat) (key : κ) (value : ν)
    (t : Tree κ ν) : (insertRun cmp key value t).1 ≠ .nil := by
  rw [insertRun_value]
  exact Search.RedBlack.insert_ne_nil _ key value t

/-- Exact final blackening cost follows from actual raw insertion nonemptiness. -/
theorem insertRun_cost (cmp : κ → κ → Measured Bool Nat) (key : κ) (value : ν)
    (t : Tree κ ν) :
    (insertRun cmp key value t).2 =
      (insRun cmp key value t).2 + tick .rootInspections 1 + tick .nodeConstructions 1 := by
  simp only [insertRun, bind]
  rw [makeBlackRun_cost_of_ne_nil (insRun_ne_nil cmp key value t)]
  exact (add_assoc _ _ _).symm


/-- Visits, tests, comparator work and the terminal call follow the original search path. -/
theorem insRun_descent (cmp : κ → κ → Measured Bool Nat) (key : κ) (value : ν)
    (t : Tree κ ν) (metric : Metric)
    (hB : metric ≠ .balanceCalls) (hP : metric ≠ .patternAttempts)
    (hD : metric ≠ .datatypeObservations) (hA : metric ≠ .nodeConstructions) :
    (insRun cmp key value t).2 metric = (lookupRun cmp key t).2 metric := by
  induction t with
  | nil => simp [insRun_nil, lookupRun_nil, Pi.add_apply, tick, hA]
  | node color left binding right ihl ihr =>
      obtain ⟨old, previous⟩ := binding
      rw [insRun_node, lookupRun_node]
      split
      · simp [Pi.add_apply, balanceRun_other, hB, hP, hD, hA, ihl]
      · split
        · simp [Pi.add_apply, balanceRun_other, hB, hP, hD, hA, ihr, Nat.add_assoc]
        · simp [Pi.add_apply, tick, hA]

theorem insRun_visits (cmp : κ → κ → Measured Bool Nat) (key : κ) (value : ν)
    (t : Tree κ ν) : (insRun cmp key value t).2 .visits = (lookupRun cmp key t).2 .visits :=
  insRun_descent cmp key value t .visits (by decide) (by decide) (by decide) (by decide)

theorem insRun_comparisons (cmp : κ → κ → Measured Bool Nat) (key : κ) (value : ν)
    (t : Tree κ ν) :
    (insRun cmp key value t).2 .comparisons = (lookupRun cmp key t).2 .comparisons :=
  insRun_descent cmp key value t .comparisons (by decide) (by decide) (by decide) (by decide)

theorem insRun_comparatorWork (cmp : κ → κ → Measured Bool Nat) (key : κ) (value : ν)
    (t : Tree κ ν) :
    (insRun cmp key value t).2 .comparatorWork = (lookupRun cmp key t).2 .comparatorWork :=
  insRun_descent cmp key value t .comparatorWork (by decide) (by decide) (by decide) (by decide)

theorem insRun_terminalNils (cmp : κ → κ → Measured Bool Nat) (key : κ) (value : ν)
    (t : Tree κ ν) :
    (insRun cmp key value t).2 .terminalNils = (lookupRun cmp key t).2 .terminalNils :=
  insRun_descent cmp key value t .terminalNils (by decide) (by decide) (by decide) (by decide)

theorem insRun_visits_le_height (cmp : κ → κ → Measured Bool Nat) (key : κ) (value : ν)
    (t : Tree κ ν) : (insRun cmp key value t).2 .visits ≤ Search.RedBlack.height t := by
  rw [insRun_visits]
  exact lookupRun_visits_le_height cmp key t

theorem insRun_comparisons_le_twice_visits (cmp : κ → κ → Measured Bool Nat)
    (key : κ) (value : ν) (t : Tree κ ν) :
    (insRun cmp key value t).2 .comparisons ≤ 2 * (insRun cmp key value t).2 .visits := by
  rw [insRun_comparisons, insRun_visits]
  exact lookupRun_comparisons_le_twice_visits cmp key t

theorem insRun_comparisons_le_height (cmp : κ → κ → Measured Bool Nat)
    (key : κ) (value : ν) (t : Tree κ ν) :
    (insRun cmp key value t).2 .comparisons ≤ 2 * Search.RedBlack.height t := by
  rw [insRun_comparisons]
  exact lookupRun_comparisons_le_height cmp key t

theorem insRun_comparatorWork_le_height (cmp : κ → κ → Measured Bool Nat)
    (key : κ) (value : ν) (t : Tree κ ν) (K : Nat)
    (local_bound : Search.RedBlack.ForallT
      (fun old _ => (cmp key old).2 ≤ K ∧ (cmp old key).2 ≤ K) t) :
    (insRun cmp key value t).2 .comparatorWork ≤ 2 * K * Search.RedBlack.height t := by
  rw [insRun_comparatorWork]
  exact lookupRun_comparatorWork_le_height cmp key t K local_bound

theorem insRun_terminalNils_le (cmp : κ → κ → Measured Bool Nat)
    (key : κ) (value : ν) (t : Tree κ ν) : (insRun cmp key value t).2 .terminalNils ≤ 1 := by
  rw [insRun_terminalNils]
  exact lookupRun_terminalNils_le cmp key t

/-- Equality does not call balance; a recursive descent calls it once on unwind. -/
theorem insRun_balanceCalls_le_visits (cmp : κ → κ → Measured Bool Nat)
    (key : κ) (value : ν) (t : Tree κ ν) :
    (insRun cmp key value t).2 .balanceCalls ≤ (insRun cmp key value t).2 .visits := by
  rw [insRun_visits]
  induction t with
  | nil => simp [insRun_nil, lookupRun_nil, Pi.add_apply, tick]
  | node color left binding right ihl ihr =>
      obtain ⟨old, previous⟩ := binding
      rw [insRun_node, lookupRun_node]
      split
      · simp [Pi.add_apply, comparisonRun_cost, tick, balanceRun_balanceCalls] at *
        omega
      · split
        · simp [Pi.add_apply, comparisonRun_cost, tick, balanceRun_balanceCalls] at *
          omega
        · simp [Pi.add_apply, comparisonRun_cost, tick]

theorem insRun_balanceCalls_le_height (cmp : κ → κ → Measured Bool Nat)
    (key : κ) (value : ν) (t : Tree κ ν) :
    (insRun cmp key value t).2 .balanceCalls ≤ Search.RedBlack.height t :=
  (insRun_balanceCalls_le_visits cmp key value t).trans
    (insRun_visits_le_height cmp key value t)

private theorem insRun_local_bound (cmp : κ → κ → Measured Bool Nat)
    (key : κ) (value : ν) (t : Tree κ ν) (metric : Metric)
    (hL : metric ≠ .visits) (hQ : metric ≠ .comparisons)
    (hM : metric ≠ .comparatorWork) (hT : metric ≠ .terminalNils)
    (K base : Nat) (leaf : tick .nodeConstructions 1 metric ≤ base)
    (local_cost : ∀ color (left : Tree κ ν) old previous right,
      (balanceRun color left old previous right).2 metric ≤ K) :
    (insRun cmp key value t).2 metric ≤ K * (insRun cmp key value t).2 .balanceCalls + base := by
  induction t with
  | nil => simpa [insRun_nil, Pi.add_apply, tick, hT] using leaf
  | node color left binding right ihl ihr =>
      obtain ⟨old, previous⟩ := binding
      rw [insRun_node]
      split
      · have h := local_cost color (insRun cmp key value left).1 old previous right
        simp [Pi.add_apply, comparisonRun_cost, tick, hL, hQ, hM,
          balanceRun_balanceCalls] at *
        nlinarith
      · split
        · have h := local_cost color left old previous (insRun cmp key value right).1
          simp [Pi.add_apply, comparisonRun_cost, tick, hL, hQ, hM,
            balanceRun_balanceCalls] at *
          nlinarith
        · simpa [Pi.add_apply, comparisonRun_cost, tick, hL, hQ, hM] using leaf

theorem insRun_patternAttempts_le (cmp : κ → κ → Measured Bool Nat)
    (key : κ) (value : ν) (t : Tree κ ν) :
    (insRun cmp key value t).2 .patternAttempts ≤ 5 * (insRun cmp key value t).2 .balanceCalls := by
  simpa only [Nat.add_zero] using insRun_local_bound cmp key value t .patternAttempts
    (by decide) (by decide) (by decide) (by decide) 5 0 (by decide)
    (fun color left old previous right => balanceRun_patternAttempts_le color left old previous right)

theorem insRun_datatypeObservations_le (cmp : κ → κ → Measured Bool Nat)
    (key : κ) (value : ν) (t : Tree κ ν) :
    (insRun cmp key value t).2 .datatypeObservations ≤
      17 * (insRun cmp key value t).2 .balanceCalls := by
  simpa only [Nat.add_zero] using insRun_local_bound cmp key value t .datatypeObservations
    (by decide) (by decide) (by decide) (by decide) 17 0 (by decide)
    (fun color left old previous right => balanceRun_datatypeObservations_le color left old previous right)

theorem insRun_nodeConstructions_le (cmp : κ → κ → Measured Bool Nat)
    (key : κ) (value : ν) (t : Tree κ ν) :
    (insRun cmp key value t).2 .nodeConstructions ≤
      3 * (insRun cmp key value t).2 .balanceCalls + 1 :=
  insRun_local_bound cmp key value t .nodeConstructions
    (by decide) (by decide) (by decide) (by decide) 3 1 (Nat.le_refl _)
    (fun color left old previous right => balanceRun_nodeConstructions_le color left old previous right)

theorem insRun_nodeConstructions_le_height (cmp : κ → κ → Measured Bool Nat)
    (key : κ) (value : ν) (t : Tree κ ν) :
    (insRun cmp key value t).2 .nodeConstructions ≤ 3 * Search.RedBlack.height t + 1 :=
  (insRun_nodeConstructions_le cmp key value t).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 3 (insRun_balanceCalls_le_height cmp key value t)) 1)

/-- The raw insertion has no final root inspection or enumeration charges. -/
theorem insRun_other (cmp : κ → κ → Measured Bool Nat) (key : κ) (value : ν)
    (t : Tree κ ν) (metric : Metric)
    (hL : metric ≠ .visits) (hQ : metric ≠ .comparisons) (hM : metric ≠ .comparatorWork)
    (hB : metric ≠ .balanceCalls) (hP : metric ≠ .patternAttempts)
    (hD : metric ≠ .datatypeObservations) (hA : metric ≠ .nodeConstructions)
    (hT : metric ≠ .terminalNils) : (insRun cmp key value t).2 metric = 0 := by
  rw [insRun_descent cmp key value t metric hB hP hD hA]
  exact lookupRun_other cmp key t metric hL hQ hM hT

/-- Final blackening changes precisely the root-inspection and node-construction coordinates. -/
theorem insertRun_preserves_metric (cmp : κ → κ → Measured Bool Nat)
    (key : κ) (value : ν) (t : Tree κ ν) (metric : Metric)
    (hR : metric ≠ .rootInspections) (hA : metric ≠ .nodeConstructions) :
    (insertRun cmp key value t).2 metric = (insRun cmp key value t).2 metric := by
  rw [insertRun_cost]
  simp [Pi.add_apply, tick, hR, hA]

theorem insertRun_rootInspections (cmp : κ → κ → Measured Bool Nat)
    (key : κ) (value : ν) (t : Tree κ ν) :
    (insertRun cmp key value t).2 .rootInspections = 1 := by
  rw [insertRun_cost]
  simp [Pi.add_apply, tick, insRun_other]

theorem insertRun_nodeConstructions (cmp : κ → κ → Measured Bool Nat)
    (key : κ) (value : ν) (t : Tree κ ν) :
    (insertRun cmp key value t).2 .nodeConstructions =
      (insRun cmp key value t).2 .nodeConstructions + 1 := by
  rw [insertRun_cost]
  simp [Pi.add_apply, tick]

theorem insertRun_visits_le_height (cmp : κ → κ → Measured Bool Nat)
    (key : κ) (value : ν) (t : Tree κ ν) :
    (insertRun cmp key value t).2 .visits ≤ Search.RedBlack.height t := by
  rw [insertRun_preserves_metric cmp key value t .visits (by decide) (by decide)]
  exact insRun_visits_le_height cmp key value t

theorem insertRun_comparisons_le_height (cmp : κ → κ → Measured Bool Nat)
    (key : κ) (value : ν) (t : Tree κ ν) :
    (insertRun cmp key value t).2 .comparisons ≤ 2 * Search.RedBlack.height t := by
  rw [insertRun_preserves_metric cmp key value t .comparisons (by decide) (by decide)]
  exact insRun_comparisons_le_height cmp key value t

theorem insertRun_comparatorWork_le_height (cmp : κ → κ → Measured Bool Nat)
    (key : κ) (value : ν) (t : Tree κ ν) (K : Nat)
    (local_bound : Search.RedBlack.ForallT
      (fun old _ => (cmp key old).2 ≤ K ∧ (cmp old key).2 ≤ K) t) :
    (insertRun cmp key value t).2 .comparatorWork ≤ 2 * K * Search.RedBlack.height t := by
  rw [insertRun_preserves_metric cmp key value t .comparatorWork (by decide) (by decide)]
  exact insRun_comparatorWork_le_height cmp key value t K local_bound

theorem insertRun_balanceCalls_le_height (cmp : κ → κ → Measured Bool Nat)
    (key : κ) (value : ν) (t : Tree κ ν) :
    (insertRun cmp key value t).2 .balanceCalls ≤ Search.RedBlack.height t := by
  rw [insertRun_preserves_metric cmp key value t .balanceCalls (by decide) (by decide)]
  exact insRun_balanceCalls_le_height cmp key value t

theorem insertRun_patternAttempts_le (cmp : κ → κ → Measured Bool Nat)
    (key : κ) (value : ν) (t : Tree κ ν) :
    (insertRun cmp key value t).2 .patternAttempts ≤
      5 * (insertRun cmp key value t).2 .balanceCalls := by
  rw [insertRun_preserves_metric cmp key value t .patternAttempts (by decide) (by decide),
    insertRun_preserves_metric cmp key value t .balanceCalls (by decide) (by decide)]
  exact insRun_patternAttempts_le cmp key value t

theorem insertRun_datatypeObservations_le (cmp : κ → κ → Measured Bool Nat)
    (key : κ) (value : ν) (t : Tree κ ν) :
    (insertRun cmp key value t).2 .datatypeObservations ≤
      17 * (insertRun cmp key value t).2 .balanceCalls := by
  rw [insertRun_preserves_metric cmp key value t .datatypeObservations (by decide) (by decide),
    insertRun_preserves_metric cmp key value t .balanceCalls (by decide) (by decide)]
  exact insRun_datatypeObservations_le cmp key value t

theorem insertRun_nodeConstructions_le_height (cmp : κ → κ → Measured Bool Nat)
    (key : κ) (value : ν) (t : Tree κ ν) :
    (insertRun cmp key value t).2 .nodeConstructions ≤ 3 * Search.RedBlack.height t + 2 := by
  rw [insertRun_nodeConstructions]
  have h := insRun_nodeConstructions_le_height cmp key value t
  omega

theorem insertRun_terminalNils_le (cmp : κ → κ → Measured Bool Nat)
    (key : κ) (value : ν) (t : Tree κ ν) : (insertRun cmp key value t).2 .terminalNils ≤ 1 := by
  rw [insertRun_preserves_metric cmp key value t .terminalNils (by decide) (by decide)]
  exact insRun_terminalNils_le cmp key value t

theorem insertRun_other (cmp : κ → κ → Measured Bool Nat) (key : κ) (value : ν)
    (t : Tree κ ν) (metric : Metric)
    (hL : metric ≠ .visits) (hQ : metric ≠ .comparisons) (hM : metric ≠ .comparatorWork)
    (hB : metric ≠ .balanceCalls) (hP : metric ≠ .patternAttempts)
    (hD : metric ≠ .datatypeObservations) (hA : metric ≠ .nodeConstructions)
    (hT : metric ≠ .terminalNils) (hR : metric ≠ .rootInspections) :
    (insertRun cmp key value t).2 metric = 0 := by
  rw [insertRun_preserves_metric cmp key value t metric hR hA]
  exact insRun_other cmp key value t metric hL hQ hM hB hP hD hA hT

theorem insertRun_unit_comparatorWork (ltb : κ → κ → Bool) (key : κ) (value : ν)
    (t : Tree κ ν) :
    (insertRun (unitComparator ltb) key value t).2 .comparatorWork =
      (insertRun (unitComparator ltb) key value t).2 .comparisons := by
  rw [insertRun_preserves_metric _ key value t .comparatorWork (by decide) (by decide),
    insertRun_preserves_metric _ key value t .comparisons (by decide) (by decide),
    insRun_comparatorWork, insRun_comparisons]
  exact lookupRun_unit_comparatorWork ltb key t

end Resources.RedBlack

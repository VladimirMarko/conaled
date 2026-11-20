import Applications.Resources.WorkloadBounds
import Applications.Resources.PositivePaths
import Applications.Resources.PositiveTrie.Traversal

/-!
# Actual forward-prefix map fold

Left subtree, optional root callback, then right subtree consume actual returned
prefixes and states. Outer coordinates count tree entries, callback invocations,
prefix-append entries and prefix wrappers. The callback observation is separate.
The ordered-list comparison is a theorem, not an executed enumeration.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.PositiveTrie.MapFold

open Search.PositiveTrie Numerals.PositiveArithmetic Numerals.PositivePaths Traversal

universe u v w
variable {α : Type u} {σ : Type v} {C : Type w}

abbrev Counts := Nat × (Nat × (Nat × Nat))
abbrev Cost (C : Type w) := Counts × C

def prefixRun [Zero C] (p branch : PosNum) : Measured PosNum (Cost C) :=
  reweight (fun cost => ((0, (0, cost)), 0)) (Resources.PositivePaths.appendRun p branch)

theorem prefixRun_value [Zero C] (p branch : PosNum) :
    (prefixRun (C := C) p branch).1 = append p branch := Resources.PositivePaths.appendRun_value p branch

theorem prefixRun_counts [Zero C] (p branch : PosNum) :
    (prefixRun (C := C) p branch).2.1 = (0, (0, (bitLength p, bitLength p - 1))) := by
  simp only [prefixRun, reweight, Resources.PositivePaths.appendRun_cost]

def payloadRun [Zero C] (callback : PosNum → α → σ → Measured σ C)
    (key : PosNum) (value : Option α) (state : σ) : Measured σ (Cost C) :=
  match value with
  | none => (state, ((0, (0, (0, 0))), 0))
  | some value =>
      let result := callback key value state
      (result.1, ((0, (1, (0, 0))), result.2))

theorem payloadRun_counts [Zero C] (callback : PosNum → α → σ → Measured σ C)
    (key : PosNum) (value : Option α) (state : σ) :
    (payloadRun callback key value state).2.1 = (0, (if value.isSome then 1 else 0, (0, 0))) := by
  cases value <;> rfl

def runFrom [Add C] [Zero C] (callback : PosNum → α → σ → Measured σ C) :
    SparseMap α → σ → PosNum → Measured σ (Cost C)
  | .nil, state, _ => (state, ((1, (0, (0, 0))), 0))
  | .node value left right, state, p =>
      bind ((), ((1, (0, (0, 0))), 0)) (fun _ =>
        bind (prefixRun p (.bit0 .one)) (fun leftKey =>
          bind (runFrom callback left state leftKey) (fun leftState =>
            bind (payloadRun callback p value leftState) (fun rootState =>
              bind (prefixRun p (.bit1 .one)) (fun rightKey =>
                runFrom callback right rootState rightKey)))))

def run [Add C] [Zero C] (callback : PosNum → α → σ → Measured σ C)
    (tree : SparseMap α) (state : σ) : Measured σ (Cost C) := runFrom callback tree state .one

theorem runFrom_value [Add C] [Zero C] (callback : PosNum → α → σ → Measured σ C)
    (tree : SparseMap α) (state : σ) (p : PosNum) :
    (runFrom callback tree state p).1 =
      SparseMap.foldFrom (fun key value state => (callback key value state).1) tree state p := by
  induction tree generalizing state p with
  | nil => rfl
  | node value left right ihl ihr =>
      cases value <;> simp only [runFrom, bind_value, prefixRun_value, payloadRun,
        SparseMap.foldFrom, ihl, ihr]

theorem run_value [Add C] [Zero C] (callback : PosNum → α → σ → Measured σ C)
    (tree : SparseMap α) (state : σ) :
    (run callback tree state).1 =
      SparseMap.fold (fun key value state => (callback key value state).1) tree state :=
  runFrom_value callback tree state .one

/-- The wrapper coordinate is identified additively before Nat subtraction. -/
theorem runFrom_counts_add [Add C] [Zero C] (callback : PosNum → α → σ → Measured σ C)
    (tree : SparseMap α) (state : σ) (p : PosNum) :
    let counts := (runFrom callback tree state p).2.1
    (counts.1, (counts.2.1, (counts.2.2.1, counts.2.2.2 + 2 * tree.numNodes))) =
      (2 * tree.numNodes + 1, (SparseMap.cardinal tree, (2 * prefixMass tree p, 2 * prefixMass tree p))) := by
  induction tree generalizing state p with
  | nil => simp [runFrom, prefixMass_nil, BinaryTree.numNodes, SparseMap.cardinal]
  | node value left right ihl ihr =>
      have hl := ihl state (append p (.bit0 .one))
      have hr := ihr (payloadRun callback p value (runFrom callback left state
        (append p (.bit0 .one))).1).1 (append p (.bit1 .one))
      simp only [Prod.mk.injEq] at hl hr
      have positive := bitLength_pos p
      simp only [runFrom, bind, Prod.fst_add, prefixRun_value, prefixRun_counts,
        payloadRun_counts, BinaryTree.numNodes, SparseMap.cardinal_node,
        prefixMass_node]
      ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

theorem runFrom_counts [Add C] [Zero C] (callback : PosNum → α → σ → Measured σ C)
    (tree : SparseMap α) (state : σ) (p : PosNum) :
    (runFrom callback tree state p).2.1 =
      (2 * tree.numNodes + 1, (SparseMap.cardinal tree,
        (2 * prefixMass tree p, 2 * (prefixMass tree p - tree.numNodes)))) := by
  have h := runFrom_counts_add callback tree state p
  have lower := numNodes_le_prefixMass tree p
  simp only [Prod.mk.injEq] at h
  ext <;> dsimp only <;> omega

theorem run_counts [Add C] [Zero C] (callback : PosNum → α → σ → Measured σ C)
    (tree : SparseMap α) (state : σ) :
    (run callback tree state).2.1 =
      (2 * tree.numNodes + 1, (SparseMap.cardinal tree,
        (2 * prefixMass tree .one, 2 * (prefixMass tree .one - tree.numNodes)))) :=
  runFrom_counts callback tree state .one

/-- Both the final state and the callback bill follow the actual ordered run. -/
theorem runFrom_callback [AddMonoid C] (callback : PosNum → α → σ → Measured σ C)
    (tree : SparseMap α) (state : σ) (p : PosNum) :
    ((runFrom callback tree state p).1, (runFrom callback tree state p).2.2) =
      Resources.run (fun entry state => callback entry.1 entry.2 state)
        (SparseMap.elementsFrom tree p) state := by
  induction tree generalizing state p with
  | nil => rfl
  | node value left right ihl ihr =>
      have lv (s : σ) (q : PosNum) := congrArg Prod.fst (ihl s q)
      have lo (s : σ) (q : PosNum) := congrArg Prod.snd (ihl s q)
      have rv (s : σ) (q : PosNum) := congrArg Prod.fst (ihr s q)
      have ro (s : σ) (q : PosNum) := congrArg Prod.snd (ihr s q)
      dsimp only at lv lo rv ro
      cases value <;> simp only [runFrom, bind, prefixRun, reweight,
        Resources.PositivePaths.appendRun_value, payloadRun, Prod.snd_add,
        zero_add, SparseMap.elementsFrom, Resources.run_append,
        Resources.run_cons, lv, lo, rv, ro]

theorem run_callback [AddMonoid C] (callback : PosNum → α → σ → Measured σ C)
    (tree : SparseMap α) (state : σ) :
    ((run callback tree state).1, (run callback tree state).2.2) =
      Resources.run (fun entry state => callback entry.1 entry.2 state)
        (SparseMap.elements tree) state := runFrom_callback callback tree state .one

theorem runFrom_invariant_on [AddMonoid C] (callback : PosNum → α → σ → Measured σ C)
    (allowed : PosNum × α → Prop) (I : σ → Prop)
    (closed : ∀ key value state, allowed (key, value) → I state → I (callback key value state).1)
    (tree : SparseMap α) (p : PosNum)
    (inputs : ∀ entry ∈ SparseMap.elementsFrom tree p, allowed entry)
    (state : σ) (initial : I state) : I (runFrom callback tree state p).1 := by
  have h := Resources.run_invariant_on (fun entry state => callback entry.1 entry.2 state)
    allowed I (fun entry state => closed entry.1 entry.2 state)
    (SparseMap.elementsFrom tree p) inputs state initial
  rw [← runFrom_callback] at h
  exact h

theorem runFrom_callback_work_le (callback : PosNum → α → σ → Measured σ Nat)
    (allowed : PosNum × α → Prop) (I : σ → Prop) (bound : Nat)
    (closed : ∀ key value state, allowed (key, value) → I state → I (callback key value state).1)
    (bounded : ∀ key value state, allowed (key, value) → I state → (callback key value state).2 ≤ bound)
    (tree : SparseMap α) (p : PosNum)
    (inputs : ∀ entry ∈ SparseMap.elementsFrom tree p, allowed entry)
    (state : σ) (initial : I state) :
    (runFrom callback tree state p).2.2 ≤ SparseMap.cardinal tree * bound := by
  have h := Resources.run_work_le_on (fun entry state => callback entry.1 entry.2 state)
    allowed I bound (fun entry state => closed entry.1 entry.2 state)
    (fun entry state => bounded entry.1 entry.2 state)
    (SparseMap.elementsFrom tree p) inputs state initial
  rw [← runFrom_callback, SparseMap.elementsFrom_eq_rawEntries, List.length_map,
    SparseMap.rawEntries_length] at h
  exact h

def outerWork (counts : Counts) : Nat := counts.1 + counts.2.1 + counts.2.2.1 + counts.2.2.2

theorem runFrom_outer_work [Add C] [Zero C] (callback : PosNum → α → σ → Measured σ C)
    (tree : SparseMap α) (state : σ) (p : PosNum) :
    outerWork (runFrom callback tree state p).2.1 = 4 * prefixMass tree p + SparseMap.cardinal tree + 1 := by
  have h := runFrom_counts_add callback tree state p
  simp only [Prod.mk.injEq] at h
  dsimp only [outerWork]
  omega

theorem run_outer_work_le [Add C] [Zero C] (callback : PosNum → α → σ → Measured σ C)
    {tree : SparseMap α} (normal : SparseMap.Normalized tree) (bits : Nat)
    (bounded : ∀ key value, SparseMap.find key tree = some value → bitLength key ≤ bits)
    (state : σ) : outerWork (run callback tree state).2.1 ≤
      4 * SparseMap.cardinal tree * bits ^ 2 + SparseMap.cardinal tree + 1 := by
  have h := map_prefixMass_one_le normal bits bounded
  rw [run, runFrom_outer_work]
  simpa only [Nat.mul_assoc] using
    Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left 4 h) (SparseMap.cardinal tree)) 1

theorem run_total_work_le (callback : PosNum → α → σ → Measured σ Nat)
    (allowed : PosNum × α → Prop) (I : σ → Prop) (bound : Nat)
    (closed : ∀ key value state, allowed (key, value) → I state → I (callback key value state).1)
    (bounded : ∀ key value state, allowed (key, value) → I state → (callback key value state).2 ≤ bound)
    {tree : SparseMap α} (normal : SparseMap.Normalized tree) (bits : Nat)
    (boundedBits : ∀ key value, SparseMap.find key tree = some value → bitLength key ≤ bits)
    (inputs : ∀ entry ∈ SparseMap.elements tree, allowed entry)
    (state : σ) (initial : I state) :
    outerWork (run callback tree state).2.1 + (run callback tree state).2.2 ≤
      4 * SparseMap.cardinal tree * bits ^ 2 + SparseMap.cardinal tree + 1 +
        SparseMap.cardinal tree * bound :=
  Nat.add_le_add (run_outer_work_le callback normal bits boundedBits state)
    (runFrom_callback_work_le callback allowed I bound closed bounded tree .one inputs state initial)

end Resources.PositiveTrie.MapFold

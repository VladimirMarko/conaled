import Applications.Resources.WorkloadBounds
import Applications.Resources.PositivePaths
import Applications.Resources.PositiveTrie.Traversal

/-!
# Actual reversed-prefix set fold

The source sequence is left, occupied root, right with actual returned states.
Two direct child-prefix wrappers are constructed at each raw node; only an
occupied root reverses its actual prefix and invokes the callback. Coordinates
are tree entries, callbacks, direct wrappers, reversal entries and wrappers.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.PositiveTrie.SetFold

open Search.PositiveTrie Numerals.PositiveArithmetic Numerals.PositivePaths Traversal

universe u v
variable {σ : Type u} {C : Type v}

abbrev Counts := Nat × (Nat × (Nat × (Nat × Nat)))
abbrev Cost (C : Type v) := Counts × C

def payloadRun [Add C] [Zero C] (callback : PosNum → σ → Measured σ C)
    (r : PosNum) (occupied : Bool) (state : σ) : Measured σ (Cost C) :=
  if occupied then
    bind (reweight (fun cost => ((0, (0, (0, cost))), 0)) (Resources.PositivePaths.reverseRun r))
      (fun key => reweight (fun observation => ((0, (1, (0, (0, 0)))), observation))
        (callback key state))
  else (state, ((0, (0, (0, (0, 0)))), 0))

theorem payloadRun_value [Add C] [Zero C] (callback : PosNum → σ → Measured σ C)
    (r : PosNum) (occupied : Bool) (state : σ) :
    (payloadRun callback r occupied state).1 =
      if occupied then (callback (reverse r) state).1 else state := by
  cases occupied <;> simp only [payloadRun, Bool.false_eq_true, ↓reduceIte, bind_value,
    reweight_value, Resources.PositivePaths.reverseRun_value]

theorem payloadRun_counts [Add C] [Zero C] (callback : PosNum → σ → Measured σ C)
    (r : PosNum) (occupied : Bool) (state : σ) :
    (payloadRun callback r occupied state).2.1 =
      (0, (if occupied then 1 else 0, (0,
        (if occupied then bitLength r else 0, if occupied then bitLength r - 1 else 0)))) := by
  cases occupied <;> simp only [payloadRun, Bool.false_eq_true, ↓reduceIte, bind, reweight,
    Resources.PositivePaths.reverseRun_cost, Prod.mk_add_mk,
    Nat.zero_add, Nat.add_zero]

def runFrom [Add C] [Zero C] (callback : PosNum → σ → Measured σ C) :
    KeySet → σ → PosNum → Measured σ (Cost C)
  | .nil, state, _ => (state, ((1, (0, (0, (0, 0)))), 0))
  | .node occupied left right, state, r =>
      bind ((), ((1, (0, (0, (0, 0)))), 0)) (fun _ =>
        bind (.bit0 r, ((0, (0, (1, (0, 0)))), 0)) (fun leftKey =>
          bind (runFrom callback left state leftKey) (fun leftState =>
            bind (payloadRun callback r occupied leftState) (fun rootState =>
              bind (.bit1 r, ((0, (0, (1, (0, 0)))), 0)) (fun rightKey =>
                runFrom callback right rootState rightKey)))))

def run [Add C] [Zero C] (callback : PosNum → σ → Measured σ C)
    (tree : KeySet) (state : σ) : Measured σ (Cost C) := runFrom callback tree state .one

theorem runFrom_value [Add C] [Zero C] (callback : PosNum → σ → Measured σ C)
    (tree : KeySet) (state : σ) (r : PosNum) :
    (runFrom callback tree state r).1 =
      KeySet.foldFrom (fun key state => (callback key state).1) tree state r := by
  induction tree generalizing state r with
  | nil => rfl
  | node occupied left right ihl ihr =>
      cases occupied <;> simp only [runFrom, bind_value, payloadRun_value,
        Bool.false_eq_true, ↓reduceIte, KeySet.foldFrom, ihl, ihr]

theorem run_value [Add C] [Zero C] (callback : PosNum → σ → Measured σ C)
    (tree : KeySet) (state : σ) :
    (run callback tree state).1 = KeySet.fold (fun key state => (callback key state).1) tree state :=
  runFrom_value callback tree state .one

theorem runFrom_counts_add [Add C] [Zero C] (callback : PosNum → σ → Measured σ C)
    (tree : KeySet) (state : σ) (r : PosNum) :
    let counts := (runFrom callback tree state r).2.1
    (counts.1, (counts.2.1, (counts.2.2.1,
      (counts.2.2.2.1, counts.2.2.2.2 + KeySet.cardinal tree)))) =
      (2 * tree.numNodes + 1, (KeySet.cardinal tree, (2 * tree.numNodes,
        (reversalMass tree r, reversalMass tree r)))) := by
  induction tree generalizing state r with
  | nil => simp [runFrom, reversalMass_nil, BinaryTree.numNodes, KeySet.cardinal]
  | node occupied left right ihl ihr =>
      have hl := ihl state (.bit0 r)
      have hr := ihr (payloadRun callback r occupied (runFrom callback left state (.bit0 r)).1).1 (.bit1 r)
      simp only [Prod.mk.injEq] at hl hr
      have positive := bitLength_pos r
      simp only [runFrom, bind, Prod.fst_add, payloadRun_counts, BinaryTree.numNodes,
        KeySet.cardinal_node, reversalMass_node]
      cases occupied <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;>
        ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

theorem runFrom_counts [Add C] [Zero C] (callback : PosNum → σ → Measured σ C)
    (tree : KeySet) (state : σ) (r : PosNum) :
    (runFrom callback tree state r).2.1 =
      (2 * tree.numNodes + 1, (KeySet.cardinal tree, (2 * tree.numNodes,
        (reversalMass tree r, reversalMass tree r - KeySet.cardinal tree)))) := by
  have h := runFrom_counts_add callback tree state r
  simp only [Prod.mk.injEq] at h
  ext <;> dsimp only <;> omega

theorem run_counts [Add C] [Zero C] (callback : PosNum → σ → Measured σ C)
    (tree : KeySet) (state : σ) :
    (run callback tree state).2.1 =
      (2 * tree.numNodes + 1, (KeySet.cardinal tree, (2 * tree.numNodes,
        (KeySet.keyMass tree, KeySet.keyMass tree - KeySet.cardinal tree)))) := by
  rw [run, runFrom_counts, reversalMass_one]

theorem runFrom_callback [AddMonoid C] (callback : PosNum → σ → Measured σ C)
    (tree : KeySet) (state : σ) (r : PosNum) :
    ((runFrom callback tree state r).1, (runFrom callback tree state r).2.2) =
      Resources.run callback ((KeySet.rawKeys tree).map (reverseAppend r)) state := by
  induction tree generalizing state r with
  | nil => rfl
  | node occupied left right ihl ihr =>
      have lv (s : σ) (q : PosNum) := congrArg Prod.fst (ihl s q)
      have lo (s : σ) (q : PosNum) := congrArg Prod.snd (ihl s q)
      have rv (s : σ) (q : PosNum) := congrArg Prod.fst (ihr s q)
      have ro (s : σ) (q : PosNum) := congrArg Prod.snd (ihr s q)
      dsimp only at lv lo rv ro
      cases occupied <;> simp only [runFrom, bind, payloadRun, reweight,
        Bool.false_eq_true, ↓reduceIte, Resources.PositivePaths.reverseRun_value,
        Prod.snd_add, zero_add, KeySet.rawKeys, List.map_append, List.map_cons,
        List.map_map, Function.comp_def, Resources.run_append, Resources.run_cons,
        lv, lo, rv, ro, reverseAppend, reverse]

theorem run_callback [AddMonoid C] (callback : PosNum → σ → Measured σ C)
    (tree : KeySet) (state : σ) :
    ((run callback tree state).1, (run callback tree state).2.2) =
      Resources.run callback (KeySet.elements tree) state := by
  simpa only [run, show reverseAppend .one = id from rfl, List.map_id, KeySet.elements_eq_rawKeys] using
    runFrom_callback callback tree state .one

theorem runFrom_invariant_on [AddMonoid C] (callback : PosNum → σ → Measured σ C)
    (allowed : PosNum → Prop) (I : σ → Prop)
    (closed : ∀ key state, allowed key → I state → I (callback key state).1)
    (tree : KeySet) (r : PosNum)
    (inputs : ∀ key ∈ (KeySet.rawKeys tree).map (reverseAppend r), allowed key)
    (state : σ) (initial : I state) : I (runFrom callback tree state r).1 := by
  have h := Resources.run_invariant_on callback allowed I closed
    ((KeySet.rawKeys tree).map (reverseAppend r)) inputs state initial
  rw [← runFrom_callback] at h
  exact h

theorem runFrom_callback_work_le (callback : PosNum → σ → Measured σ Nat)
    (allowed : PosNum → Prop) (I : σ → Prop) (bound : Nat)
    (closed : ∀ key state, allowed key → I state → I (callback key state).1)
    (bounded : ∀ key state, allowed key → I state → (callback key state).2 ≤ bound)
    (tree : KeySet) (r : PosNum)
    (inputs : ∀ key ∈ (KeySet.rawKeys tree).map (reverseAppend r), allowed key)
    (state : σ) (initial : I state) :
    (runFrom callback tree state r).2.2 ≤ KeySet.cardinal tree * bound := by
  have h := Resources.run_work_le_on callback allowed I bound closed bounded
    ((KeySet.rawKeys tree).map (reverseAppend r)) inputs state initial
  rw [← runFrom_callback, List.length_map, KeySet.rawKeys_length] at h
  exact h

def outerWork (counts : Counts) : Nat :=
  counts.1 + counts.2.1 + counts.2.2.1 + counts.2.2.2.1 + counts.2.2.2.2

theorem runFrom_outer_work [Add C] [Zero C] (callback : PosNum → σ → Measured σ C)
    (tree : KeySet) (state : σ) (r : PosNum) :
    outerWork (runFrom callback tree state r).2.1 = 4 * tree.numNodes + 2 * reversalMass tree r + 1 := by
  have h := runFrom_counts_add callback tree state r
  simp only [Prod.mk.injEq] at h
  dsimp only [outerWork]
  omega

theorem run_outer_work_le [Add C] [Zero C] (callback : PosNum → σ → Measured σ C)
    {tree : KeySet} (normal : KeySet.Normalized tree) (bits : Nat)
    (bounded : ∀ key, KeySet.mem key tree = true → bitLength key ≤ bits) (state : σ) :
    outerWork (run callback tree state).2.1 ≤ 6 * KeySet.cardinal tree * bits + 1 := by
  have hn := KeySet.numNodes_le_cardinal_mul normal bits bounded
  have hm := KeySet.keyMass_le_cardinal_mul tree bits bounded
  rw [run, runFrom_outer_work, reversalMass_one]
  simp only [Nat.mul_assoc]
  omega

theorem run_total_work_le (callback : PosNum → σ → Measured σ Nat)
    (allowed : PosNum → Prop) (I : σ → Prop) (bound : Nat)
    (closed : ∀ key state, allowed key → I state → I (callback key state).1)
    (bounded : ∀ key state, allowed key → I state → (callback key state).2 ≤ bound)
    {tree : KeySet} (normal : KeySet.Normalized tree) (bits : Nat)
    (boundedBits : ∀ key, KeySet.mem key tree = true → bitLength key ≤ bits)
    (inputs : ∀ key ∈ KeySet.elements tree, allowed key) (state : σ) (initial : I state) :
    outerWork (run callback tree state).2.1 + (run callback tree state).2.2 ≤
      6 * KeySet.cardinal tree * bits + 1 + KeySet.cardinal tree * bound := by
  have hc := runFrom_callback_work_le callback allowed I bound closed bounded tree .one
    (by simpa only [show reverseAppend .one = id from rfl, List.map_id,
      KeySet.elements_eq_rawKeys] using inputs) state initial
  exact Nat.add_le_add (run_outer_work_le callback normal bits boundedBits state) hc

end Resources.PositiveTrie.SetFold

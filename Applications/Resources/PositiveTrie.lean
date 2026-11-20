import Applications.Resources.Measured
import Applications.Resources.CollisionWork
import Applications.Search.PositiveTrie.Basic
import Applications.Search.Collisions.Representations
import Applications.Numerals.PositiveArithmetic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.Dedup

/-!
# Source calls and node constructions for positive tries

The two cost coordinates count entered raw calls and constructed BinaryTree
nodes. Lookup stops at nil; insertion follows every key constructor and builds
one node per call. Recursive branches consume their actual measured child
results through `bind`. Table-product wrappers have zero extra tariff.

These are declared source events. They do not include encoding, parsing,
printing, native allocation, garbage collection or elapsed time.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.PositiveTrie

universe u

variable {ν : Type u}

open Numerals.PositiveArithmetic

/-- Entered recursive calls, then BinaryTree node-construction events. -/
abbrev Cost := Nat × Nat

def lookRun (default : ν) : PosNum → BinaryTree ν → Measured ν Cost
  | _, .nil => (default, (1, 0))
  | .one, .node value _ _ => (value, (1, 0))
  | .bit0 key, .node _ left _ =>
      bind ((), (1, 0)) (fun _ => lookRun default key left)
  | .bit1 key, .node _ _ right =>
      bind ((), (1, 0)) (fun _ => lookRun default key right)

theorem lookRun_nil (default : ν) (key : PosNum) :
    lookRun default key .nil = (default, (1, 0)) := by
  cases key <;> rfl

theorem lookRun_one_node (default value : ν) (left right : BinaryTree ν) :
    lookRun default .one (.node value left right) = (value, (1, 0)) := rfl

theorem lookRun_bit0_node (default value : ν) (key : PosNum) (left right : BinaryTree ν) :
    lookRun default (.bit0 key) (.node value left right) =
      bind ((), (1, 0)) (fun _ => lookRun default key left) := rfl

theorem lookRun_bit1_node (default value : ν) (key : PosNum) (left right : BinaryTree ν) :
    lookRun default (.bit1 key) (.node value left right) =
      bind ((), (1, 0)) (fun _ => lookRun default key right) := rfl

theorem lookRun_value (default : ν) (key : PosNum) (tree : BinaryTree ν) :
    (lookRun default key tree).1 = Search.PositiveTrie.look default key tree := by
  induction key generalizing tree with
  | one => cases tree <;> rfl
  | bit0 key ih =>
      cases tree with
      | nil => rfl
      | node value left right => exact ih left
  | bit1 key ih =>
      cases tree with
      | nil => rfl
      | node value left right => exact ih right

theorem lookRun_calls_le (default : ν) (key : PosNum) (tree : BinaryTree ν) :
    (lookRun default key tree).2.1 ≤ bitLength key := by
  induction key generalizing tree with
  | one => cases tree <;> exact Nat.le_refl 1
  | bit0 key ih =>
      cases tree with
      | nil => exact Nat.le_add_left 1 _
      | node value left right =>
          simpa only [lookRun, bind, Prod.fst_add, bitLength_bit0, Nat.add_comm] using
            Nat.add_le_add_left (ih left) 1
  | bit1 key ih =>
      cases tree with
      | nil => exact Nat.le_add_left 1 _
      | node value left right =>
          simpa only [lookRun, bind, Prod.fst_add, bitLength_bit1, Nat.add_comm] using
            Nat.add_le_add_left (ih right) 1

theorem lookRun_constructions (default : ν) (key : PosNum) (tree : BinaryTree ν) :
    (lookRun default key tree).2.2 = 0 := by
  induction key generalizing tree with
  | one => cases tree <;> rfl
  | bit0 key ih => cases tree <;> simp only [lookRun, bind, Prod.snd_add, Nat.zero_add, ih]
  | bit1 key ih => cases tree <;> simp only [lookRun, bind, Prod.snd_add, Nat.zero_add, ih]

def lookupRun (key : PosNum) (table : Search.PositiveTrie.Table ν) : Measured ν Cost :=
  lookRun table.1 key table.2

theorem lookupRun_value (key : PosNum) (table : Search.PositiveTrie.Table ν) :
    (lookupRun key table).1 = Search.PositiveTrie.lookup key table :=
  lookRun_value table.1 key table.2

theorem lookupRun_calls_le (key : PosNum) (table : Search.PositiveTrie.Table ν) :
    (lookupRun key table).2.1 ≤ bitLength key := lookRun_calls_le table.1 key table.2

theorem lookupRun_calls_le_log (key : PosNum) (table : Search.PositiveTrie.Table ν) :
    (lookupRun key table).2.1 ≤ Nat.log2 (Numerals.PositiveKeys.numeric key) + 1 := by
  rw [← bitLength_eq_log2]
  exact lookupRun_calls_le key table

theorem lookupRun_constructions (key : PosNum) (table : Search.PositiveTrie.Table ν) :
    (lookupRun key table).2.2 = 0 := lookRun_constructions table.1 key table.2

/-- Charge entry before the child call and construction after its actual result. -/
def insRun (default : ν) : PosNum → ν → BinaryTree ν → Measured (BinaryTree ν) Cost
  | .one, value, .nil => (.node value .nil .nil, (1, 1))
  | .bit0 key, value, .nil =>
      bind ((), (1, 0)) (fun _ =>
        bind (insRun default key value .nil) (fun left => (.node default left .nil, (0, 1))))
  | .bit1 key, value, .nil =>
      bind ((), (1, 0)) (fun _ =>
        bind (insRun default key value .nil) (fun right => (.node default .nil right, (0, 1))))
  | .one, value, .node _ left right => (.node value left right, (1, 1))
  | .bit0 key, value, .node old left right =>
      bind ((), (1, 0)) (fun _ =>
        bind (insRun default key value left) (fun next => (.node old next right, (0, 1))))
  | .bit1 key, value, .node old left right =>
      bind ((), (1, 0)) (fun _ =>
        bind (insRun default key value right) (fun next => (.node old left next, (0, 1))))

theorem insRun_value (default : ν) (key : PosNum) (value : ν) (tree : BinaryTree ν) :
    (insRun default key value tree).1 = Search.PositiveTrie.ins default key value tree := by
  induction key generalizing tree with
  | one => cases tree <;> rfl
  | bit0 key ih => cases tree <;> simp only [insRun, bind_value, Search.PositiveTrie.ins, ih]
  | bit1 key ih => cases tree <;> simp only [insRun, bind_value, Search.PositiveTrie.ins, ih]

theorem insRun_cost (default : ν) (key : PosNum) (value : ν) (tree : BinaryTree ν) :
    (insRun default key value tree).2 = (bitLength key, bitLength key) := by
  induction key generalizing tree with
  | one => cases tree <;> rfl
  | bit0 key ih =>
      cases tree <;> simp only [insRun, bind, ih, bitLength_bit0, Prod.mk_add_mk,
        Nat.zero_add, Nat.add_comm]
  | bit1 key ih =>
      cases tree <;> simp only [insRun, bind, ih, bitLength_bit1, Prod.mk_add_mk,
        Nat.zero_add, Nat.add_comm]

theorem insRun_calls (default : ν) (key : PosNum) (value : ν) (tree : BinaryTree ν) :
    (insRun default key value tree).2.1 = bitLength key :=
  congrArg Prod.fst (insRun_cost default key value tree)

theorem insRun_constructions (default : ν) (key : PosNum) (value : ν) (tree : BinaryTree ν) :
    (insRun default key value tree).2.2 = bitLength key :=
  congrArg Prod.snd (insRun_cost default key value tree)

def insertRun (key : PosNum) (value : ν) (table : Search.PositiveTrie.Table ν) :
    Measured (Search.PositiveTrie.Table ν) Cost :=
  bind (insRun table.1 key value table.2) (fun tree => pure (table.1, tree))

theorem insertRun_value (key : PosNum) (value : ν) (table : Search.PositiveTrie.Table ν) :
    (insertRun key value table).1 = Search.PositiveTrie.insert key value table := by
  simp only [insertRun, bind_value, pure, Search.PositiveTrie.insert, insRun_value]

theorem insertRun_default (key : PosNum) (value : ν) (table : Search.PositiveTrie.Table ν) :
    (insertRun key value table).1.1 = table.1 := by
  rw [insertRun_value]
  rfl

theorem insertRun_cost (key : PosNum) (value : ν) (table : Search.PositiveTrie.Table ν) :
    (insertRun key value table).2 = (bitLength key, bitLength key) := by
  simpa only [insertRun, bind, pure, add_zero] using insRun_cost table.1 key value table.2

theorem insertRun_calls (key : PosNum) (value : ν) (table : Search.PositiveTrie.Table ν) :
    (insertRun key value table).2.1 = bitLength key :=
  congrArg Prod.fst (insertRun_cost key value table)

theorem insertRun_constructions (key : PosNum) (value : ν)
    (table : Search.PositiveTrie.Table ν) :
    (insertRun key value table).2.2 = bitLength key :=
  congrArg Prod.snd (insertRun_cost key value table)

/-- The written path is fully materialized, so its next lookup visits every bit. -/
theorem lookRun_ins_cost (default : ν) (key : PosNum) (value : ν) (tree : BinaryTree ν) :
    (lookRun default key (Search.PositiveTrie.ins default key value tree)).2 =
      (bitLength key, 0) := by
  induction key generalizing tree with
  | one => cases tree <;> rfl
  | bit0 key ih =>
      cases tree <;> simp only [Search.PositiveTrie.ins, lookRun, bind, ih,
        bitLength_bit0, Prod.mk_add_mk, Nat.add_zero, Nat.add_comm]
  | bit1 key ih =>
      cases tree <;> simp only [Search.PositiveTrie.ins, lookRun, bind, ih,
        bitLength_bit1, Prod.mk_add_mk, Nat.add_zero, Nat.add_comm]

theorem lookupRun_insertRun_cost (key : PosNum) (value : ν)
    (table : Search.PositiveTrie.Table ν) :
    (lookupRun key (insertRun key value table).1).2 = (bitLength key, 0) := by
  rw [insertRun_value]
  exact lookRun_ins_cost table.1 key value table.2

theorem lookupRun_insertRun_value (key : PosNum) (value : ν)
    (table : Search.PositiveTrie.Table ν) :
    (lookupRun key (insertRun key value table).1).1 = value := by
  rw [lookupRun_value, insertRun_value]
  exact Search.PositiveTrie.lookup_insert_same key value table

theorem insert_lookup_value (key : PosNum) (value : ν) (table : Search.PositiveTrie.Table ν) :
    (bind (insertRun key value table) (lookupRun key)).1 = value :=
  lookupRun_insertRun_value key value table

theorem insert_lookup_cost (key : PosNum) (value : ν) (table : Search.PositiveTrie.Table ν) :
    (bind (insertRun key value table) (lookupRun key)).2 =
      (2 * bitLength key, bitLength key) := by
  simp only [bind, insertRun_cost, lookupRun_insertRun_cost, Prod.mk_add_mk,
    Nat.add_zero, two_mul]

theorem insRun_nil_numNodes (default : ν) (key : PosNum) (value : ν) :
    ((insRun default key value .nil).1).numNodes = bitLength key := by
  induction key with
  | one => rfl
  | bit0 key ih =>
      simp only [insRun, bind_value, BinaryTree.numNodes, ih, bitLength_bit0, Nat.add_zero]
  | bit1 key ih =>
      simp only [insRun, bind_value, BinaryTree.numNodes, ih, bitLength_bit1, Nat.zero_add]

/-- The source all-left key family O^h(H). -/
def longKey : Nat → PosNum
  | 0 => .one
  | h + 1 => .bit0 (longKey h)

theorem longKey_numeric (h : Nat) : Numerals.PositiveKeys.numeric (longKey h) = 2 ^ h := by
  induction h with
  | zero => rfl
  | succ h ih =>
      rw [longKey, Numerals.PositiveKeys.numeric_bit0, ih, Nat.pow_succ]
      simp only [Nat.zero_add, Nat.mul_comm]

theorem longKey_bitLength (h : Nat) : bitLength (longKey h) = h + 1 := by
  induction h with
  | zero => rfl
  | succ h ih => rw [longKey, bitLength_bit0, ih]

theorem longKey_empty_insert (default value : ν) (h : Nat) :
    (insertRun (longKey h) value (Search.PositiveTrie.empty default)).2 = (h + 1, h + 1) := by
  rw [insertRun_cost, longKey_bitLength]

theorem longKey_populated_lookup (default value : ν) (h : Nat) :
    (lookupRun (longKey h)
      (insertRun (longKey h) value (Search.PositiveTrie.empty default)).1).2 = (h + 1, 0) := by
  rw [lookupRun_insertRun_cost, longKey_bitLength]

theorem longKey_insert_numNodes (default value : ν) (h : Nat) :
    ((insertRun (longKey h) value (Search.PositiveTrie.empty default)).1.2).numNodes = h + 1 := by
  change ((insRun default (longKey h) value .nil).1).numNodes = h + 1
  rw [insRun_nil_numNodes, longKey_bitLength]

theorem longKey_single_distinct (h : Nat) : ([longKey h].dedup).length = 1 := by
  simp

/-- One distinct explicitly written key does not bound the native-positive path. -/
theorem singleton_lookup_unbounded (bound : Nat) :
    ∃ key : PosNum, ([key].dedup).length = 1 ∧
      bound < (lookupRun key (insertRun key true (Search.PositiveTrie.empty false)).1).2.1 := by
  refine ⟨longKey bound, longKey_single_distinct bound, ?_⟩
  rw [longKey_populated_lookup]
  exact Nat.lt_succ_self bound

/-! ## The existing common collision client -/

/-- Trie calls/constructions, unary counter calls, loop steps, and terminal calls. -/
abbrev CollisionCost := Cost × (Nat × Nat × Nat)

def calls : CollisionCost →+ Nat where
  toFun cost := cost.1.1
  map_zero' := rfl
  map_add' _ _ := rfl

def constructions : CollisionCost →+ Nat where
  toFun cost := cost.1.2
  map_zero' := rfl
  map_add' _ _ := rfl

def counterCalls : CollisionCost →+ Nat where
  toFun cost := cost.2.1
  map_zero' := rfl
  map_add' _ _ := rfl

def loopSteps : CollisionCost →+ Nat where
  toFun cost := cost.2.2.1
  map_zero' := rfl
  map_add' _ _ := rfl

def terminalCalls : CollisionCost →+ Nat where
  toFun cost := cost.2.2.2
  map_zero' := rfl
  map_add' _ _ := rfl

def trieCost : Cost →+ CollisionCost where
  toFun cost := (cost, (0, (0, 0)))
  map_zero' := rfl
  map_add' _ _ := rfl

def counterCost : Nat →+ CollisionCost where
  toFun cost := ((0, 0), (cost, (0, 0)))
  map_zero' := rfl
  map_add' _ _ := rfl

def readRun (key : PosNum) (table : Search.PositiveTrie.Table Bool) :
    Measured Bool CollisionCost := reweight trieCost (lookupRun key table)

def writeRun (key : PosNum) (value : Bool) (table : Search.PositiveTrie.Table Bool) :
    Measured (Search.PositiveTrie.Table Bool) CollisionCost :=
  reweight trieCost (insertRun key value table)

/-- The source first-operand-recursive addition is exactly 1+c, not c+1. -/
def incrementRun (counter : Nat) : Measured Nat CollisionCost :=
  reweight counterCost (CollisionWork.unaryAddRun 1 counter)

theorem incrementRun_value (counter : Nat) : (incrementRun counter).1 = 1 + counter :=
  CollisionWork.unaryAddRun_value 1 counter

theorem incrementRun_cost (counter : Nat) : (incrementRun counter).2 = counterCost 2 := by
  change counterCost (CollisionWork.unaryAddRun 1 counter).2 = counterCost 2
  rw [CollisionWork.unaryAddRun_cost]

def loopTick : CollisionCost := ((0, 0), (0, (1, 0)))

def terminalTick : CollisionCost := ((0, 0), (0, (0, 1)))

abbrev stepRun : PosNum → Nat × Search.PositiveTrie.Table Bool →
    Measured (Nat × Search.PositiveTrie.Table Bool) CollisionCost :=
  CollisionWork.step readRun writeRun incrementRun loopTick

/-- Configure the common executor; the trie instance adds no independent loop. -/
def collisionRun (keys : List PosNum) (state : Nat × Search.PositiveTrie.Table Bool) :
    Measured (Nat × Search.PositiveTrie.Table Bool) CollisionCost :=
  CollisionWork.run readRun writeRun incrementRun loopTick terminalTick keys state

theorem stepRun_cost_true (key : PosNum) (state : Nat × Search.PositiveTrie.Table Bool)
    (seen : (lookupRun key state.2).1 = true) :
    (stepRun key state).2 =
      loopTick + (trieCost (lookupRun key state.2).2 + counterCost 2) := by
  rw [stepRun, CollisionWork.step_cost_true readRun writeRun incrementRun loopTick key state seen,
    incrementRun_cost]
  rfl

theorem stepRun_cost_false (key : PosNum) (state : Nat × Search.PositiveTrie.Table Bool)
    (fresh : (lookupRun key state.2).1 = false) :
    (stepRun key state).2 =
      loopTick + (trieCost (lookupRun key state.2).2 + trieCost (insertRun key true state.2).2) :=
  CollisionWork.step_cost_false readRun writeRun incrementRun loopTick key state fresh

theorem stepRun_calls_le (key : PosNum) (state : Nat × Search.PositiveTrie.Table Bool) :
    calls (stepRun key state).2 ≤ 2 * bitLength key := by
  have read_bound := lookupRun_calls_le key state.2
  cases seen : (lookupRun key state.2).1 with
  | false =>
      rw [stepRun_cost_false key state seen]
      change 0 + ((lookupRun key state.2).2.1 + (insertRun key true state.2).2.1) ≤ _
      rw [insertRun_calls, Nat.zero_add]
      omega
  | true =>
      rw [stepRun_cost_true key state seen]
      change 0 + ((lookupRun key state.2).2.1 + 0) ≤ _
      simp only [Nat.zero_add, Nat.add_zero]
      omega

theorem stepRun_constructions_le (key : PosNum) (state : Nat × Search.PositiveTrie.Table Bool) :
    constructions (stepRun key state).2 ≤ bitLength key := by
  cases seen : (lookupRun key state.2).1 with
  | false =>
      rw [stepRun_cost_false key state seen]
      change 0 + ((lookupRun key state.2).2.2 + (insertRun key true state.2).2.2) ≤ _
      rw [lookupRun_constructions, insertRun_constructions]
      simp only [Nat.zero_add, Nat.le_refl]
  | true =>
      rw [stepRun_cost_true key state seen]
      change 0 + ((lookupRun key state.2).2.2 + 0) ≤ _
      rw [lookupRun_constructions]
      exact Nat.zero_le _

theorem stepRun_counterCalls (key : PosNum) (state : Nat × Search.PositiveTrie.Table Bool) :
    counterCalls (stepRun key state).2 = if (lookupRun key state.2).1 then 2 else 0 := by
  cases seen : (lookupRun key state.2).1 with
  | false => rw [stepRun_cost_false key state seen]; rfl
  | true => rw [stepRun_cost_true key state seen]; rfl

theorem stepRun_counter (key : PosNum) (state : Nat × Search.PositiveTrie.Table Bool) :
    (stepRun key state).1.1 =
      if (lookupRun key state.2).1 then 1 + state.1 else state.1 := by
  cases seen : (lookupRun key state.2).1 with
  | false =>
      rw [stepRun, CollisionWork.step_of_false readRun writeRun incrementRun loopTick key state seen]
      rfl
  | true =>
      rw [stepRun, CollisionWork.step_of_true readRun writeRun incrementRun loopTick key state seen]
      exact incrementRun_value state.1

theorem stepRun_counter_balance (key : PosNum) (state : Nat × Search.PositiveTrie.Table Bool) :
    counterCalls (stepRun key state).2 + 2 * state.1 = 2 * (stepRun key state).1.1 := by
  rw [stepRun_counterCalls, stepRun_counter]
  split <;> omega

theorem stepRun_loopSteps (key : PosNum) (state : Nat × Search.PositiveTrie.Table Bool) :
    loopSteps (stepRun key state).2 = 1 := by
  cases seen : (lookupRun key state.2).1 with
  | false => rw [stepRun_cost_false key state seen]; rfl
  | true => rw [stepRun_cost_true key state seen]; rfl

theorem stepRun_terminalCalls (key : PosNum) (state : Nat × Search.PositiveTrie.Table Bool) :
    terminalCalls (stepRun key state).2 = 0 := by
  cases seen : (lookupRun key state.2).1 with
  | false => rw [stepRun_cost_false key state seen]; rfl
  | true => rw [stepRun_cost_true key state seen]; rfl

theorem collisionRun_nil (state : Nat × Search.PositiveTrie.Table Bool) :
    collisionRun [] state = (state, terminalTick) :=
  CollisionWork.run_nil readRun writeRun incrementRun loopTick terminalTick state

theorem collisionRun_cons (key : PosNum) (keys : List PosNum)
    (state : Nat × Search.PositiveTrie.Table Bool) :
    collisionRun (key :: keys) state = bind (stepRun key state) (collisionRun keys) :=
  CollisionWork.run_cons readRun writeRun incrementRun loopTick terminalTick key keys state

theorem collisionRun_value (keys : List PosNum) (state : Nat × Search.PositiveTrie.Table Bool) :
    (collisionRun keys state).1 = Search.Collisions.run (Search.PositiveTrie.ops false) keys state :=
  CollisionWork.run_value (Search.PositiveTrie.ops false) readRun writeRun incrementRun
    loopTick terminalTick lookupRun_value (fun key table => insertRun_value key true table)
    (fun counter => (incrementRun_value counter).trans (Nat.add_comm 1 counter)) keys state

theorem collisionRun_source (keys : List PosNum) (counter : Nat)
    (table : Search.PositiveTrie.Table Bool) :
    (collisionRun keys (counter, table)).1.1 = Search.Collisions.FastEnough.loop keys counter table := by
  rw [collisionRun_value]
  exact (Search.Collisions.FastEnough.loop_common keys counter table).symm

theorem collisionRun_calls_le (keys : List PosNum) (state : Nat × Search.PositiveTrie.Table Bool) :
    calls (collisionRun keys state).2 ≤ 2 * (keys.map bitLength).sum := by
  have bound := CollisionWork.run_cost_le_sum readRun writeRun incrementRun loopTick terminalTick
    calls (fun key => 2 * bitLength key) (fun _ => True) (by intros; trivial)
    (fun key state _ => stepRun_calls_le key state) keys state trivial
  simpa only [collisionRun, List.sum_map_mul_left, show calls terminalTick = 0 from rfl,
    Nat.add_zero] using bound

theorem collisionRun_constructions_le (keys : List PosNum)
    (state : Nat × Search.PositiveTrie.Table Bool) :
    constructions (collisionRun keys state).2 ≤ (keys.map bitLength).sum := by
  have bound := CollisionWork.run_cost_le_sum readRun writeRun incrementRun loopTick terminalTick
    constructions bitLength (fun _ => True) (by intros; trivial)
    (fun key state _ => stepRun_constructions_le key state) keys state trivial
  simpa only [collisionRun, show constructions terminalTick = 0 from rfl, Nat.add_zero] using bound

theorem collisionRun_counterCalls_le (keys : List PosNum)
    (state : Nat × Search.PositiveTrie.Table Bool) :
    counterCalls (collisionRun keys state).2 ≤ 2 * keys.length := by
  have bound := CollisionWork.run_counter_cost_le readRun writeRun incrementRun loopTick terminalTick
    counterCalls (fun _ : Nat => 0) 2 (by intros; rfl) (by intros; rfl) rfl rfl
    (by
      intro counter
      change (CollisionWork.unaryAddRun 1 counter).2 + 0 = 0 + 2
      rw [CollisionWork.unaryAddRun_cost]) keys state
  simpa only [collisionRun, Nat.zero_add] using bound

theorem collisionRun_counter_balance (keys : List PosNum)
    (state : Nat × Search.PositiveTrie.Table Bool) :
    counterCalls (collisionRun keys state).2 + 2 * state.1 =
      2 * (collisionRun keys state).1.1 := by
  induction keys generalizing state with
  | nil => rw [collisionRun_nil]; exact Nat.zero_add _
  | cons key keys ih =>
      rw [collisionRun_cons]
      simp only [bind, map_add]
      have first := stepRun_counter_balance key state
      have rest := ih (stepRun key state).1
      omega

theorem collisionRun_loopSteps (keys : List PosNum)
    (state : Nat × Search.PositiveTrie.Table Bool) :
    loopSteps (collisionRun keys state).2 = keys.length := by
  have exact_count := CollisionWork.run_constant_observation readRun writeRun incrementRun
    loopTick terminalTick loopSteps 1 stepRun_loopSteps keys state
  simpa only [collisionRun, Nat.one_mul, show loopSteps terminalTick = 0 from rfl,
    Nat.add_zero] using exact_count

theorem collisionRun_terminalCalls (keys : List PosNum)
    (state : Nat × Search.PositiveTrie.Table Bool) :
    terminalCalls (collisionRun keys state).2 = 1 := by
  have exact_count := CollisionWork.run_constant_observation readRun writeRun incrementRun
    loopTick terminalTick terminalCalls 0 stepRun_terminalCalls keys state
  simpa only [collisionRun, Nat.zero_mul, show terminalCalls terminalTick = 1 from rfl,
    Nat.zero_add] using exact_count

def collisionsRun (keys : List PosNum) : Measured Nat CollisionCost :=
  bind (collisionRun keys (0, Search.PositiveTrie.empty false)) (fun state => pure state.1)

theorem collisionsRun_value (keys : List PosNum) :
    (collisionsRun keys).1 = Search.Collisions.count keys := by
  change (collisionRun keys (0, Search.PositiveTrie.empty false)).1.1 = _
  rw [collisionRun_source]
  exact Search.Collisions.FastEnough.collisions_correct keys

theorem collisionsRun_cost (keys : List PosNum) :
    (collisionsRun keys).2 = (collisionRun keys (0, Search.PositiveTrie.empty false)).2 := by
  simp only [collisionsRun, bind, pure, add_zero]

theorem collisionsRun_counterCalls (keys : List PosNum) :
    counterCalls (collisionsRun keys).2 = 2 * Search.Collisions.count keys := by
  have balance := collisionRun_counter_balance keys (0, Search.PositiveTrie.empty false)
  change counterCalls (collisionRun keys (0, Search.PositiveTrie.empty false)).2 + 2 * 0 =
    2 * (collisionsRun keys).1 at balance
  rw [Nat.mul_zero, Nat.add_zero, collisionsRun_value] at balance
  rw [collisionsRun_cost]
  exact balance

/-! ## The sum of the declared event tariffs -/

def totalWork : CollisionCost →+ Nat :=
  calls + constructions + counterCalls + loopSteps + terminalCalls

theorem collisionRun_totalWork_le (keys : List PosNum)
    (state : Nat × Search.PositiveTrie.Table Bool) :
    totalWork (collisionRun keys state).2 ≤
      3 * (keys.map bitLength).sum + 3 * keys.length + 1 := by
  have call_bound := collisionRun_calls_le keys state
  have node_bound := collisionRun_constructions_le keys state
  have counter_bound := collisionRun_counterCalls_le keys state
  have loops := collisionRun_loopSteps keys state
  have terminal := collisionRun_terminalCalls keys state
  change calls (collisionRun keys state).2 + constructions (collisionRun keys state).2 +
    counterCalls (collisionRun keys state).2 + loopSteps (collisionRun keys state).2 +
    terminalCalls (collisionRun keys state).2 ≤ _
  rw [loops, terminal]
  omega

theorem collisionsRun_totalWork_le (keys : List PosNum) :
    totalWork (collisionsRun keys).2 ≤
      3 * (keys.map bitLength).sum + 3 * keys.length + 1 := by
  rw [collisionsRun_cost]
  exact collisionRun_totalWork_le keys _

/-- Only the keys actually present in the input need the supplied bit bound. -/
theorem collisionRun_totalWork_le_of_bitLength_le (keys : List PosNum)
    (state : Nat × Search.PositiveTrie.Table Bool) (B : Nat)
    (bounded : ∀ key ∈ keys, bitLength key ≤ B) :
    totalWork (collisionRun keys state).2 ≤ 3 * keys.length * (B + 1) + 1 := by
  have sum_bound : (keys.map bitLength).sum ≤ keys.length * B := by
    have bound := List.sum_le_length_nsmul (keys.map bitLength) B (by
      intro bits inside
      obtain ⟨key, member, rfl⟩ := List.mem_map.mp inside
      exact bounded key member)
    simpa only [List.length_map, nsmul_eq_mul, Nat.cast_id] using bound
  calc
    totalWork (collisionRun keys state).2 ≤
        3 * (keys.map bitLength).sum + 3 * keys.length + 1 := collisionRun_totalWork_le keys state
    _ ≤ 3 * (keys.length * B) + 3 * keys.length + 1 := by omega
    _ = 3 * keys.length * (B + 1) + 1 := by
      simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]

theorem collisionsRun_totalWork_le_of_bitLength_le (keys : List PosNum) (B : Nat)
    (bounded : ∀ key ∈ keys, bitLength key ≤ B) :
    totalWork (collisionsRun keys).2 ≤ 3 * keys.length * (B + 1) + 1 := by
  rw [collisionsRun_cost]
  exact collisionRun_totalWork_le_of_bitLength_le keys _ B bounded

end Resources.PositiveTrie

import Applications.Resources.RedBlackWorkload
import Applications.Resources.Potential
import Applications.Resources.CollisionWork
import Applications.Resources.PositiveCounter
import Applications.Resources.CollisionHistory
import Applications.Search.Collisions.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Log

/-!
# Collision counting with the accepted red-black operations

The table work retains the accepted operation observations and their prices.
Distinct-key bounds follow from actual BST enumeration and a finite set of
possible input keys; input length is not substituted for that cardinality.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.CollisionRedBlack

universe u v
variable {κ : Type u} {ν : Type v}

open Search.RedBlack (Tree)

private theorem elements_length (tree : Tree κ ν) :
    (Search.RedBlack.elements tree).length = tree.size := by
  induction tree with
  | nil => rfl
  | node color left binding right ihl ihr =>
      obtain ⟨key, value⟩ := binding
      simp [RBTree.RBNode.size, ihl, ihr, Nat.add_comm, Nat.add_left_comm]

/-- Strict BST validity makes the enumerated keys distinct. Only keys in the
supplied finite set may occur; the set need not enumerate an insertion history. -/
theorem size_le_card [DecidableEq κ] (decode : κ → Int) (keys : Finset κ)
    (tree : Tree κ ν) (valid : Search.RedBlack.BST decode tree)
    (stored : Search.RedBlack.ForallT (fun key _ => key ∈ keys) tree) :
    tree.size ≤ keys.card := by
  have subset : ((Search.RedBlack.elements tree).map Prod.fst).toFinset ⊆ keys := by
    intro key member
    obtain ⟨binding, inTree, same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    subst key
    exact (Search.RedBlack.forallT_elements_iff _ tree).mp stored binding inTree
  calc
    tree.size = ((Search.RedBlack.elements tree).map Prod.fst).length := by
      rw [List.length_map, elements_length]
    _ = ((Search.RedBlack.elements tree).map Prod.fst).toFinset.card :=
      (List.toFinset_card_of_nodup (Search.RedBlack.keys_nodup decode valid)).symm
    _ ≤ keys.card := Finset.card_le_card subset

/-- The logarithm depends on distinct possible stored keys, including the empty
set endpoint. Shape and BST validity are separate hypotheses. -/
theorem height_le_card_log [DecidableEq κ] (decode : κ → Int) (keys : Finset κ)
    (tree : Tree κ ν) (valid : Search.RedBlack.BST decode tree)
    (stored : Search.RedBlack.ForallT (fun key _ => key ∈ keys) tree)
    {parent : RBTree.RBColor} {blackHeight : Nat}
    (shape : Search.RedBlack.RB tree parent blackHeight) :
    Search.RedBlack.height tree ≤ 2 * (keys.card + 1).log2 := by
  apply shape.height_log_bound.trans
  apply Nat.mul_le_mul_left
  simp only [Nat.log2_eq_log_two]
  exact Nat.log_mono_right (Nat.add_le_add_right (size_le_card decode keys tree valid stored) 1)

/-- Charge for a lookup and a possible insertion at the same starting tree.
All accepted balancing, pattern, construction and blackening observations remain
in the priced insertion coefficient. -/
def tableTariff (prices : RedBlack.Metric → Nat) (comparisonBound distinct : Nat) : Nat :=
  2 * (RedBlack.lookupSlope prices comparisonBound +
    RedBlack.insertSlope prices comparisonBound) * (distinct + 1).log2 +
    RedBlack.lookupIntercept prices + RedBlack.insertIntercept prices

theorem tableTariff_unit (comparisonBound distinct : Nat) :
    tableTariff (fun _ => 1) comparisonBound distinct =
      2 * (32 + 4 * comparisonBound) * (distinct + 1).log2 + 5 := by
  simp only [tableTariff, RedBlack.lookupSlope, RedBlack.insertSlope,
    RedBlack.lookupIntercept, RedBlack.insertIntercept]
  ring

/-- Comparison work is bounded only for the actual query and stored labels.
Both operation costs are retained, even though a duplicate branch will omit the
insertion in the collision program. -/
theorem lookup_insert_weighted_le [DecidableEq κ] (decode : κ → Int)
    (prices : RedBlack.Metric → Nat) (cmp : κ → κ → Measured Bool Nat)
    (query : κ) (value : ν) (tree : Tree κ ν) (keys : Finset κ) (K : Nat)
    (valid : Search.RedBlack.BST decode tree)
    (stored : Search.RedBlack.ForallT (fun key _ => key ∈ keys) tree)
    {parent : RBTree.RBColor} {blackHeight : Nat}
    (shape : Search.RedBlack.RB tree parent blackHeight)
    (comparisons : Search.RedBlack.ForallT
      (fun key _ => (cmp query key).2 ≤ K ∧ (cmp key query).2 ≤ K) tree) :
    RedBlack.weighted prices (RedBlack.lookupRun cmp query tree).2 +
      RedBlack.weighted prices (RedBlack.insertRun cmp query value tree).2 ≤
      tableTariff prices K keys.card := by
  have look := RedBlack.lookupRun_weighted_height prices cmp query tree K comparisons
  have write := RedBlack.insertRun_weighted_height prices cmp query value tree K comparisons
  have height := height_le_card_log decode keys tree valid stored shape
  have scaled := Nat.mul_le_mul_left
    (RedBlack.lookupSlope prices K + RedBlack.insertSlope prices K) height
  dsimp [tableTariff]
  nlinarith

/-- The old tree metrics, changed counter digits, and client overhead remain
separate observations in an existing product additive monoid. -/
abbrev Cost := RedBlack.Cost × (Nat × Nat)

/-- Price only the accepted tree-operation observations. -/
def tableWork (prices : RedBlack.Metric → Nat) : Cost →+ Nat where
  toFun cost := RedBlack.weighted prices cost.1
  map_zero' := RedBlack.weighted_zero prices
  map_add' left right := RedBlack.weighted_add prices left.1 right.1

/-- Changed binary digits are separate from tree construction and loop entry. -/
def counterWork : Cost →+ Nat where
  toFun cost := cost.2.1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Each transition, counter dispatch, and final observation receive one unit. -/
def overhead : Cost →+ Nat where
  toFun cost := cost.2.2
  map_zero' := rfl
  map_add' _ _ := rfl

/-- One aggregate for a caller's chosen tree prices, retaining each summand. -/
def totalWork (prices : RedBlack.Metric → Nat) (cost : Cost) : Nat :=
  tableWork prices cost + counterWork cost + overhead cost

/-- Applying the false default is an unpriced observation of the actual search
result; every accepted search and comparison charge is preserved. -/
def readRun (cmp : κ → κ → Measured Bool Nat) (query : κ) (tree : Tree κ Bool) :
    Measured Bool Cost :=
  let result := RedBlack.lookupRun cmp query tree
  (result.1.getD false, (result.2, (0, 0)))

/-- Source insertion keeps its complete balance and final-blackening metrics. -/
def writeRun (cmp : κ → κ → Measured Bool Nat) (key : κ) (value : Bool)
    (tree : Tree κ Bool) : Measured (Tree κ Bool) Cost :=
  reweight (fun work => (work, (0, 0))) (RedBlack.insertRun cmp key value tree)

theorem readRun_value (cmp : κ → κ → Measured Bool Nat) (key : κ) (tree : Tree κ Bool) :
    (readRun cmp key tree).1 = Search.RedBlack.lookup (fun a b => (cmp a b).1) false key tree :=
  RedBlack.lookupRun_getD cmp false key tree

theorem writeRun_value (cmp : κ → κ → Measured Bool Nat) (key : κ) (value : Bool)
    (tree : Tree κ Bool) :
    (writeRun cmp key value tree).1 = Search.RedBlack.insert (fun a b => (cmp a b).1) key value tree :=
  RedBlack.insertRun_value cmp key value tree

/-- The existing zero/positive binary increment supplies actual changed digits,
with one separate counter-dispatch observation. -/
def incrementRun (counter : Num) : Measured Num Cost :=
  reweight (fun writes => (0, (writes, 1))) (PositiveCounter.numAddOneRun counter)

def tick : Cost := (0, (0, 1))

/-- One specialization of the shared client; there is no new collision loop. -/
def step (cmp : κ → κ → Measured Bool Nat) (key : κ) (state : Num × Tree κ Bool) :
    Measured (Num × Tree κ Bool) Cost :=
  CollisionWork.step (readRun cmp) (writeRun cmp) incrementRun tick key state

def run (cmp : κ → κ → Measured Bool Nat) (xs : List κ) (state : Num × Tree κ Bool) :
    Measured (Num × Tree κ Bool) Cost :=
  CollisionWork.run (readRun cmp) (writeRun cmp) incrementRun tick tick xs state

def collisions (cmp : κ → κ → Measured Bool Nat) (xs : List κ) :
    Measured (Num × Tree κ Bool) Cost := run cmp xs (.zero, .nil)

/-- Decode the actual counter, retaining the actual colored tree. -/
def stateValue (state : Num × Tree κ Bool) : Nat × Tree κ Bool :=
  ((state.1 : Nat), state.2)

theorem step_value (cmp : κ → κ → Measured Bool Nat) (key : κ) (state : Num × Tree κ Bool) :
    stateValue (step cmp key state).1 =
      Search.Collisions.step (Search.RedBlack.table (fun a b => (cmp a b).1) false)
        (stateValue state) key := by
  cases seen : (readRun cmp key state.2).1 with
  | false =>
      rw [step, CollisionWork.step_of_false _ _ _ _ _ _ seen]
      change ((state.1 : Nat), (writeRun cmp key true state.2).1) =
        if Search.RedBlack.lookup (fun a b => (cmp a b).1) false key state.2 then
          ((state.1 : Nat) + 1, state.2)
        else ((state.1 : Nat), Search.RedBlack.insert (fun a b => (cmp a b).1) key true state.2)
      rw [readRun_value] at seen
      rw [seen, writeRun_value]
      rfl
  | true =>
      rw [step, CollisionWork.step_of_true _ _ _ _ _ _ seen]
      change (((PositiveCounter.numAddOneRun state.1).1 : Nat), state.2) =
        if Search.RedBlack.lookup (fun a b => (cmp a b).1) false key state.2 then
          ((state.1 : Nat) + 1, state.2)
        else ((state.1 : Nat), Search.RedBlack.insert (fun a b => (cmp a b).1) key true state.2)
      rw [readRun_value] at seen
      rw [seen, PositiveCounter.numAddOneRun_toNat]
      rfl

/-- Raw value erasure has no BST or balance hypothesis. Those hypotheses are
needed for map correctness and the resource bounds, not execution agreement. -/
theorem run_value (cmp : κ → κ → Measured Bool Nat) (xs : List κ)
    (state : Num × Tree κ Bool) :
    stateValue (run cmp xs state).1 =
      Search.Collisions.run (Search.RedBlack.table (fun a b => (cmp a b).1) false)
        xs (stateValue state) := by
  exact CollisionWork.run_value_fusion (readRun cmp) (writeRun cmp) incrementRun tick tick
    (Search.RedBlack.table (fun a b => (cmp a b).1) false) stateValue (fun _ => True)
    (by intros; trivial) (fun key state _ => step_value cmp key state) xs state trivial

theorem collisions_correct [DecidableEq κ] (decode : κ → Int)
    (cmp : κ → κ → Measured Bool Nat) (injective : Function.Injective decode)
    (order : ∀ a b, (cmp a b).1 = true ↔ decode a < decode b) (xs : List κ) :
    ((collisions cmp xs).1.1 : Nat) = Search.Collisions.count xs := by
  have erased := congrArg Prod.fst (run_value cmp xs (.zero, .nil))
  have correct := Search.Collisions.collisions_correct
    (Search.RedBlack.table_laws decode (fun a b => (cmp a b).1) injective order false) xs
  exact erased.trans correct

/-- The source signed observation of every reached counter is nonnegative. -/
theorem run_counter_nonnegative (cmp : κ → κ → Measured Bool Nat) (xs : List κ)
    (state : Num × Tree κ Bool) : 0 ≤ ((run cmp xs state).1.1.toZNum : Int) :=
  PositiveCounter.num_toZNum_nonnegative _

def Valid (decode : κ → Int) (keys : Finset κ) (tree : Tree κ Bool) : Prop :=
  Search.RedBlack.BST decode tree ∧
    (∃ blackHeight, Search.RedBlack.RB tree .red blackHeight) ∧
    Search.RedBlack.ForallT (fun key _ => key ∈ keys) tree

theorem valid_nil (decode : κ → Int) (keys : Finset κ) :
    Valid decode keys (.nil : Tree κ Bool) :=
  ⟨Search.RedBlack.bst_nil decode, ⟨0, Search.RedBlack.RB.nil .red⟩, trivial⟩

theorem step_valid (decode : κ → Int) (keys : Finset κ)
    (cmp : κ → κ → Measured Bool Nat)
    (order : ∀ a b, (cmp a b).1 = true ↔ decode a < decode b)
    (key : κ) (state : Num × Tree κ Bool) (admitted : key ∈ keys)
    (valid : Valid decode keys state.2) : Valid decode keys (step cmp key state).1.2 := by
  cases seen : (readRun cmp key state.2).1 with
  | false =>
      rw [step, CollisionWork.step_of_false _ _ _ _ _ _ seen]
      change Valid decode keys (writeRun cmp key true state.2).1
      rw [writeRun_value]
      obtain ⟨bst, ⟨blackHeight, shape⟩, stored⟩ := valid
      exact ⟨Search.RedBlack.insert_bst decode (fun a b => (cmp a b).1) order bst key true,
        Search.RedBlack.insert_rb _ key true shape,
        Search.RedBlack.insert_forallT _ _ key true state.2 admitted stored⟩
  | true =>
      rw [step, CollisionWork.step_of_true _ _ _ _ _ _ seen]
      exact valid

theorem run_valid (decode : κ → Int) (keys : Finset κ)
    (cmp : κ → κ → Measured Bool Nat)
    (order : ∀ a b, (cmp a b).1 = true ↔ decode a < decode b)
    (xs : List κ) (inputs : ∀ key ∈ xs, key ∈ keys) (state : Num × Tree κ Bool)
    (valid : Valid decode keys state.2) : Valid decode keys (run cmp xs state).1.2 := by
  exact CollisionWork.run_invariant_on (readRun cmp) (writeRun cmp) incrementRun tick tick
    (fun key => key ∈ keys) (fun state => Valid decode keys state.2)
    (step_valid decode keys cmp order) xs inputs state valid

theorem step_tableWork_le_operations (prices : RedBlack.Metric → Nat)
    (cmp : κ → κ → Measured Bool Nat) (key : κ) (state : Num × Tree κ Bool) :
    tableWork prices (step cmp key state).2 ≤
      RedBlack.weighted prices (RedBlack.lookupRun cmp key state.2).2 +
      RedBlack.weighted prices (RedBlack.insertRun cmp key true state.2).2 := by
  cases seen : (readRun cmp key state.2).1 with
  | false =>
      rw [step, CollisionWork.step_of_false _ _ _ _ _ _ seen]
      simp [tableWork, tick, readRun, writeRun, reweight, RedBlack.weighted_add]
  | true =>
      rw [step, CollisionWork.step_of_true _ _ _ _ _ _ seen]
      simp [tableWork, tick, readRun, incrementRun, reweight]

theorem step_tableWork_le [DecidableEq κ] (decode : κ → Int) (keys : Finset κ)
    (prices : RedBlack.Metric → Nat) (cmp : κ → κ → Measured Bool Nat) (K : Nat)
    (comparisons : ∀ a ∈ keys, ∀ b ∈ keys, (cmp a b).2 ≤ K)
    (key : κ) (state : Num × Tree κ Bool) (admitted : key ∈ keys)
    (valid : Valid decode keys state.2) :
    tableWork prices (step cmp key state).2 ≤ tableTariff prices K keys.card := by
  obtain ⟨bst, ⟨blackHeight, shape⟩, stored⟩ := valid
  have localBound : Search.RedBlack.ForallT
      (fun old _ => (cmp key old).2 ≤ K ∧ (cmp old key).2 ≤ K) state.2 :=
    Search.RedBlack.forallT_imp
      (fun old _ h => ⟨comparisons key admitted old h, comparisons old h key admitted⟩) stored
  exact (step_tableWork_le_operations prices cmp key state).trans
    (lookup_insert_weighted_le decode prices cmp key true state.2 keys K bst stored shape localBound)

/-- All actual prefix trees remain balanced valid maps containing keys from the
same finite input set. Thus each visited prefix has at most its cardinality. -/
theorem run_tableWork_le [DecidableEq κ] (decode : κ → Int) (keys : Finset κ)
    (prices : RedBlack.Metric → Nat) (cmp : κ → κ → Measured Bool Nat)
    (order : ∀ a b, (cmp a b).1 = true ↔ decode a < decode b) (K : Nat)
    (comparisons : ∀ a ∈ keys, ∀ b ∈ keys, (cmp a b).2 ≤ K)
    (xs : List κ) (inputs : ∀ key ∈ xs, key ∈ keys) (state : Num × Tree κ Bool)
    (valid : Valid decode keys state.2) :
    tableWork prices (run cmp xs state).2 ≤ xs.length * tableTariff prices K keys.card := by
  have bound := CollisionWork.run_cost_le_sum_on (readRun cmp) (writeRun cmp) incrementRun tick tick
    (tableWork prices) (fun _ => tableTariff prices K keys.card)
    (fun key => key ∈ keys) (fun state => Valid decode keys state.2)
    (step_valid decode keys cmp order)
    (step_tableWork_le decode keys prices cmp K comparisons) xs inputs state valid
  simpa [run, tableWork, tick, List.sum_replicate] using bound

def counterPotential (counter : Num) : Nat := BinaryCounter.ones (PositiveCounter.numDigits counter)

/-- Exact accounting follows the selected duplicate branches of the same run. -/
theorem run_counter_potential (cmp : κ → κ → Measured Bool Nat) (xs : List κ)
    (state : Num × Tree κ Bool) :
    counterWork (run cmp xs state).2 + counterPotential (run cmp xs state).1.1 =
      counterPotential state.1 + Resources.budget (step cmp)
        (fun key state => if (readRun cmp key state.2).1 then 2 else 0) xs state := by
  exact CollisionWork.run_counter_potential (readRun cmp) (writeRun cmp) incrementRun tick tick
    counterWork counterPotential 2 (by intros; rfl) (by intros; rfl) rfl rfl
    PositiveCounter.numAddOneRun_potential xs state

theorem run_counterWork_le (cmp : κ → κ → Measured Bool Nat) (xs : List κ)
    (state : Num × Tree κ Bool) :
    counterWork (run cmp xs state).2 ≤ counterPotential state.1 + 2 * xs.length := by
  exact CollisionWork.run_counter_cost_le (readRun cmp) (writeRun cmp) incrementRun tick tick
    counterWork counterPotential 2 (by intros; rfl) (by intros; rfl) rfl rfl
    PositiveCounter.numAddOneRun_potential xs state

theorem step_overhead_le (cmp : κ → κ → Measured Bool Nat) (key : κ)
    (state : Num × Tree κ Bool) : overhead (step cmp key state).2 ≤ 2 := by
  cases seen : (readRun cmp key state.2).1 with
  | false => rw [step, CollisionWork.step_of_false _ _ _ _ _ _ seen]; exact Nat.le_succ 1
  | true => rw [step, CollisionWork.step_of_true _ _ _ _ _ _ seen]; exact Nat.le_refl 2

theorem run_overhead_le (cmp : κ → κ → Measured Bool Nat) (xs : List κ)
    (state : Num × Tree κ Bool) : overhead (run cmp xs state).2 ≤ 2 * xs.length + 1 := by
  have bound := CollisionWork.run_cost_le_sum (readRun cmp) (writeRun cmp) incrementRun tick tick
    overhead (fun _ => 2) (fun _ => True) (by intros; trivial)
    (fun key state _ => step_overhead_le cmp key state) xs state trivial
  simpa [run, overhead, tick, List.sum_replicate, Nat.mul_comm] using bound

/-- Empty-start total work includes tree operations, every binary increment,
loop entry, counter dispatch and the terminal observation. -/
theorem collisions_totalWork_le [DecidableEq κ] (decode : κ → Int)
    (prices : RedBlack.Metric → Nat) (cmp : κ → κ → Measured Bool Nat)
    (order : ∀ a b, (cmp a b).1 = true ↔ decode a < decode b) (K : Nat)
    (xs : List κ) (comparisons : ∀ a ∈ xs, ∀ b ∈ xs, (cmp a b).2 ≤ K) :
    totalWork prices (collisions cmp xs).2 ≤
      xs.length * (tableTariff prices K xs.toFinset.card + 4) + 1 := by
  have tables := run_tableWork_le decode xs.toFinset prices cmp order K
    (by simpa only [List.mem_toFinset] using comparisons) xs
    (by simp) (.zero, .nil) (valid_nil decode xs.toFinset)
  have counters := run_counterWork_le cmp xs (.zero, .nil)
  have dispatch := run_overhead_le cmp xs (.zero, .nil)
  simp only [counterPotential, PositiveCounter.numDigits_zero, BinaryCounter.ones, Nat.zero_add] at counters
  dsimp [totalWork, collisions]
  nlinarith

/-- The measured signed comparator and the zero-start binary counter together
instantiate the source paragraph's balanced-table collision algorithm. -/
def signedCollisions (xs : List ZNum) : Measured (Num × Tree ZNum Bool) Cost :=
  collisions CollisionHistory.signedLtRun xs

theorem signed_order (x y : ZNum) :
    (CollisionHistory.signedLtRun x y).1 = true ↔ (x : Int) < (y : Int) := by
  rw [CollisionHistory.signedLtRun_value]
  exact decide_eq_true_iff

theorem signedCollisions_correct (xs : List ZNum) :
    ((signedCollisions xs).1.1 : Nat) = Search.Collisions.count xs :=
  collisions_correct (fun z : ZNum => (z : Int)) CollisionHistory.signedLtRun
    (fun _ _ h => ZNum.to_int_inj.mp h) signed_order xs

/-- Key bit length and distinct-key cardinality are independent parameters. -/
theorem signedCollisions_totalWork_le (xs : List ZNum) (B : Nat)
    (keyBound : ∀ key ∈ xs, CollisionHistory.bZ key ≤ B) :
    totalWork (fun _ => 1) (signedCollisions xs).2 ≤
      xs.length * (tableTariff (fun _ => 1) (2 * (B + 1)) xs.toFinset.card + 4) + 1 := by
  exact collisions_totalWork_le (fun z : ZNum => (z : Int)) (fun _ => 1)
    CollisionHistory.signedLtRun signed_order (2 * (B + 1)) xs
    (fun a ha b _ => CollisionHistory.signedLtRun_bound_left a b B (keyBound a ha))

/-- A readable majorant retains the bit-length and distinct-key factors,
with corrections that also cover the empty input. -/
theorem signedCollisions_totalWork_majorant (xs : List ZNum) (B : Nat)
    (keyBound : ∀ key ∈ xs, CollisionHistory.bZ key ≤ B) :
    totalWork (fun _ => 1) (signedCollisions xs).2 ≤
      90 * (xs.length + 1) * (B + 1) * (1 + (xs.toFinset.card + 1).log2) := by
  have bound := signedCollisions_totalWork_le xs B keyBound
  rw [tableTariff_unit] at bound
  have term : 2 * (32 + 4 * (2 * (B + 1))) * (xs.toFinset.card + 1).log2 + 5 + 4 ≤
      89 * (B + 1) * (1 + (xs.toFinset.card + 1).log2) := by
    nlinarith
  have multiplied := Nat.mul_le_mul_left xs.length term
  have positive : 1 ≤ (B + 1) * (1 + (xs.toFinset.card + 1).log2) := by
    exact Nat.mul_pos (by omega) (by omega)
  nlinarith

/-- For nonempty inputs the explicit length correction is absorbed by two. -/
theorem signedCollisions_nonempty_bound (xs : List ZNum) (nonempty : 1 ≤ xs.length) (B : Nat)
    (keyBound : ∀ key ∈ xs, CollisionHistory.bZ key ≤ B) :
    totalWork (fun _ => 1) (signedCollisions xs).2 ≤
      180 * xs.length * (B + 1) * (1 + (xs.toFinset.card + 1).log2) := by
  have bound := signedCollisions_totalWork_majorant xs B keyBound
  have lengths : xs.length + 1 ≤ 2 * xs.length := by omega
  have scaled := Nat.mul_le_mul_right
    (90 * (B + 1) * (1 + (xs.toFinset.card + 1).log2)) lengths
  nlinarith

/-- This conditional family has no unit-comparison premise. It uses the actual
signed comparator and its explicit input-dependent bit-length bound. -/
theorem signed_family_isBigO (inputs : Nat → List ZNum) (bits : Nat → Nat)
    (keyBound : ∀ index key, key ∈ inputs index → CollisionHistory.bZ key ≤ bits index) :
    Asymptotics.IsBigO Filter.atTop
      (fun index => (totalWork (fun _ => 1) (signedCollisions (inputs index)).2 : ℝ))
      (fun index => ((((inputs index).length + 1) * (bits index + 1) *
        (1 + ((inputs index).toFinset.card + 1).log2) : Nat) : ℝ)) := by
  apply Resources.isBigO_of_nat_bound _ _ 90 0
  intro index _
  have bound := signedCollisions_totalWork_majorant (inputs index) (bits index) (keyBound index)
  simpa only [Nat.mul_assoc] using bound

end Resources.CollisionRedBlack

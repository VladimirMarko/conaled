import Applications.Resources.PositiveTrie.Finite
import Applications.Search.PositiveTrie.Normalized

/-!
# Actual pruning erasure and simultaneous difference

Prune observes its entered call and emitted BinaryTree.node. The recursive
executors separately observe their own entries, prune calls and emitted nodes.
Nil entries count one. Each branch consumes its actual measured child result;
a returned existing subtree has no construction event. These are declared
source events, not physical allocation or a complete machine-cost model.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.PositiveTrie.Pruning

open Search.PositiveTrie Numerals.PositiveArithmetic

universe u
variable {α : Type u}

abbrev PruneCost := Nat × Nat
abbrev Cost := Nat × (Nat × Nat)

def pruneRun (occupied : α → Bool) : α → BinaryTree α → BinaryTree α →
    Measured (BinaryTree α) PruneCost
  | value, .nil, .nil =>
      if occupied value then (.node value .nil .nil, (1, 1)) else (.nil, (1, 0))
  | value, left, right => (.node value left right, (1, 1))

theorem pruneRun_calls (occupied : α → Bool) (value : α) (left right : BinaryTree α) :
    (pruneRun occupied value left right).2.1 = 1 := by
  cases h : occupied value <;> cases left <;> cases right <;> simp [pruneRun, h]

theorem pruneRun_nodes_le (occupied : α → Bool) (value : α) (left right : BinaryTree α) :
    (pruneRun occupied value left right).2.2 ≤ 1 := by
  cases h : occupied value <;> cases left <;> cases right <;> simp [pruneRun, h]

theorem pruneRun_map_value (value : Option α) (left right : SparseMap α) :
    (pruneRun Option.isSome value left right).1 = SparseMap.prune value left right := by
  cases value <;> cases left <;> cases right <;> rfl

theorem pruneRun_set_value (value : Bool) (left right : KeySet) :
    (pruneRun id value left right).1 = KeySet.prune value left right := by
  cases value <;> cases left <;> cases right <;> rfl

def eraseRun (occupied : α → Bool) (default : α) :
    PosNum → BinaryTree α → Measured (BinaryTree α) Cost
  | _, .nil => (.nil, (1, (0, 0)))
  | .one, .node _ left right =>
      bind ((), (1, (0, 0))) (fun _ =>
        reweight (fun cost => (0, cost)) (pruneRun occupied default left right))
  | .bit0 key, .node value left right =>
      bind ((), (1, (0, 0))) (fun _ =>
        bind (eraseRun occupied default key left) (fun next =>
          reweight (fun cost => (0, cost)) (pruneRun occupied value next right)))
  | .bit1 key, .node value left right =>
      bind ((), (1, (0, 0))) (fun _ =>
        bind (eraseRun occupied default key right) (fun next =>
          reweight (fun cost => (0, cost)) (pruneRun occupied value left next)))

theorem eraseRun_nil (occupied : α → Bool) (default : α) (key : PosNum) :
    eraseRun occupied default key .nil = (.nil, (1, (0, 0))) := by cases key <;> rfl

theorem eraseRun_calls_eq_look (occupied : α → Bool) (default : α)
    (key : PosNum) (tree : BinaryTree α) :
    (eraseRun occupied default key tree).2.1 = (lookRun default key tree).2.1 := by
  induction key generalizing tree with
  | one => cases tree <;> rfl
  | bit0 key ih =>
      cases tree <;> simp only [eraseRun, lookRun, bind, reweight, Prod.fst_add,
        Nat.add_zero, ih]
  | bit1 key ih =>
      cases tree <;> simp only [eraseRun, lookRun, bind, reweight, Prod.fst_add,
        Nat.add_zero, ih]

theorem eraseRun_calls_le (occupied : α → Bool) (default : α)
    (key : PosNum) (tree : BinaryTree α) :
    (eraseRun occupied default key tree).2.1 ≤ bitLength key := by
  rw [eraseRun_calls_eq_look]
  exact lookRun_calls_le default key tree

theorem eraseRun_calls_le_height (occupied : α → Bool) (default : α)
    (key : PosNum) (tree : BinaryTree α) :
    (eraseRun occupied default key tree).2.1 ≤ tree.height + 1 := by
  rw [eraseRun_calls_eq_look]
  induction tree generalizing key with
  | nil => rw [lookRun_nil]; exact Nat.le_refl 1
  | node value left right ihl ihr =>
      cases key with
      | one => simp [lookRun]
      | bit0 key =>
          have h := ihl key
          simp only [lookRun, bind, Prod.fst_add, BinaryTree.height]
          omega
      | bit1 key =>
          have h := ihr key
          simp only [lookRun, bind, Prod.fst_add, BinaryTree.height]
          omega

theorem eraseRun_prunes_le_calls (occupied : α → Bool) (default : α)
    (key : PosNum) (tree : BinaryTree α) :
    (eraseRun occupied default key tree).2.2.1 ≤
      (eraseRun occupied default key tree).2.1 := by
  induction key generalizing tree with
  | one => cases tree <;> simp [eraseRun, bind, reweight, pruneRun_calls]
  | bit0 key ih =>
      cases tree with
      | nil => simp [eraseRun]
      | node value left right =>
          have h := ih left
          simp only [eraseRun, bind, reweight, Prod.fst_add, Prod.snd_add,
            Nat.zero_add, Nat.add_zero, pruneRun_calls]
          omega
  | bit1 key ih =>
      cases tree with
      | nil => simp [eraseRun]
      | node value left right =>
          have h := ih right
          simp only [eraseRun, bind, reweight, Prod.fst_add, Prod.snd_add,
            Nat.zero_add, Nat.add_zero, pruneRun_calls]
          omega

theorem eraseRun_prunes_le_height (occupied : α → Bool) (default : α)
    (key : PosNum) (tree : BinaryTree α) :
    (eraseRun occupied default key tree).2.2.1 ≤ tree.height := by
  induction key generalizing tree with
  | one => cases tree <;> simp [eraseRun, bind, reweight, pruneRun_calls]
  | bit0 key ih =>
      cases tree with
      | nil => simp [eraseRun]
      | node value left right =>
          have h := ih left
          simp only [eraseRun, bind, reweight, Prod.snd_add, Prod.fst_add,
            Nat.zero_add, pruneRun_calls, BinaryTree.height]
          omega
  | bit1 key ih =>
      cases tree with
      | nil => simp [eraseRun]
      | node value left right =>
          have h := ih right
          simp only [eraseRun, bind, reweight, Prod.snd_add, Prod.fst_add,
            Nat.zero_add, pruneRun_calls, BinaryTree.height]
          omega

theorem eraseRun_nodes_le_prunes (occupied : α → Bool) (default : α)
    (key : PosNum) (tree : BinaryTree α) :
    (eraseRun occupied default key tree).2.2.2 ≤
      (eraseRun occupied default key tree).2.2.1 := by
  induction key generalizing tree with
  | one =>
      cases tree with
      | nil => simp [eraseRun]
      | node value left right =>
          simpa only [eraseRun, bind, reweight, Prod.snd_add, Prod.fst_add,
            Nat.zero_add, pruneRun_calls] using pruneRun_nodes_le occupied default left right
  | bit0 key ih =>
      cases tree with
      | nil => simp [eraseRun]
      | node value left right =>
          have h := ih left
          have hp := pruneRun_nodes_le occupied value (eraseRun occupied default key left).1 right
          simp only [eraseRun, bind, reweight, Prod.snd_add, Prod.fst_add,
            Nat.zero_add, pruneRun_calls]
          omega
  | bit1 key ih =>
      cases tree with
      | nil => simp [eraseRun]
      | node value left right =>
          have h := ih right
          have hp := pruneRun_nodes_le occupied value left (eraseRun occupied default key right).1
          simp only [eraseRun, bind, reweight, Prod.snd_add, Prod.fst_add,
            Nat.zero_add, pruneRun_calls]
          omega

theorem eraseRun_work_le (occupied : α → Bool) (default : α)
    (key : PosNum) (tree : BinaryTree α) :
    (eraseRun occupied default key tree).2.1 +
        (eraseRun occupied default key tree).2.2.1 +
        (eraseRun occupied default key tree).2.2.2 ≤ 3 * bitLength key := by
  have hc := eraseRun_calls_le occupied default key tree
  have hp := eraseRun_prunes_le_calls occupied default key tree
  have hn := eraseRun_nodes_le_prunes occupied default key tree
  omega

def mapEraseRun (key : PosNum) (tree : SparseMap α) : Measured (SparseMap α) Cost :=
  eraseRun Option.isSome none key tree

def setEraseRun (key : PosNum) (tree : KeySet) : Measured KeySet Cost :=
  eraseRun id false key tree

theorem mapEraseRun_value (key : PosNum) (tree : SparseMap α) :
    (mapEraseRun key tree).1 = SparseMap.erase key tree := by
  unfold mapEraseRun
  induction key generalizing tree with
  | one => cases tree <;> simp only [eraseRun, bind_value, reweight_value,
      pruneRun_map_value, SparseMap.erase]
  | bit0 key ih => cases tree <;> simp only [eraseRun, bind_value, reweight_value,
      pruneRun_map_value, SparseMap.erase, ih]
  | bit1 key ih => cases tree <;> simp only [eraseRun, bind_value, reweight_value,
      pruneRun_map_value, SparseMap.erase, ih]

theorem setEraseRun_value (key : PosNum) (tree : KeySet) :
    (setEraseRun key tree).1 = KeySet.erase key tree := by
  unfold setEraseRun
  induction key generalizing tree with
  | one => cases tree <;> simp only [eraseRun, bind_value, reweight_value,
      pruneRun_set_value, KeySet.erase]
  | bit0 key ih => cases tree <;> simp only [eraseRun, bind_value, reweight_value,
      pruneRun_set_value, KeySet.erase, ih]
  | bit1 key ih => cases tree <;> simp only [eraseRun, bind_value, reweight_value,
      pruneRun_set_value, KeySet.erase, ih]

theorem mapEraseRun_normalized (key : PosNum) {tree : SparseMap α}
    (normal : SparseMap.Normalized tree) : SparseMap.Normalized (mapEraseRun key tree).1 := by
  rw [mapEraseRun_value]
  exact SparseMap.normalized_erase key normal

theorem setEraseRun_normalized (key : PosNum) {tree : KeySet}
    (normal : KeySet.Normalized tree) : KeySet.Normalized (setEraseRun key tree).1 := by
  rw [setEraseRun_value]
  exact KeySet.normalized_erase key normal

theorem mapEraseRun_work_le (key : PosNum) (tree : SparseMap α) :
    (mapEraseRun key tree).2.1 + (mapEraseRun key tree).2.2.1 +
      (mapEraseRun key tree).2.2.2 ≤ 3 * bitLength key :=
  eraseRun_work_le Option.isSome none key tree

theorem setEraseRun_work_le (key : PosNum) (tree : KeySet) :
    (setEraseRun key tree).2.1 + (setEraseRun key tree).2.2.1 +
      (setEraseRun key tree).2.2.2 ≤ 3 * bitLength key :=
  eraseRun_work_le id false key tree

/-- A mathematical observation of the simultaneous recursion, not an extra run. -/
def pairedNodes : KeySet → KeySet → Nat
  | .nil, _ => 0
  | .node _ _ _, .nil => 0
  | .node _ left right, .node _ left' right' =>
      pairedNodes left left' + pairedNodes right right' + 1

def diffRun : KeySet → KeySet → Measured KeySet Cost
  | .nil, _ => (.nil, (1, (0, 0)))
  | tree@(.node _ _ _), .nil => (tree, (1, (0, 0)))
  | .node value left right, .node value' left' right' =>
      bind ((), (1, (0, 0))) (fun _ =>
        bind (diffRun left left') (fun l =>
          bind (diffRun right right') (fun r =>
            reweight (fun cost => (0, cost)) (pruneRun id (value && !value') l r))))

theorem diffRun_value (left right : KeySet) :
    (diffRun left right).1 = KeySet.diff left right := by
  induction left generalizing right with
  | nil => rfl
  | node value left rightTree ihl ihr =>
      cases right <;> simp only [diffRun, bind_value, reweight_value, pruneRun_set_value,
        KeySet.diff, ihl, ihr]

theorem pairedNodes_le_left (left right : KeySet) : pairedNodes left right ≤ left.numNodes := by
  induction left generalizing right with
  | nil => simp [pairedNodes]
  | node value left rightTree ihl ihr =>
      cases right with
      | nil => simp [pairedNodes]
      | node value' left' right' =>
          have hl := ihl left'
          have hr := ihr right'
          simp only [pairedNodes, BinaryTree.numNodes]
          omega

theorem pairedNodes_le_right (left right : KeySet) : pairedNodes left right ≤ right.numNodes := by
  induction left generalizing right with
  | nil => simp [pairedNodes]
  | node value left rightTree ihl ihr =>
      cases right with
      | nil => rfl
      | node value' left' right' =>
          have hl := ihl left'
          have hr := ihr right'
          simp only [pairedNodes, BinaryTree.numNodes]
          omega

theorem diffRun_calls (left right : KeySet) :
    (diffRun left right).2.1 = 2 * pairedNodes left right + 1 := by
  induction left generalizing right with
  | nil => rfl
  | node value left rightTree ihl ihr =>
      cases right with
      | nil => rfl
      | node value' left' right' =>
          simp only [diffRun, bind, reweight, Prod.fst_add, Nat.add_zero,
            ihl, ihr, pairedNodes]
          omega

theorem diffRun_prunes (left right : KeySet) :
    (diffRun left right).2.2.1 = pairedNodes left right := by
  induction left generalizing right with
  | nil => rfl
  | node value left rightTree ihl ihr =>
      cases right with
      | nil => rfl
      | node value' left' right' =>
          simp only [diffRun, bind, reweight, Prod.snd_add, Prod.fst_add,
            Nat.zero_add, pruneRun_calls, ihl, ihr, pairedNodes]
          omega

theorem diffRun_nodes_le (left right : KeySet) :
    (diffRun left right).2.2.2 ≤ pairedNodes left right := by
  induction left generalizing right with
  | nil => rfl
  | node value left rightTree ihl ihr =>
      cases right with
      | nil => rfl
      | node value' left' right' =>
          have hl := ihl left'
          have hr := ihr right'
          have hp := pruneRun_nodes_le id (value && !value')
            (diffRun left left').1 (diffRun rightTree right').1
          simp only [diffRun, bind, reweight, Prod.snd_add, Nat.zero_add, pairedNodes]
          omega

theorem diffRun_work_le (left right : KeySet) :
    (diffRun left right).2.1 + (diffRun left right).2.2.1 +
      (diffRun left right).2.2.2 ≤ 4 * pairedNodes left right + 1 := by
  rw [diffRun_calls, diffRun_prunes]
  have h := diffRun_nodes_le left right
  omega

theorem diffRun_work_le_of_bitLength {left : KeySet} (normal : KeySet.Normalized left)
    (right : KeySet) (bound : Nat)
    (bounded : ∀ key, KeySet.mem key left = true → bitLength key ≤ bound) :
    (diffRun left right).2.1 + (diffRun left right).2.2.1 +
      (diffRun left right).2.2.2 ≤ 4 * (KeySet.cardinal left * bound) + 1 := by
  have h := (pairedNodes_le_left left right).trans
    (KeySet.numNodes_le_cardinal_mul normal bound bounded)
  have hw := diffRun_work_le left right
  omega

theorem diffRun_normalized {left : KeySet} (normal : KeySet.Normalized left) (right : KeySet) :
    KeySet.Normalized (diffRun left right).1 := by
  rw [diffRun_value]
  exact KeySet.normalized_diff normal right

end Resources.PositiveTrie.Pruning

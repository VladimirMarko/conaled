import Applications.Sequences.LCA.Catalog
import Applications.Sequences.LCA.Workspace

/-! The full sparse-table intermediate strategy for the same bounded RMQ input
and total query specification as the shared-block backend. -/
namespace Sequences.LCA.SparseCatalog
open Resources Resources.Prepared TreeReduction Backend Catalog
open Sequences.PreparedRMQ
abbrev Key := Int ×ₗ Nat
abbrev State (m : Nat) := Vector (Vector Key m × Nat) (Nat.log 2 m+1) × Vector Nat (m+1)

def keys (input : Input m) : Vector Key m := Vector.ofFn fun i => (keyM input i.val).1

def keysM (input : Input m) : Measured (Vector Key m) Nat :=
  TableExecution.tabulate (toLex (0,0)) (fun i => keyM input i.val)

theorem keysM_value (input : Input m) : (keysM input).1 = keys input :=
  TableExecution.tabulate_value _ _

theorem keysM_cost (input : Input m) : (keysM input).2 ≤ 12*m := by
  simpa [keysM, Nat.mul_comm] using TableExecution.tabulate_cost
    (toLex (0,0)) (fun i : Fin m => keyM input i.val) 6 (fun i => keyM_cost input i.val)

def prepared (input : Input m) : State m :=
  (SparseExecution.prepare (toLex (0,0)) (keys input) (Nat.log 2 m)).1

/-- Two bound/order comparisons and one branch dispatch cost three. The
successful branch then charges inclusive-length arithmetic and index recovery. -/
def answer (state : State m) (q : Nat × Nat) : Measured Nat Nat :=
  TreeBackend.countDispatch <| TreeBackend.dispatch <| if h : q.1 ≤ q.2 ∧ q.2 < m then
    bind (subtractWord q.2 q.1) fun len =>
    bind (TreeBackend.increment len) fun length =>
    bind (SparseExecution.query state.1 state.2
      ⟨q.1,by omega⟩ ⟨min length m,by omega⟩) fun result => ((ofLex result).2,1)
  else pure 0

def ops (m : Nat) : Ops (Input m) (Nat × Nat) Nat (State m) where
  prepare input := bind (keysM input) fun source => SparseExecution.prepare (toLex (0,0)) source (Nat.log 2 m)
  answer := answer

def Valid (input : Input m) (state : State m) := state = prepared input

theorem prepare_valid (input : Input m) : Valid input ((ops m).prepare input).1 := by
  simp [Valid, ops, Resources.bind, keysM_value, prepared]

theorem prepared_query (input : Input m) (q : Nat × Nat) (h : q.1 ≤ q.2 ∧ q.2 < m) :
    (answer (prepared input) q).1 = rmqSpec input q := by
  have hl : 0 < q.2-q.1+1 := by omega
  have hend : q.1+(q.2-q.1+1) ≤ m := by omega
  simp only [answer, Resources.bind, TreeBackend.countDispatch, TreeBackend.dispatch, h, and_self, dite_true, subtractWord,
    TreeBackend.increment, min_eq_left (show q.2-q.1+1 ≤ m by omega)]
  unfold prepared
  rw [SparseExecution.query_prepared _ _ (Nat.log 2 m) ⟨q.1,by omega⟩
    ⟨q.2-q.1+1,by omega⟩ hl hend le_rfl]
  simp only [Nat.add_sub_cancel]
  unfold rmqSpec argmin
  apply congrArg (fun key : Key => (ofLex key).2)
  apply rangeMin_congr_interval
  intro i hi
  have hj : q.1+i < m := by omega
  simp [vectorRead, Nat.mod_eq_of_lt hj, keys, keyM_value]

theorem laws (m : Nat) : Laws (@Backend.spec m) (ops m) Valid where
  prepare := prepare_valid
  answer input state hv q := by
    subst state
    by_cases h : q.1 ≤ q.2 ∧ q.2 < m
    · simpa [ops, Backend.spec, h] using prepared_query input q h
    · simp [ops, answer, Backend.spec, h, TreeBackend.countDispatch, TreeBackend.dispatch, Resources.bind, Resources.pure]

theorem answer_cost (state : State m) (q : Nat × Nat) : (answer state q).2 ≤ 16 := by
  simp only [answer, Resources.bind, TreeBackend.countDispatch, TreeBackend.dispatch]
  split
  · simp [subtractWord, TreeBackend.increment, SparseExecution.query_cost]
  · simp [Resources.pure]

def preparationWork (m : Nat) := 26*m+3+Nat.log 2 m*(11*m+7)

theorem prepare_cost (input : Input m) : ((ops m).prepare input).2 ≤ preparationWork m := by
  have hk := keysM_cost input
  have hs := SparseExecution.prepare_cost (toLex (0,0)) (keysM input).1 (Nat.log 2 m)
  simp only [ops, Resources.bind, preparationWork]
  omega

private def small : Input 3 where
  cells := #v[(0,1),(0,0),(0,1)]
  positive := by decide
  bounded i := by fin_cases i <;> decide
  identityBound i := by fin_cases i <;> decide
  unit i hi := by
    have hh : i < 2 := by omega
    interval_cases i <;> simp [Dijkstra.Store.lookup]

/-- A length-three query overlaps sparse blocks and returns the independent
minimum's index. The endpoint pair 0,2 is translated to inclusive length3. -/
example : (answer (prepared small) (0,2)).1 = 1 := by
  rw [prepared_query small (0,2) (by decide)]
  decide

example : (answer (prepared small) (2,2)).1 = 2 := by
  rw [prepared_query small (2,2) (by decide)]
  decide

example : (answer (prepared small) (0,3)).1 = 0 := by
  simp [answer, TreeBackend.countDispatch, TreeBackend.dispatch, Resources.pure]

end Sequences.LCA.SparseCatalog

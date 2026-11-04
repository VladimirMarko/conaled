import Applications.Sequences.LCA.Catalog
import Applications.Sequences.LCA.Workspace
import Applications.Sequences.LCA.QueryStorage
import Applications.Sequences.LCA.Control
import Applications.Sequences.LCA.KeyBounds

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

/-- Retain each produced scalar until this query returns. The ten sparse
register results are shared with the verified common query interpreter. -/
def answerRun (state : State m) (q : Nat × Nat) : QueryStorage.Run Nat :=
  QueryStorage.bindRun (QueryStorage.note ()
    [.nat q.1,.nat q.2,.bit (decide (q.1 ≤ q.2)),.bit (decide (q.2 < m))]) fun _ =>
  if h : q.1 ≤ q.2 ∧ q.2 < m then
    QueryStorage.bindRun (QueryStorage.scalar (q.2-q.1)) fun len =>
    QueryStorage.bindRun (QueryStorage.scalar (len+1)) fun length =>
    QueryStorage.bindRun (QueryStorage.sparseRun state.1 state.2
      ⟨q.1,by omega⟩ ⟨min length m,by omega⟩) fun result =>
      QueryStorage.scalar (ofLex result).2
  else QueryStorage.scalar 0

theorem answerRun_value (state : State m) (q : Nat × Nat) :
    (answerRun state q).1 = (answer state q).1 := by
  by_cases h : q.1 ≤ q.2 ∧ q.2 < m <;>
    simp [answerRun, answer, QueryStorage.bindRun, QueryStorage.note, QueryStorage.scalar,
      QueryStorage.sparseRun_value, h, TreeBackend.countDispatch, TreeBackend.dispatch,
      Resources.bind, Resources.pure, subtractWord, TreeBackend.increment]

theorem answerRun_slots (state : State m) (q : Nat × Nat) :
    (answerRun state q).2.length ≤ 17 := by
  by_cases h : q.1 ≤ q.2 ∧ q.2 < m <;>
    simp [answerRun, QueryStorage.bindRun_slots, QueryStorage.scalar, QueryStorage.note,
      QueryStorage.sparseRun_slots, h]

def stateWords (state : State m) : Nat :=
  2*state.1.toArray.size + (state.1.toList.map (fun row => row.1.toArray.size)).sum +
    state.2.toArray.size

theorem stateWords_eq (state : State m) :
    stateWords state = SparseExecution.retainedSlots m (Nat.log 2 m) := by
  simp [stateWords, SparseExecution.retainedSlots, List.sum_replicate]
  ring

/-- The six slots hold the input reference, two indices, guard result, loaded
depth and encoded key during a bounds-safe key load. -/
def keyControl (input : Input m) (i : Fin m) : Control.Run Key :=
  let depth := (Dijkstra.Store.lookup input.cells i).2
  let result : Key := toLex ((depth : Int),i.val)
  Control.note result [.ref input.cells,.nat i.val,.nat m,.bit true,.nat depth,.ref result]

theorem keyControl_value (input : Input m) (i : Fin m) :
    (keyControl input i).value = (keyM input i.val).1 := by
  rw [keyM_value]
  simp [keyControl, Control.note, depthKey, Input.depth, i.isLt]

def keysControl (input : Input m) : Control.Run (Vector Key m) :=
  Control.tabulate (toLex (0,0)) (keyControl input)

theorem keysControl_value (input : Input m) : (keysControl input).value = keys input := by
  simp [keysControl, Control.tabulate_value, keyControl_value, keys]

theorem keysControl_peak (input : Input m) : (keysControl input).peak ≤ 14 :=
  Control.tabulate_peak _ _ (c := 6) (by intro i; exact Nat.le_refl _)

/-- All source, copied keys and sparse buffers remain live during construction.
The scalar bounds observe the actual table/control interpreters; adding their
peaks is a conservative schedule that needs no early frame reclamation. -/
def preparationPeak (input : Input m) : Nat :=
  2*input.cells.toArray.size + (keys input).toArray.size +
    Workspace.words (Workspace.sparseRun (toLex (0,0)) (keys input) (Nat.log 2 m)) +
    (keysControl input).peak +
    (Control.sparseRun (toLex (0,0)) (keys input) (Nat.log 2 m)).peak + 4

def storage (m : Nat) : Resources.Prepared.Storage (Input m) (State m) where
  retained := stateWords
  preparePeak := preparationPeak
  queryPeak state := stateWords state + 17

theorem query_frame_fits (state : State m) (q : Nat × Nat) :
    stateWords state + (answerRun state q).2.length ≤ (storage m).queryPeak state := by
  have := answerRun_slots state q
  change _ ≤ stateWords state + 17
  omega

def profile (m : Nat) : Profile (Input m) where
  preparation _ := preparationWork m
  query _ := 16
  maintenance _ := 0
  retained _ := SparseExecution.retainedSlots m (Nat.log 2 m)
  peak _ := SparseExecution.retainedSlots m (Nat.log 2 m) + 3*m +
    8*(Nat.log 2 m+1)+8*(m+1)+64

theorem preparationPeak_le (input : Input m) : preparationPeak input ≤ (profile m).peak input := by
  have hk := keysControl_peak input
  have hs := Control.sparseRun_peak (toLex (0,0)) (keys input) (Nat.log 2 m)
  simp only [preparationPeak, Vector.size_toArray, Workspace.sparseRun_words, profile]
  omega

theorem bounds (m : Nat) : Bounds (ops m) Valid (storage m) (profile m) where
  preparation := prepare_cost
  query _ state _ q := answer_cost state q
  retained _ state _ := by simp [storage, profile, stateWords_eq]
  preparePeak := preparationPeak_le
  queryPeak _ state _ := by simp [storage, profile, stateWords_eq]; omega

theorem preparationControl_value (input : Input m) :
    (Control.sparseRun (toLex (0,0)) (keysControl input).value (Nat.log 2 m)).value =
      ((ops m).prepare input).1 := by
  simp [Control.sparseRun_value, keysControl_value, ops, Resources.bind, keysM_value]

theorem preparationBuffers_value (input : Input m) :
    (Workspace.sparseRun (toLex (0,0)) (keys input) (Nat.log 2 m)).value =
      ((ops m).prepare input).1 := by
  simp [Workspace.sparseRun_value, ops, Resources.bind, keysM_value]

/-- Every copied key and every stored sparse cell fits the finite rectangle
whose encoding preserves depth order and tie identity. -/
theorem keys_fit (input : Input m) (i : Fin m) :
    KeyBounds.Fits 0 m m (keys input)[i.val] := by
  have hd := input.bounded i
  simp only [keys, Vector.getElem_ofFn, keyM_value, depthKey, KeyBounds.Fits,
    ofLex_toLex, Input.depth, i.isLt, dite_true, add_zero]
  exact ⟨by omega,by exact_mod_cast hd,True.intro⟩

theorem prepared_cell_fits (input : Input m) (level : Fin (Nat.log 2 m+1)) (i : Fin m) :
    KeyBounds.Fits 0 m m ((prepared input).1[level.val].1)[i.val] := by
  simp only [prepared, SparseExecution.prepare, Resources.bind, Resources.pure,
    SparseExecution.build_get _ _ _ level]
  exact KeyBounds.finiteRow_fits _ (keys_fit input) level.val i

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

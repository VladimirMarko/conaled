import Applications.Sequences.LCA.Preparation
import Applications.Sequences.LCA.PreparationBounds

/-! A monotone arena interpretation of preprocessing buffers. Allocation events
come from array initialization and descriptor reservation. Indexed writes reuse
their existing region. The trace is an observation, not a target-allocated list.
All temporaries remain live until preparation finishes, so no reclamation or
alias-lifetime assumption is needed. Scalar operations and bounded loop control
use the target's register/control interface, not native Lean call frames. -/
namespace Sequences.LCA.Workspace
open Dijkstra.Store PreparedRMQ

structure Run (α : Type) where
  value : α
  allocations : List Nat

def pure (a : α) : Run α := ⟨a,[]⟩
def bind (a : Run α) (f : α → Run β) : Run β :=
  let b := f a.value
  ⟨b.value, a.allocations ++ b.allocations⟩
def words (a : Run α) : Nat := a.allocations.sum

def reserve (slots : Nat) : Run Unit := ⟨(), [slots]⟩
def allocArray (cellWords : Nat) (seed : α) (n : Nat) : Run (Vector α n) :=
  ⟨Vector.replicate n seed, [cellWords*n]⟩
def write (mem : Vector α n) (i : Fin n) (value : α) : Run (Vector α n) :=
  pure (Dijkstra.Store.write mem i value)

@[simp] theorem words_pure (a : α) : words (pure a) = 0 := rfl
@[simp] theorem words_bind (a : Run α) (f : α → Run β) :
    words (bind a f) = words a + words (f a.value) := by simp [words, bind]
@[simp] theorem words_allocArray (cellWords : Nat) (seed : α) (n : Nat) :
    words (allocArray cellWords seed n) = cellWords*n := by simp [words,allocArray]
@[simp] theorem words_reserve (n : Nat) : words (reserve n) = n := by simp [words,reserve]
@[simp] theorem words_write (mem : Vector α n) (i : Fin n) (value : α) :
    words (write mem i value) = 0 := rfl

def fill (f : Fin n → Run α) : List (Fin n) → Vector α n → Run (Vector α n)
  | [], mem => pure mem
  | i::rest, mem => bind (f i) fun value => bind (write mem i value) fun mem' => fill f rest mem'

theorem fill_value (f : Fin n → Run α) (indices : List (Fin n)) (mem : Vector α n) :
    (fill f indices mem).value =
      accum (fun _ x => x) mem (indices.map (fun i => (i,(f i).value))) := by
  induction indices generalizing mem with
  | nil => rfl
  | cons i rest ih => simpa [fill,bind,write,pure,accum,accumStep] using ih (Dijkstra.Store.write mem i (f i).value)

theorem fill_words (f : Fin n → Run α) (indices : List (Fin n)) (mem : Vector α n)
    (c : Nat) (hc : ∀ i, words (f i) = c) : words (fill f indices mem) = indices.length*c := by
  induction indices generalizing mem with
  | nil => simp [fill]
  | cons i rest ih => simp [fill, hc, ih, Nat.add_mul, Nat.add_comm]

def tabulate (cellWords : Nat) (seed : α) (f : Fin n → Run α) : Run (Vector α n) :=
  bind (allocArray cellWords seed n) fun mem => fill f (List.finRange n) mem

theorem tabulate_value (cellWords : Nat) (seed : α) (f : Fin n → Run α) :
    (tabulate cellWords seed f).value = Vector.ofFn (fun i => (f i).value) := by
  apply Vector.ext
  intro i hi
  simp only [tabulate,bind,fill_value]
  have hh := accum_lookup (fun (_ : α) x => x) (allocArray cellWords seed n).value
    ((List.finRange n).map (fun i => (i,(f i).value))) ⟨i,hi⟩
  rw [valuesAt_map_unique _ _ (List.nodup_finRange n)] at hh
  simpa [lookup] using hh

theorem tabulate_words (cellWords : Nat) (seed : α) (f : Fin n → Run α)
    (c : Nat) (hc : ∀ i, words (f i) = c) :
    words (tabulate cellWords seed f) = n*(cellWords+c) := by
  simp [tabulate, fill_words f _ _ c hc, Nat.mul_add, Nat.mul_comm]

@[simp] theorem tabulate_pure_words (cellWords : Nat) (seed : α) (f : Fin n → α) :
    words (tabulate cellWords seed (fun i => pure (f i))) = n*cellWords := by
  simpa using tabulate_words cellWords seed (fun i => pure (f i)) 0 (fun _ => rfl)

/-- One initialized row is updated in place throughout the cumulative scan. -/
def rowFill [LinearOrder α] (seed : α) (source : Nat → Resources.Measured α Nat) (capacity : Nat) :
    (len : Nat) → len ≤ capacity → Run (Vector α capacity)
  | 0, _ => allocArray 1 seed capacity
  | k+1, hk => bind (rowFill seed source capacity k (by omega)) fun mem =>
    let slot : Fin capacity := ⟨k,by omega⟩
    let x := (source k).1
    if hz : k = 0 then write mem slot x
    else write mem slot (min (lookup mem ⟨k-1,by omega⟩) x)

theorem rowFill_value [LinearOrder α] (seed : α) (source : Nat → Resources.Measured α Nat)
    (capacity len : Nat) (h : len ≤ capacity) :
    (rowFill seed source capacity len h).value =
      (MicroExecution.rowFill seed source capacity len h).1 := by
  induction len with
  | zero => simp [rowFill,allocArray,MicroExecution.rowFill,TableExecution.initStore_exact]
  | succ k ih =>
    simp only [rowFill,bind,MicroExecution.rowFill,Resources.bind,MicroExecution.rowIndex,
      TableExecution.store,TableExecution.read,MicroExecution.minimum]
    rw [ih]
    split_ifs <;> simp_all [write,pure]

theorem rowFill_words [LinearOrder α] (seed : α) (source : Nat → Resources.Measured α Nat)
    (capacity len : Nat) (h : len ≤ capacity) : words (rowFill seed source capacity len h) = capacity := by
  induction len with
  | zero => simp [rowFill]
  | succ k ih =>
    simp only [rowFill, words_bind, ih]
    split_ifs <;> simp

def classRun (heights : Heights steps) : Run (ClassTable steps) :=
  let seed := (MicroExecution.keySource heights 0 0).1
  bind (allocArray 1 seed (steps+1)) fun seedRow =>
  tabulate 1 seedRow (fun start : Fin (steps+1) =>
    rowFill seed (MicroExecution.keySource heights start.val) (steps+1) (steps+1) le_rfl)

theorem classRun_value (heights : Heights steps) :
    (classRun heights).value = (MicroExecution.buildClassM heights).1 := by
  simp only [classRun,bind,tabulate_value,rowFill_value,MicroExecution.buildClassM,
    Resources.bind,TableExecution.tabulate_value,MicroExecution.buildRow]

theorem classRun_words (heights : Heights steps) :
    words (classRun heights) = (steps+1)*(steps+1)+2*(steps+1) := by
  simp only [classRun,words_bind,words_allocArray,one_mul]
  rw [tabulate_words _ _ _ (steps+1) (fun _ => rowFill_words _ _ _ _ _)]
  ring

def canonicalRun (steps code : Nat) : Run (Heights steps) :=
  tabulate 1 (0 : Int) (fun i : Fin (steps+1) => pure (MicroExecution.relativeCodeM code i.val).1)

theorem canonicalRun_value (steps code : Nat) :
    (canonicalRun steps code).value = (MicroExecution.canonicalM steps code).1 := by
  simp [canonicalRun,tabulate_value,pure,MicroExecution.canonicalM,TableExecution.tabulate_value]

theorem canonicalRun_words (steps code : Nat) : words (canonicalRun steps code) = steps+1 := by
  simp [canonicalRun,tabulate_pure_words]

def sharedRun (steps : Nat) : Run (SharedTable steps) :=
  bind (allocArray 1 (toLex ((0 : Int),(0 : Nat))) (steps+1)) fun seedRow =>
  bind (allocArray 1 seedRow (steps+1)) fun seedClass =>
  tabulate 1 seedClass (fun code : Fin (2^steps) =>
    bind (canonicalRun steps code.val) fun heights => classRun heights)

theorem sharedRun_value (steps : Nat) : (sharedRun steps).value = (MicroExecution.sharedM steps).1 := by
  simp only [sharedRun,bind,tabulate_value,canonicalRun_value,classRun_value,
    MicroExecution.sharedM,Resources.bind,TableExecution.tabulate_value]

theorem sharedRun_words (steps : Nat) :
    words (sharedRun steps) = 2*(steps+1) + 2^steps*((steps+1)*(steps+1)+3*(steps+1)+1) := by
  simp only [sharedRun,words_bind,words_allocArray,one_mul]
  rw [tabulate_words _ _ _ ((steps+1)*(steps+1)+3*(steps+1)) (by
    intro code
    simp [canonicalRun_words,classRun_words]
    ring)]
  ring

/-- Descriptors occupy a reserved contiguous arena. The recursive prefix only
initializes its next descriptor; row buffers occupy separate allocations. -/
def sparseRows [LinearOrder α] (seed : α) (input : Vector α n) :
    (levels : Nat) → Run (Vector (Vector α n × Nat) (levels+1))
  | 0 => bind (tabulate 1 seed (fun i => pure input[i.val])) fun row => pure #v[(row,1)]
  | k+1 => bind (sparseRows seed input k) fun prev =>
    let desc := prev[k]
    bind (tabulate 1 seed (fun i => pure (SparseExecution.rowCell desc.1 desc.2 i).1)) fun row =>
    pure (prev.push (row,desc.2+desc.2))

theorem sparseRows_value [LinearOrder α] (seed : α) (input : Vector α n) (levels : Nat) :
    (sparseRows seed input levels).value = (SparseExecution.build seed input levels).1 := by
  induction levels with
  | zero =>
    simp [sparseRows,bind,pure,tabulate_value,SparseExecution.build,Resources.bind,
      TableExecution.tabulate_value,TableExecution.read,lookup]
  | succ k ih =>
    simp only [sparseRows,bind,pure,tabulate_value,ih,SparseExecution.build,Resources.bind,
      SparseExecution.nextRow,TableExecution.tabulate_value]

theorem sparseRows_words [LinearOrder α] (seed : α) (input : Vector α n) (levels : Nat) :
    words (sparseRows seed input levels) = (levels+1)*n := by
  induction levels with
  | zero => simp [sparseRows,tabulate_pure_words]
  | succ k ih =>
    simp only [sparseRows,words_bind,ih]
    simp [tabulate_pure_words]
    ring

/-- The logarithm vector is initialized by prefix writes into its reserved
arena. Every next entry reads an earlier initialized slot. -/
def logsFill : (n : Nat) → Run (Vector Nat (n+1))
  | 0 => pure #v[0]
  | k+1 => bind (logsFill k) fun prev =>
    let value := if k = 0 then 0 else prev[(k+1)/2]'(by omega) + 1
    pure (prev.push value)

theorem logsFill_value (n : Nat) : (logsFill n).value = (SparseExecution.logs n).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [logsFill,bind,pure,ih,SparseExecution.logs,Resources.bind,TableExecution.read,lookup]
    by_cases h : n = 0 <;> simp [h]

theorem logsFill_words (n : Nat) : words (logsFill n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [logsFill, ih]

def sparseRun [LinearOrder α] (seed : α) (input : Vector α n) (levels : Nat) :
    Run (Vector (Vector α n × Nat) (levels+1) × Vector Nat (n+1)) :=
  bind (reserve (2*(levels+1))) fun _ =>
  bind (sparseRows seed input levels) fun rows =>
  bind (reserve (n+1)) fun _ =>
  bind (logsFill n) fun logs => pure (rows,logs)

theorem sparseRun_value [LinearOrder α] (seed : α) (input : Vector α n) (levels : Nat) :
    (sparseRun seed input levels).value = (SparseExecution.prepare seed input levels).1 := by
  simp [sparseRun,bind,pure,sparseRows_value,logsFill_value,SparseExecution.prepare,Resources.bind,Resources.pure]

theorem sparseRun_words [LinearOrder α] (seed : α) (input : Vector α n) (levels : Nat) :
    words (sparseRun seed input levels) = SparseExecution.retainedSlots n levels := by
  simp [sparseRun,sparseRows_words,logsFill_words,SparseExecution.retainedSlots]
  ring

def microRun (source : Nat → Resources.Measured Int Nat) (steps blocks : Nat) :
    Run (BlockedRMQ.MicroData steps blocks) :=
  bind (tabulate 1 (0 : Int) (fun i : Fin (blocks*(steps+1)) => pure (source i.val).1)) fun depths =>
  bind (tabulate 1 (⟨0,Nat.two_pow_pos steps⟩ : Fin (2^steps))
    (fun block : Fin blocks => pure (Preparation.blockAddressM source steps block.val).1)) fun classes =>
  bind (sharedRun steps) fun shared => pure ⟨depths,classes,shared⟩

theorem microRun_value (source : Nat → Resources.Measured Int Nat) (steps blocks : Nat) :
    (microRun source steps blocks).value = (Preparation.microM source steps blocks).1 := by
  simp only [microRun,bind,tabulate_value,pure,sharedRun_value,Preparation.microM,
    Resources.bind,Resources.pure,TableExecution.tabulate_value]

theorem microRun_words (source : Nat → Resources.Measured Int Nat) (steps blocks : Nat) :
    words (microRun source steps blocks) = blocks*(steps+1)+blocks+
      (2*(steps+1)+2^steps*((steps+1)*(steps+1)+3*(steps+1)+1)) := by
  simp [microRun,tabulate_pure_words,sharedRun_words]
  ring

def prepareRun (source : Nat → Resources.Measured Int Nat) (steps blocks levels : Nat)
    (hb : 0 < blocks) : Run (BlockedRMQ.Data steps blocks levels) :=
  bind (microRun source steps blocks) fun micro =>
  bind (tabulate 1 (toLex ((0 : Int),(0 : Nat))) (fun block : Fin blocks =>
    pure (BlockedRMQ.withinMeasured micro hb block.val 0 steps).1)) fun minima =>
  bind (sparseRun (toLex (0,0)) minima levels) fun tables => pure ⟨micro,tables.1,tables.2⟩

theorem prepareRun_value (source : Nat → Resources.Measured Int Nat) (steps blocks levels : Nat)
    (hb : 0 < blocks) :
    (prepareRun source steps blocks levels hb).value = (Preparation.prepare source steps blocks levels hb).1 := by
  simp only [prepareRun,bind,microRun_value,tabulate_value,pure,sparseRun_value,
    Preparation.prepare,Resources.bind,Resources.pure,Preparation.minimaM,TableExecution.tabulate_value]

theorem prepareRun_words (source : Nat → Resources.Measured Int Nat) (steps blocks levels : Nat)
    (hb : 0 < blocks) : words (prepareRun source steps blocks levels hb) =
      blocks*(steps+1)+blocks+
      (2*(steps+1)+2^steps*((steps+1)*(steps+1)+3*(steps+1)+1))+blocks+
      SparseExecution.retainedSlots blocks levels := by
  simp [prepareRun,microRun_words,tabulate_pure_words,sparseRun_words]
  ring

/-- No region is reclaimed in this interpretation. Its prefix sum is both
the next allocation base and the currently live arena size. -/
theorem prefix_entry_le (events : List Nat) (j : Nat) (hj : j < events.length) :
    (events.take j).sum + events[j] ≤ events.sum := by
  induction events generalizing j with
  | nil => simp at hj
  | cons size rest ih =>
    cases j with
    | zero => simp
    | succ j =>
      simpa [List.take_succ_cons, Nat.add_assoc] using Nat.add_le_add_left (ih j (by simpa using hj)) size

def regionAddress (run : Run α) (event : Fin run.allocations.length)
    (slot : Fin run.allocations[event.val]) : Fin (words run) :=
  ⟨(run.allocations.take event.val).sum+slot.val, by
    have hh := prefix_entry_le run.allocations event.val event.isLt
    have hs := slot.isLt
    unfold words
    omega⟩

theorem region_disjoint (events : List Nat) (a b : Fin events.length) (hab : a.val < b.val) :
    (events.take a.val).sum + events[a.val] ≤ (events.take b.val).sum := by
  have hb : (events.take b.val).length = b.val := by simp
  have hh := prefix_entry_le (events.take b.val) a.val (by rw [hb]; exact hab)
  simpa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hab)] using hh

/-- Region addresses embed after caller-owned storage and scalar/control
frames. The whole allocation history fits; earlier regions remain live. -/
def addressIn (run : Run α) (external capacity : Nat) (h : external+words run ≤ capacity)
    (event : Fin run.allocations.length) (slot : Fin run.allocations[event.val]) : Fin capacity :=
  ⟨external+(regionAddress run event slot).val, by
    have hh := (regionAddress run event slot).isLt
    omega⟩

def temporaryWords (n : Nat) : Nat :=
  2*blockSize n + 2*blockSize n*2^(blockSize n-1)

def selectedRun (source : Nat → Resources.Measured Int Nat) (n : Nat) :=
  prepareRun source (blockSize n-1) (PreparationBounds.blocks n) (PreparationBounds.levels n)
    (PreparationBounds.blocks_pos n)

theorem selectedRun_words (source : Nat → Resources.Measured Int Nat) (n : Nat) :
    words (selectedRun source n) = PreparationBounds.retainedSlots n + temporaryWords n := by
  have hb := blockSize_pos n
  simp only [selectedRun,prepareRun_words, show blockSize n-1+1 = blockSize n by omega]
  unfold PreparationBounds.retainedSlots PreparationBounds.paddedCapacity PreparationBounds.sharedSlots temporaryWords
  ring

theorem temporaryWords_le (hn : 0 < n) : temporaryWords n ≤ 6*n := by
  have he := PreparationBounds.class_entries_le hn
  have hb := blockSize_le hn
  have hp := blockSize_pos n
  have hh : blockSize n ≤ blockSize n*blockSize n := by nlinarith
  have hm := Nat.mul_le_mul_right (2^(blockSize n-1)) hh
  unfold temporaryWords
  nlinarith

theorem prepareRun_linear (source : Nat → Resources.Measured Int Nat) (hn : 0 < n) :
    words (selectedRun source n) ≤ 42*n := by
  rw [selectedRun_words]
  have hr := PreparationBounds.retainedSlots_le hn
  have ht := temporaryWords_le hn
  omega

/-- External input and scalar/control frames have independent contracts.
This theorem does not infer a register bound for an arbitrary source callback. -/
theorem prepareRun_peak (source : Nat → Resources.Measured Int Nat) (hn : 0 < n)
    (hi : inputWords ≤ 4*n) (hf : frameWords ≤ 18*n) :
    inputWords + frameWords + words (selectedRun source n) ≤ 64*n := by
  have hh := prepareRun_linear source hn
  omega

theorem prepareRun_peak128 (source : Nat → Resources.Measured Int Nat) (hn : 0 < n)
    (hi : inputWords ≤ 4*n) (hf : frameWords ≤ 64*n) :
    inputWords + frameWords + words (selectedRun source n) ≤ 128*n := by
  have hh := prepareRun_linear source hn
  omega

/-- The singleton run actually allocates fifteen slots, including shared
seeds and the per-class temporaries that remain live. -/
example : words (selectedRun (fun _ => ((0 : Int),1)) 1) = 15 := by
  rw [selectedRun_words]
  decide

example : (selectedRun (fun _ => ((0 : Int),1)) 1).value =
    (Preparation.prepare (fun _ => ((0 : Int),1)) 0 1 0 (by decide)).1 := by
  exact prepareRun_value _ 0 1 0 (by decide)

end Sequences.LCA.Workspace

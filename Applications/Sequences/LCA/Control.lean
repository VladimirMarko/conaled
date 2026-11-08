import Applications.Sequences.LCA.Workspace
import Applications.Sequences.LCA.QueryStorage

/-! Scalar/control storage for the preparation schedule. A saved frame contains
the actual scalar values or references retained across a call. Sequencing
releases a completed call's frame; bounded array loops reuse one frame.
Recursive scalar and row computations keep their explicit continuation frames.
Arena arrays themselves are accounted by Workspace, not copied into frames. -/
namespace Sequences.LCA.Control
open Dijkstra.Store PreparedRMQ
abbrev Key := Int ×ₗ Nat

/-- A target scalar or one-word reference; arena payload is not duplicated.
Key references denote the packed ordered cell used by the word backend. -/
inductive Slot where
  | nat : Nat → Slot
  | integer : Int → Slot
  | bit : Bool → Slot
  | ref {α : Type} : α → Slot

structure Run (α : Type) where
  value : α
  peak : Nat

def pure (a : α) : Run α := ⟨a,0⟩
def note (a : α) (slots : List Slot) : Run α := ⟨a,slots.length⟩
def scope (slots : List Slot) (a : Run α) : Run α := ⟨a.value,slots.length+a.peak⟩
def seq (a : Run α) (f : α → Run β) : Run β :=
  let b := f a.value
  ⟨b.value,max a.peak b.peak⟩

def allocArray (seed : α) (n : Nat) : Run (Vector α n) :=
  note (Vector.replicate n seed) [.ref seed,.nat n,.nat 0,.ref (Vector.replicate n seed)]

/-- The list is the finite loop schedule, not an allocated runtime list.
The enclosing tabulation scope retains the buffer, callback, limit and counter. -/
def fillLoop (f : Fin n → Run α) : List (Fin n) → Vector α n → Run (Vector α n)
  | [], mem => pure mem
  | i::rest, mem => seq (f i) fun x => fillLoop f rest (Dijkstra.Store.write mem i x)

theorem fillLoop_value (f : Fin n → Run α) (indices : List (Fin n)) (mem : Vector α n) :
    (fillLoop f indices mem).value = accum (fun _ x => x) mem (indices.map (fun i => (i,(f i).value))) := by
  induction indices generalizing mem with
  | nil => rfl
  | cons i rest ih => simpa [fillLoop,seq,accum,accumStep] using ih (Dijkstra.Store.write mem i (f i).value)

theorem fillLoop_peak (f : Fin n → Run α) (indices : List (Fin n)) (mem : Vector α n)
    (hc : ∀ i, (f i).peak ≤ c) : (fillLoop f indices mem).peak ≤ c := by
  induction indices generalizing mem with
  | nil => simp [fillLoop,pure]
  | cons i rest ih => exact max_le (hc i) (ih _)

def tabulate (seed : α) (f : Fin n → Run α) : Run (Vector α n) :=
  seq (allocArray seed n) fun mem =>
  scope [.ref mem,.ref f,.nat n,.nat 0] (fillLoop f (List.finRange n) mem)

theorem tabulate_value (seed : α) (f : Fin n → Run α) :
    (tabulate seed f).value = Vector.ofFn (fun i => (f i).value) := by
  apply Vector.ext
  intro i hi
  simp only [tabulate,seq,scope,fillLoop_value]
  have hh := accum_lookup (fun (_ : α) x => x) (allocArray seed n).value
    ((List.finRange n).map (fun i => (i,(f i).value))) ⟨i,hi⟩
  rw [valuesAt_map_unique _ _ (List.nodup_finRange n)] at hh
  simpa [lookup] using hh

theorem tabulate_peak (seed : α) (f : Fin n → Run α) (hc : ∀ i, (f i).peak ≤ c) :
    (tabulate seed f).peak ≤ c+8 := by
  have hh := fillLoop_peak f (List.finRange n) (allocArray seed n).value hc
  simp only [tabulate,seq,scope,allocArray,note,List.length_cons,List.length_nil]
  change _ ≤ c at hh
  dsimp [allocArray,note] at hh
  omega

def rowFill (seed : Key) (source : Nat → Run Key) (capacity : Nat) :
    (len : Nat) → len ≤ capacity → Run (Vector Key capacity)
  | 0, _ => allocArray seed capacity
  | k+1, hk => scope [.ref seed,.ref source,.nat capacity,.nat k]
    (seq (rowFill seed source capacity k (by omega)) fun mem =>
    scope [.ref mem] (seq (source k) fun x =>
      let slot : Fin capacity := ⟨k,by omega⟩
      let previous := if h : k = 0 then x else lookup mem ⟨k-1,by omega⟩
      let value := min previous x
      note (Dijkstra.Store.write mem slot value) [.ref mem,.nat k,.ref x,.ref previous,.ref value]))

theorem rowFill_value (seed : Key) (source : Nat → Run Key) (capacity len : Nat)
    (h : len ≤ capacity) :
    (rowFill seed source capacity len h).value =
      (MicroExecution.rowFill seed (fun i => ((source i).value,0)) capacity len h).1 := by
  induction len with
  | zero => simp [rowFill,allocArray,note,MicroExecution.rowFill,TableExecution.initStore_exact]
  | succ k ih =>
    simp only [rowFill,scope,seq,note,ih,MicroExecution.rowFill,Resources.bind,
      MicroExecution.rowIndex,TableExecution.read,TableExecution.store,MicroExecution.minimum]
    by_cases hk : k = 0 <;> simp [hk]

theorem rowFill_peak (seed : Key) (source : Nat → Run Key) (capacity len : Nat)
    (h : len ≤ capacity) (hc : ∀ i, (source i).peak ≤ c) :
    (rowFill seed source capacity len h).peak ≤ 4*len+c+10 := by
  induction len with
  | zero => simp [rowFill,allocArray,note]
  | succ k ih =>
    have hh := ih (by omega)
    have hs := hc k
    simp only [rowFill,scope,seq,note,List.length_cons,List.length_nil]
    omega

def keySource (heights : Heights steps) (start i : Nat) : Run Key :=
  let j := start+i
  let depth := boundedDepth heights j
  note (depthKey (boundedDepth heights) j)
    [.ref heights,.nat start,.nat i,.nat j,.integer depth,.ref (depthKey (boundedDepth heights) j)]

theorem keySource_value (heights : Heights steps) (start i : Nat) :
    (keySource heights start i).value = (MicroExecution.keySource heights start i).1 := by
  rw [MicroExecution.keySource_exact]
  rfl

theorem keySource_peak (heights : Heights steps) (start i : Nat) :
    (keySource heights start i).peak = 6 := rfl

def classRun (heights : Heights steps) : Run (ClassTable steps) :=
  seq (keySource heights 0 0) fun seed =>
  scope [.ref heights,.ref seed] (seq (allocArray seed (steps+1)) fun seedRow =>
  scope [.ref seedRow] (tabulate seedRow (fun start : Fin (steps+1) =>
    rowFill seed (keySource heights start.val) (steps+1) (steps+1) le_rfl)))

theorem classRun_value (heights : Heights steps) :
    (classRun heights).value = buildClass heights := by
  simp only [classRun,seq,scope,keySource_value,tabulate_value,rowFill_value]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn]
  change (MicroExecution.buildRow _ _ (steps+1)).1 = _
  rw [MicroExecution.buildRow_value]
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn,MicroExecution.keySource_exact,
    buildClass,Vector.getElem_ofFn]
  change rangeMin (fun k => depthKey (boundedDepth heights) (i+k)) 0 j =
    (prefixRow (depthKey (boundedDepth heights)) i steps).get ⟨j,hj⟩
  rw [MicroExecution.rangeMin_translate,prefixRow_get]

theorem classRun_peak (heights : Heights steps) : (classRun heights).peak ≤ 48*(steps+1) := by
  have ht := tabulate_peak (Vector.replicate (steps+1) (keySource heights 0 0).value)
    (fun start : Fin (steps+1) => rowFill (keySource heights 0 0).value
      (keySource heights start.val) (steps+1) (steps+1) le_rfl)
    (fun start => rowFill_peak _ _ _ _ _ (fun i => (keySource_peak heights start.val i).le))
  simp only [classRun,seq,scope,keySource_peak,allocArray,note,List.length_cons,List.length_nil]
  omega

def relativeRun (code : Nat) : Nat → Run Int
  | 0 => note 0 [.nat code]
  | i+1 => scope [.nat code,.nat i] (seq (relativeRun code i) fun height =>
    let shifted := code / 2^i
    let up := decide (shifted%2=1)
    note (height + if up then 1 else -1) [.integer height,.nat shifted,.bit up])

theorem relativeRun_value (code i : Nat) :
    (relativeRun code i).value = (MicroExecution.relativeCodeM code i).1 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [relativeRun,seq,scope,note,ih,MicroExecution.relativeCodeM,
      Resources.bind,MicroExecution.counter,MicroExecution.shiftWord,MicroExecution.lowBit,MicroExecution.stepHeight]
    split <;> simp_all

theorem relativeRun_peak (code i : Nat) : (relativeRun code i).peak ≤ 2*i+4 := by
  induction i with
  | zero => simp [relativeRun,note]
  | succ i ih => simp only [relativeRun,scope,seq,note,List.length_cons,List.length_nil]; omega

def canonicalRun (steps code : Nat) : Run (Heights steps) :=
  tabulate 0 (fun i : Fin (steps+1) => relativeRun code i.val)

theorem canonicalRun_value (steps code : Nat) :
    (canonicalRun steps code).value = canonicalHeights steps code := by
  simp only [canonicalRun,tabulate_value,canonicalHeights]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn,relativeRun_value]
  exact MicroExecution.relativeCodeM_value steps code i (by omega)

theorem canonicalRun_peak (steps code : Nat) : (canonicalRun steps code).peak ≤ 16*(steps+1) := by
  have hh := tabulate_peak (0 : Int) (fun i : Fin (steps+1) => relativeRun code i.val)
    (c := 2*steps+4) (fun i => by have := relativeRun_peak code i.val; have := i.isLt; omega)
  unfold canonicalRun
  omega

def sharedRun (steps : Nat) : Run (SharedTable steps) :=
  seq (allocArray (toLex ((0 : Int),(0 : Nat))) (steps+1)) fun seedRow =>
  scope [.ref seedRow] (seq (allocArray seedRow (steps+1)) fun seedClass =>
  scope [.ref seedClass] (tabulate seedClass (fun code : Fin (2^steps) =>
    seq (canonicalRun steps code.val) fun heights => scope [.ref heights] (classRun heights))))

theorem sharedRun_value (steps : Nat) : (sharedRun steps).value = prepareShared steps := by
  simp only [sharedRun,seq,scope,tabulate_value,canonicalRun_value,classRun_value]
  rfl

theorem sharedRun_peak (steps : Nat) : (sharedRun steps).peak ≤ 64*(steps+1) := by
  have hc : ∀ code : Fin (2^steps),
      (seq (canonicalRun steps code.val) fun heights => scope [.ref heights] (classRun heights)).peak ≤ 49*(steps+1) := by
    intro code
    have h₁ := canonicalRun_peak steps code.val
    have h₂ := classRun_peak (canonicalRun steps code.val).value
    simp only [seq,scope,List.length_cons,List.length_nil]
    omega
  have hh := tabulate_peak
    (Vector.replicate (steps+1) (Vector.replicate (steps+1) (toLex ((0 : Int),(0 : Nat)))))
    (fun code : Fin (2^steps) => seq (canonicalRun steps code.val) fun heights => scope [.ref heights] (classRun heights)) hc
  simp only [sharedRun,seq,scope,allocArray,note,List.length_cons,List.length_nil]
  dsimp [seq,scope] at hh
  simp only [Nat.zero_add] at *
  omega

def codeRun (source : Nat → Run Int) (offset : Nat) : Nat → Run Nat
  | 0 => note 0 [.ref source,.nat offset]
  | k+1 => scope [.ref source,.nat offset,.nat k] (seq (source offset) fun a =>
    scope [.integer a] (seq (source (offset+1)) fun b =>
    scope [.integer b,.bit (decide (a<b))] (seq (codeRun source (offset+1) k) fun rest =>
      note ((if a<b then 1 else 0)+2*rest) [.nat rest,.nat (2*rest)])))

theorem codeRun_value (source : Nat → Run Int) (offset steps : Nat) :
    (codeRun source offset steps).value =
      shapeCode (classify steps (fun i => (source (offset+i)).value)) := by
  induction steps generalizing offset with
  | zero => rfl
  | succ k ih =>
    simp only [codeRun,seq,scope,note,ih,shapeCode,classify,Fin.val_zero,Nat.add_zero,Fin.val_succ]
    simp only [Nat.zero_add,decide_eq_true_eq]
    congr 2
    congr 1
    funext i
    simp [classify,Nat.add_comm,Nat.add_left_comm]

theorem codeRun_peak (source : Nat → Run Int) (offset steps : Nat)
    (hc : ∀ i, (source i).peak ≤ c) : (codeRun source offset steps).peak ≤ 8*steps+c+4 := by
  induction steps generalizing offset with
  | zero => simp [codeRun,note]
  | succ k ih =>
    have hr := ih (offset+1)
    have ha := hc offset
    have hb := hc (offset+1)
    simp only [codeRun,seq,scope,note,List.length_cons,List.length_nil]
    omega

def blockAddress (source : Nat → Run Int) (steps block : Nat) : Run (Fin (2^steps)) :=
  let code := scope [.nat block,.nat (block*(steps+1))]
    (codeRun source (block*(steps+1)) steps)
  ⟨⟨code.value, by change (codeRun source _ _).value < _; rw [codeRun_value]; exact shapeCode_lt _⟩,
    code.peak⟩

theorem blockAddress_value (source : Nat → Run Int) (steps block : Nat) :
    (blockAddress source steps block).value =
      classAddress steps (fun i => (source (block*(steps+1)+i)).value) := by
  apply Fin.ext
  exact codeRun_value source _ _

def microRun (source : Nat → Run Int) (steps blocks : Nat) : Run (BlockedRMQ.MicroData steps blocks) :=
  seq (tabulate 0 (fun i : Fin (blocks*(steps+1)) => source i.val)) fun depths =>
  scope [.ref depths] (seq (tabulate (⟨0,Nat.two_pow_pos steps⟩ : Fin (2^steps))
    (fun block : Fin blocks => blockAddress source steps block.val)) fun classes =>
  scope [.ref classes] (seq (sharedRun steps) fun shared => pure ⟨depths,classes,shared⟩))

theorem microRun_value (source : Nat → Run Int) (steps blocks : Nat) :
    (microRun source steps blocks).value = BlockedRMQ.buildMicro (fun i => (source i).value) steps blocks := by
  simp only [microRun,seq,scope,tabulate_value,blockAddress_value,sharedRun_value,pure]
  rfl

theorem microRun_peak (source : Nat → Run Int) (steps blocks : Nat)
    (hc : ∀ i, (source i).peak ≤ 10) : (microRun source steps blocks).peak ≤ 80*(steps+1) := by
  have hd := tabulate_peak (0 : Int) (fun i : Fin (blocks*(steps+1)) => source i.val) (fun i => hc i.val)
  have ha := tabulate_peak (⟨0,Nat.two_pow_pos steps⟩ : Fin (2^steps))
    (fun block : Fin blocks => blockAddress source steps block.val)
    (c := 8*steps+16) (by intro block; have := codeRun_peak source (block.val*(steps+1)) steps hc; change 2+_ ≤ _; omega)
  have hs := sharedRun_peak steps
  simp only [microRun,seq,scope,pure,List.length_cons,List.length_nil]
  omega

def readRun (input : Vector Key n) (i : Fin n) : Run Key :=
  note input[i.val] [.ref input,.nat i.val,.ref input[i.val]]

def rowCellRun (row : Vector Key n) (span : Nat) (i : Fin n) : Run Key :=
  let j := i.val+span
  let j' : Fin n := ⟨j%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
  let a := row[i.val]
  let b := row[j'.val]
  note (min a b) [.ref row,.nat span,.nat i.val,.nat j,.nat j'.val,.ref a,.ref b]

def sparseRows (seed : Key) (input : Vector Key n) :
    (levels : Nat) → Run (Vector (Vector Key n × Nat) (levels+1))
  | 0 => seq (tabulate seed (readRun input)) fun row => note #v[(row,1)] [.ref row,.nat 1]
  | k+1 => scope [.ref seed,.ref input,.nat k] (seq (sparseRows seed input k) fun prev =>
    let desc := prev[k]
    scope [.ref prev,.ref desc.1,.nat desc.2] (seq (tabulate seed (rowCellRun desc.1 desc.2)) fun row =>
      note (prev.push (row,desc.2+desc.2)) [.ref row,.nat (desc.2+desc.2)]))

theorem sparseRows_value (seed : Key) (input : Vector Key n) (levels : Nat) :
    (sparseRows seed input levels).value = (SparseExecution.build seed input levels).1 := by
  induction levels with
  | zero => simp [sparseRows,seq,note,tabulate_value,SparseExecution.build,Resources.bind,
      TableExecution.tabulate_value,readRun,TableExecution.read,lookup]
  | succ k ih =>
    simp only [sparseRows,scope,seq,note,ih,tabulate_value,SparseExecution.build,
      Resources.bind,SparseExecution.nextRow,TableExecution.tabulate_value]
    rfl

theorem sparseRows_peak (seed : Key) (input : Vector Key n) (levels : Nat) :
    (sparseRows seed input levels).peak ≤ 8*(levels+1)+16 := by
  induction levels with
  | zero =>
    have h := tabulate_peak seed (readRun input) (c := 3) (fun _ => le_rfl)
    simp only [sparseRows,seq,note,List.length_cons,List.length_nil]
    omega
  | succ k ih =>
    have h := tabulate_peak seed
      (rowCellRun ((sparseRows seed input k).value[k]).1 ((sparseRows seed input k).value[k]).2)
      (c := 7) (fun _ => le_rfl)
    simp only [sparseRows,scope,seq,note,List.length_cons,List.length_nil]
    omega

def logsRun : (n : Nat) → Run (Vector Nat (n+1))
  | 0 => note #v[0] [.nat 0]
  | k+1 => scope [.nat k] (seq (logsRun k) fun prev =>
      let j := (k+1)/2
      let v := if k=0 then 0 else prev[j]'(by omega)+1
      note (prev.push v) [.ref prev,.nat j,.nat v])

theorem logsRun_value (n : Nat) : (logsRun n).value = (SparseExecution.logs n).1 := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [logsRun,scope,seq,note,ih,SparseExecution.logs,Resources.bind]
                 split <;> rfl

theorem logsRun_peak (n : Nat) : (logsRun n).peak ≤ 4*(n+1) := by
  induction n with
  | zero => simp [logsRun,note]
  | succ k ih => simp only [logsRun,scope,seq,note,List.length_cons,List.length_nil]; omega

def sparseRun (seed : Key) (input : Vector Key n) (levels : Nat) :=
  seq (sparseRows seed input levels) fun rows =>
    scope [.ref rows] (seq (logsRun n) fun logs => pure (rows,logs))

theorem sparseRun_value (seed : Key) (input : Vector Key n) (levels : Nat) :
    (sparseRun seed input levels).value = (SparseExecution.prepare seed input levels).1 := by
  simp [sparseRun,seq,scope,pure,sparseRows_value,logsRun_value,SparseExecution.prepare,Resources.bind,Resources.pure]

theorem sparseRun_peak (seed : Key) (input : Vector Key n) (levels : Nat) :
    (sparseRun seed input levels).peak ≤ 8*(levels+1)+8*(n+1)+32 := by
  have hr := sparseRows_peak seed input levels
  have hl := logsRun_peak n
  simp only [sparseRun,seq,scope,pure,List.length_cons,List.length_nil]
  omega

def withinRun (data : BlockedRMQ.MicroData steps blocks) (hb : 0 < blocks)
    (block offset len : Nat) : Run Key :=
  let r := QueryStorage.withinRun data hb block offset len
  ⟨r.1,r.2.length⟩

theorem withinRun_value (data : BlockedRMQ.MicroData steps blocks) (hb : 0 < blocks)
    (block offset len : Nat) : (withinRun data hb block offset len).value =
      BlockedRMQ.within data hb block offset len := by
  exact (QueryStorage.withinRun_value data hb block offset len).trans
    (BlockedRMQ.withinMeasured_value data hb block offset len)

theorem withinRun_peak (data : BlockedRMQ.MicroData steps blocks) (hb : 0 < blocks)
    (block offset len : Nat) : (withinRun data hb block offset len).peak = 13 :=
  QueryStorage.withinRun_slots data hb block offset len

def prepareRun (source : Nat → Run Int) (steps blocks levels : Nat) (hb : 0 < blocks) :
    Run (BlockedRMQ.Data steps blocks levels) :=
  seq (microRun source steps blocks) fun micro =>
  scope [.ref micro] (seq (tabulate (toLex ((0 : Int),(0 : Nat)))
    (fun block : Fin blocks => withinRun micro hb block.val 0 steps)) fun minima =>
  scope [.ref minima] (seq (sparseRun (toLex (0,0)) minima levels) fun tables =>
    pure ⟨micro,tables.1,tables.2⟩))

theorem prepareRun_value (source : Nat → Run Int) (steps blocks levels : Nat) (hb : 0 < blocks) :
    (prepareRun source steps blocks levels hb).value =
      BlockedRMQ.build (fun i => (source i).value) steps blocks hb levels := by
  simp only [prepareRun,seq,scope,pure,microRun_value,tabulate_value,withinRun_value,sparseRun_value]
  rfl

theorem prepareRun_peak (source : Nat → Run Int) (steps blocks levels : Nat) (hb : 0 < blocks)
    (hc : ∀ i, (source i).peak ≤ 10) :
    (prepareRun source steps blocks levels hb).peak ≤
      max (80*(steps+1)) (8*(levels+1)+8*(blocks+1)+36) := by
  have hm := microRun_peak source steps blocks hc
  have ht := tabulate_peak (toLex ((0 : Int),(0 : Nat)))
    (fun block : Fin blocks => withinRun (microRun source steps blocks).value hb block.val 0 steps)
    (fun block => (withinRun_peak _ hb block.val 0 steps).le)
  have hs := sparseRun_peak (toLex ((0 : Int),(0 : Nat)))
    (tabulate (toLex ((0 : Int),(0 : Nat)))
      (fun block : Fin blocks => withinRun (microRun source steps blocks).value hb block.val 0 steps)).value levels
  simp only [prepareRun,seq,scope,pure,List.length_cons,List.length_nil]
  omega

def selectedRun (source : Nat → Run Int) (n : Nat) :=
  prepareRun source (blockSize n-1) (PreparationBounds.blocks n) (PreparationBounds.levels n)
    (PreparationBounds.blocks_pos n)

theorem selectedRun_value (source : Nat → Run Int) (n : Nat) :
    (selectedRun source n).value = BlockedRMQ.build (fun i => (source i).value)
      (blockSize n-1) (PreparationBounds.blocks n) (PreparationBounds.blocks_pos n)
      (PreparationBounds.levels n) := prepareRun_value _ _ _ _ _

theorem selectedRun_peak (source : Nat → Run Int) (hn : 0 < n)
    (hc : ∀ i, (source i).peak ≤ 10) : (selectedRun source n).peak ≤ 128*n := by
  have h := prepareRun_peak source (blockSize n-1) (PreparationBounds.blocks n)
    (PreparationBounds.levels n) (PreparationBounds.blocks_pos n) hc
  have hb := blockSize_le hn
  have hp := blockSize_pos n
  have hk := PreparationBounds.blocks_le hn
  have hl := Nat.log_le_self 2 (PreparationBounds.blocks n)
  unfold PreparationBounds.levels at h
  change (prepareRun source _ _ _ _).peak ≤ _
  unfold PreparationBounds.levels
  omega

/-- Statement checks: the recursive log prefix includes its unused zero entry;
the selected singleton uses the same source-parametric preparation theorem. -/
example : (logsRun 3).value = #v[0,0,1,1] := by decide
example (source : Nat → Run Int) (hc : ∀ i, (source i).peak ≤ 10) :
    (selectedRun source 1).peak ≤ 128 := by simpa using selectedRun_peak source (by decide : 0 < 1) hc

end Sequences.LCA.Control

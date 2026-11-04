import Applications.Sequences.LCA.Backend
import Applications.Sequences.LCA.Storage

set_option autoImplicit false
set_option warningAsError true

namespace Sequences.LCA.QueryStorage
open Resources BlockedRMQ

/-- Scalar registers and references into the prepared arena. Keys use the
backend's packed-key representation; row/table constructors denote pointers,
not copies of their finite arrays. The word-width certificate is separate. -/
inductive Slot where
  | nat : Nat → Slot
  | integer : Int → Slot
  | bit : Bool → Slot
  | key : Key → Slot
  | row {n : Nat} : Vector Key n → Slot
  | table {s : Nat} : ClassTable s → Slot
  | state {s b l : Nat} : Data s b l → Slot

abbrev Run (α : Type) := α × List Slot

def note {α : Type} (x : α) (slots : List Slot) : Run α := (x,slots)
def bindRun {α β : Type} (a : Run α) (f : α → Run β) : Run β :=
  let b := f a.1
  (b.1,a.2 ++ b.2)
theorem bindRun_value {α β : Type} (a : Run α) (f : α → Run β) :
    (bindRun a f).1 = (f a.1).1 := rfl

theorem measured_value {α β : Type} (a : Measured α Nat) (f : α → Measured β Nat) :
    (Resources.bind a f).1 = (f a.1).1 := rfl

theorem bindRun_slots {α β : Type} (a : Run α) (f : α → Run β) :
    (bindRun a f).2.length = a.2.length + (f a.1).2.length := List.length_append

def scalar (x : Nat) : Run Nat := note x [.nat x]
def key (x : Key) : Run Key := note x [.key x]
def bit (x : Bool) : Run Bool := note x [.bit x]
def index {n : Nat} (x : Fin n) : Run (Fin n) := note x [.nat x.val]

/-- Every result is retained until query return. This deliberately simple
lifetime interpretation gives a bound without relying on register reuse. -/
def withinRun {steps blocks : Nat} (data : MicroData steps blocks) (hb : 0 < blocks)
    (block offset len : Nat) : Run Key :=
  bindRun (index (⟨min block (blocks-1),by omega⟩ : Fin blocks)) fun bi =>
  bindRun (index data.classes[bi.val]) fun code =>
  bindRun (index (⟨min offset steps,by omega⟩ : Fin (steps+1))) fun oi =>
  bindRun (index (⟨min len steps,by omega⟩ : Fin (steps+1))) fun li =>
  bindRun (note data.shared[code.val] [.table data.shared[code.val]]) fun table =>
  bindRun (note table[oi.val] [.row table[oi.val]]) fun row =>
  bindRun (key row[li.val]) fun k =>
  bindRun (scalar (ofLex k).2) fun relativeIndex =>
  bindRun (scalar (block*(steps+1))) fun base =>
  bindRun (scalar (base+relativeIndex)) fun global =>
  bindRun (index (⟨min global (blocks*(steps+1)-1),by
    have := Nat.mul_pos hb (show 0<steps+1 by omega)
    omega⟩ : Fin (blocks*(steps+1)))) fun gi =>
  bindRun (note data.depths[gi.val] [.integer data.depths[gi.val]]) fun d =>
  key (toLex (d,global))

theorem withinRun_value {steps blocks : Nat} (data : MicroData steps blocks) (hb : 0 < blocks)
    (block offset len : Nat) : (withinRun data hb block offset len).1 =
      (withinMeasured data hb block offset len).1 := rfl

theorem withinRun_slots {steps blocks : Nat} (data : MicroData steps blocks) (hb : 0 < blocks)
    (block offset len : Nat) : (withinRun data hb block offset len).2.length = 13 := rfl

def sparseRun {n levels : Nat} (table : Vector (Vector Key n × Nat) (levels+1))
    (logs : Vector Nat (n+1)) (start : Fin n) (len : Fin (n+1)) : Run Key :=
  bindRun (scalar logs[len.val]) fun k =>
  bindRun (index (⟨min k levels,by omega⟩ : Fin (levels+1))) fun level =>
  bindRun (note table[level.val] [.row table[level.val].1,.nat table[level.val].2]) fun desc =>
  bindRun (scalar (start.val+len.val)) fun stop =>
  bindRun (scalar (stop-desc.2)) fun second =>
  bindRun (index (⟨min second (n-1),by have := start.isLt; omega⟩ : Fin n)) fun right =>
  bindRun (key desc.1[start.val]) fun a =>
  bindRun (key desc.1[right.val]) fun b => key (min a b)

theorem sparseRun_value {n levels : Nat} (table : Vector (Vector Key n × Nat) (levels+1))
    (logs : Vector Nat (n+1)) (start : Fin n) (len : Fin (n+1)) :
    (sparseRun table logs start len).1 = (SparseExecution.query table logs start len).1 := rfl

theorem sparseRun_slots {n levels : Nat} (table : Vector (Vector Key n × Nat) (levels+1))
    (logs : Vector Nat (n+1)) (start : Fin n) (len : Fin (n+1)) :
    (sparseRun table logs start len).2.length = 10 := rfl

def summaryRun {steps blocks levels : Nat} (data : Data steps blocks levels) (hb : 0 < blocks)
    (start count : Nat) : Run Key :=
  bindRun (index (⟨min start (blocks-1),by omega⟩ : Fin blocks)) fun si =>
  bindRun (scalar (count+1)) fun len =>
  bindRun (index (⟨min len blocks,by omega⟩ : Fin (blocks+1))) fun li =>
  sparseRun data.macroRows data.macroLogs si li

theorem summaryRun_value {steps blocks levels : Nat} (data : Data steps blocks levels) (hb : 0 < blocks)
    (start count : Nat) : (summaryRun data hb start count).1 =
      (summaryMeasured data hb start count).1 := rfl

theorem summaryRun_slots {steps blocks levels : Nat} (data : Data steps blocks levels) (hb : 0 < blocks)
    (start count : Nat) : (summaryRun data hb start count).2.length = 13 := rfl

def queryKeyRun {steps blocks levels : Nat} (data : Data steps blocks levels) (hb : 0 < blocks)
    (lo hi : Nat) : Run Key :=
  bindRun (scalar (lo/(steps+1))) fun first =>
  bindRun (scalar (hi/(steps+1))) fun last =>
  bindRun (bit (decide (first=last))) fun same =>
  if same then
    bindRun (scalar (lo%(steps+1))) fun offset =>
    bindRun (scalar (hi-lo)) fun len => withinRun data.micro hb first offset len
  else
    bindRun (scalar (lo%(steps+1))) fun offset =>
    bindRun (scalar (steps-offset)) fun leftLen =>
    bindRun (withinRun data.micro hb first offset leftLen) fun left =>
    bindRun (scalar (hi%(steps+1))) fun rightLen =>
    bindRun (withinRun data.micro hb last 0 rightLen) fun right =>
    bindRun (scalar (first+1)) fun next =>
    bindRun (bit (decide (last=next))) fun adjacent =>
    if adjacent then key (min left right)
    else
      bindRun (scalar (last-first)) fun gap =>
      bindRun (scalar (gap-2)) fun middleLen =>
      bindRun (summaryRun data hb next middleLen) fun middle =>
      bindRun (key (min middle right)) fun rest => key (min left rest)

set_option maxRecDepth 4096 in
theorem queryKeyRun_value {steps blocks levels : Nat} (data : Data steps blocks levels) (hb : 0 < blocks)
    (lo hi : Nat) : (queryKeyRun data hb lo hi).1 = (queryKeyMeasured data hb lo hi).1 := by
  dsimp only [queryKeyRun, queryKeyMeasured, bindRun, scalar, note, bit, Resources.bind]
  split_ifs <;> rfl

theorem queryKeyRun_slots {steps blocks levels : Nat} (data : Data steps blocks levels) (hb : 0 < blocks)
    (lo hi : Nat) : (queryKeyRun data hb lo hi).2.length ≤ 51 := by
  cases hs : decide (lo/(steps+1)=hi/(steps+1)) <;>
    cases ha : decide (hi/(steps+1)=lo/(steps+1)+1) <;>
    simp only [queryKeyRun, bindRun_slots, scalar, note, bit, hs, ha, key,
      Bool.false_eq_true, ite_false, ite_true, List.length_cons, List.length_nil,
      withinRun_slots, summaryRun_slots] <;> omega

def queryRun {steps blocks levels : Nat} (data : Data steps blocks levels) (hb : 0 < blocks)
    (lo hi : Nat) : Run Nat :=
  bindRun (queryKeyRun data hb lo hi) fun k => scalar (ofLex k).2

theorem queryRun_value {steps blocks levels : Nat} (data : Data steps blocks levels) (hb : 0 < blocks)
    (lo hi : Nat) : (queryRun data hb lo hi).1 = (queryMeasured data hb lo hi).1 := by
  simp only [queryRun, queryMeasured, bindRun, scalar, note, Resources.bind, queryKeyRun_value]

theorem queryRun_slots {steps blocks levels : Nat} (data : Data steps blocks levels) (hb : 0 < blocks)
    (lo hi : Nat) : (queryRun data hb lo hi).2.length ≤ 52 := by
  have hh := queryKeyRun_slots data hb lo hi
  simpa only [queryRun, bindRun, scalar, note, List.length_append, List.length_cons, List.length_nil] using Nat.add_le_add_right hh 1

/-- The wrapper retains its input references, endpoints and two guard results
alongside the backend trace. Invalid intervals return before table reads. -/
def answerRun {m : Nat} (data : Backend.State m) (q : Nat × Nat) : Run Nat :=
  bindRun (note () [.state data,.nat q.1,.nat q.2]) fun _ =>
  bindRun (bit (decide (q.1 ≤ q.2))) fun ordered =>
  bindRun (bit (decide (q.2<m))) fun bounded =>
  if ordered && bounded then queryRun data (PreparationBounds.blocks_pos m) q.1 q.2
  else scalar 0

theorem answerRun_value {m : Nat} (data : Backend.State m) (q : Nat × Nat) :
    (answerRun data q).1 = (Backend.answerM data q).1 := by
  by_cases h : q.1 ≤ q.2 ∧ q.2<m
  · simp [answerRun, Backend.answerM, bindRun, bit, note, Resources.bind,
      TreeBackend.dispatch, h.1, h.2, queryRun_value]
  · have hb : (decide (q.1 ≤ q.2) && decide (q.2<m)) = false := by
      by_cases hl : q.1 ≤ q.2 <;> by_cases hh : q.2<m <;> simp_all
    simp [answerRun, Backend.answerM, bindRun, bit, note, Resources.bind,
      TreeBackend.dispatch, hb, scalar, Resources.pure]

theorem answerRun_slots {m : Nat} (data : Backend.State m) (q : Nat × Nat) :
    (answerRun data q).2.length ≤ 57 := by
  have hh := queryRun_slots data (PreparationBounds.blocks_pos m) q.1 q.2
  by_cases h : q.1 ≤ q.2 ∧ q.2<m
  · simpa only [answerRun, bindRun, bit, note, h.1, h.2, decide_true, Bool.and_self,
      ite_true, List.length_append, List.length_cons, List.length_nil] using
      (show 3+(1+(1+(queryRun data (PreparationBounds.blocks_pos m) q.1 q.2).2.length))≤57 by omega)
  · have hb : (decide (q.1 ≤ q.2) && decide (q.2<m)) = false := by
      by_cases hl : q.1 ≤ q.2 <;> by_cases hh : q.2<m <;> simp_all
    simp [answerRun, bindRun, bit, note, hb, scalar]

/-- Maximum actual trace length over the finite admitted address domain, plus
six slots for any rejected query (whose endpoints need not fit the domain). -/
def answerPeak {m : Nat} (data : Backend.State m) : Nat :=
  max 6 (Finset.univ.sup fun q : Fin m × Fin m => (answerRun data (q.1.val,q.2.val)).2.length)

theorem answerPeak_le {m : Nat} (data : Backend.State m) : answerPeak data ≤ 57 := by
  apply max_le (by decide)
  apply Finset.sup_le
  intro q _
  exact answerRun_slots data _

theorem answerRun_fits {m : Nat} (data : Backend.State m) (q : Nat × Nat) :
    (answerRun data q).2.length ≤ answerPeak data := by
  by_cases h : q.1 ≤ q.2 ∧ q.2<m
  · have hq : q.1<m := by omega
    exact (Finset.le_sup (f := fun p : Fin m × Fin m => (answerRun data (p.1.val,p.2.val)).2.length)
      (Finset.mem_univ (⟨q.1,hq⟩,⟨q.2,h.2⟩))).trans (le_max_right _ _)
  · have hb : (decide (q.1 ≤ q.2) && decide (q.2<m)) = false := by
      by_cases hl : q.1 ≤ q.2 <;> by_cases hh : q.2<m <;> simp_all
    simpa only [answerRun, bindRun, bit, note, hb, Bool.false_eq_true, ite_false, scalar,
      List.length_append, List.length_cons, List.length_nil] using
      (show 6 ≤ answerPeak data from le_max_left _ _)

theorem every_prefix_fits {m : Nat} (data : Backend.State m) (q : Nat × Nat) (k : Nat) :
    ((answerRun data q).2.take k).length ≤ answerPeak data :=
  (by simp only [List.length_take]; exact (min_le_right _ _).trans (answerRun_fits data q))

def queryPeak {m : Nat} (data : Backend.State m) : Nat := Storage.dataWords data + answerPeak data

theorem queryPeak_le {m : Nat} (hm : 0<m) (data : Backend.State m) : queryPeak data ≤ 128*m := by
  have hd := (Storage.dataWords_le hm data).trans (PreparationBounds.retainedSlots_le hm)
  have hs := answerPeak_le data
  unfold queryPeak
  omega

end Sequences.LCA.QueryStorage

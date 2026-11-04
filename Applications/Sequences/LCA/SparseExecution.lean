import Applications.Sequences.LCA.FiniteSparse
import Applications.Sequences.LCA.TableExecution

/-! Indexed sparse-table execution. Costs count word arithmetic, comparisons,
reads and slot writes. Vector push denotes initializing the next reserved slot,
not a claim about native persistent-array copying. Row descriptors contain a
row address and its power-of-two span; spans are obtained by doubling. -/
namespace Sequences.LCA.SparseExecution
open Resources Dijkstra.Store TableExecution
variable {α : Type} [LinearOrder α]

/-- A floor-log table, including the unused zero-length entry. Each new entry
reads a strictly earlier slot. Division by two is a word shift. -/
def logs : (n : Nat) → Measured (Vector Nat (n+1)) Nat
  | 0 => (#v[0], 1)
  | k+1 => bind (logs k) fun prev =>
    bind (if k = 0 then (0, 1) else
      bind ((⟨(k+1)/2, by omega⟩, 1) : Measured (Fin (k+1)) Nat) fun j =>
      bind (TableExecution.read prev j) fun v => (v+1, 2)) fun v =>
    (prev.push v, 1)

private theorem log_recur (k : Nat) (hk : k ≠ 0) :
    Nat.log 2 ((k+1)/2) + 1 = Nat.log 2 (k+1) := by
  rw [Nat.log_div_base]
  have hp := Nat.log_pos (by decide : 1 < 2) (show 2 ≤ k+1 by omega)
  omega

theorem logs_get (n : Nat) (i : Fin (n+1)) :
    (logs n).1[i.val] = Nat.log 2 i.val := by
  induction n with
  | zero =>
    have hi : i.val = 0 := by omega
    simp [logs]
  | succ n ih =>
    by_cases hi : i.val < n+1
    · simpa [logs, Resources.bind, hi, Nat.ne_of_lt hi] using ih ⟨i.val, hi⟩
    · have he : i.val = n+1 := by omega
      simp only [logs, Resources.bind, he, Vector.getElem_push_eq]
      by_cases hn : n = 0
      · subst n; simp
      · simp only [hn, ↓reduceIte, TableExecution.read, lookup]
        have hd : (n+1)/2 ≤ n := by omega
        rw [ih ⟨(n+1)/2, by omega⟩]
        exact log_recur n hn

theorem logs_cost (n : Nat) : (logs n).2 ≤ 1 + 5*n := by
  induction n with
  | zero => simp [logs]
  | succ n ih =>
    by_cases hn : n = 0 <;> simp [logs, Resources.bind, hn, TableExecution.read] <;> omega

/-- Compute one next row from the stored preceding row, charging address
addition, remainder, two reads and the ordered-cell comparison. -/
def rowCell (row : Vector α n) (span : Nat) (i : Fin n) : Measured α Nat :=
  bind ((i.val + span, 1) : Measured Nat Nat) fun j =>
  bind ((⟨j % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩, 1) :
    Measured (Fin n) Nat) fun j' =>
  bind (TableExecution.read row i) fun a =>
  bind (TableExecution.read row j') fun b =>
  (min a b, 1)

theorem rowCell_value (row : Vector α n) (span : Nat) (i : Fin n) :
    (rowCell row span i).1 = min row[i.val]
      (row[(i.val+span)%n]'(Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt))) := by
  rfl

theorem rowCell_cost (row : Vector α n) (span : Nat) (i : Fin n) :
    (rowCell row span i).2 = 5 := rfl

def nextRow (seed : α) (row : Vector α n) (span : Nat) : Measured (Vector α n) Nat :=
  tabulate seed (rowCell row span)

theorem nextRow_value (seed : α) (row : Vector α n) (k : Nat) :
    (nextRow seed row (2^k)).1 = nextSparseRow row k := by
  rw [nextRow, tabulate_value]
  apply Vector.ext
  intro i hi
  simp [nextSparseRow, rowCell_value]

theorem nextRow_cost (seed : α) (row : Vector α n) (span : Nat) :
    (nextRow seed row span).2 ≤ 7*n := by
  simpa [nextRow, Nat.mul_comm] using
    tabulate_cost seed (rowCell row span) 5 (fun i => (rowCell_cost row span i).le)

/-- Each descriptor holds a row pointer and span. The base row is copied into
owned initialized slots. At each step only the latest descriptor is read. -/
def build (seed : α) (input : Vector α n) :
    (levels : Nat) → Measured (Vector (Vector α n × Nat) (levels+1)) Nat
  | 0 => bind (tabulate seed (TableExecution.read input)) fun row => (#v[(row,1)], 2)
  | k+1 => bind (build seed input k) fun prev =>
    bind ((prev[k], 2) : Measured (Vector α n × Nat) Nat) fun desc =>
    bind (nextRow seed desc.1 desc.2) fun row =>
    bind ((desc.2+desc.2, 1) : Measured Nat Nat) fun span =>
    (prev.push (row,span), 2)

theorem build_get (seed : α) (input : Vector α n) (levels : Nat)
    (k : Fin (levels+1)) :
    (build seed input levels).1[k.val] = (finiteRow input k.val, 2^k.val) := by
  induction levels with
  | zero =>
    have hk : k.val = 0 := by omega
    simp [build, Resources.bind, tabulate_value, TableExecution.read, lookup, finiteRow]
  | succ levels ih =>
    by_cases hk : k.val < levels+1
    · simpa [build, Resources.bind, hk, Nat.ne_of_lt hk] using ih ⟨k.val,hk⟩
    · have he : k.val = levels+1 := by omega
      simp only [build, Resources.bind, he, Vector.getElem_push_eq]
      rw [ih ⟨levels, by omega⟩, nextRow_value]
      simp [finiteRow, pow_succ, Nat.mul_two]

theorem build_rows (seed : α) (input : Vector α n) (levels : Nat) :
    (build seed input levels).1.map Prod.fst = buildSparse input levels := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  rw [build_get seed input levels ⟨i,hi⟩, buildSparse_get input levels ⟨i,hi⟩]

theorem build_cost (seed : α) (input : Vector α n) (levels : Nat) :
    (build seed input levels).2 ≤ 3*n + 2 + levels*(7*n+5) := by
  induction levels with
  | zero =>
    have hh := tabulate_cost seed (TableExecution.read input) 1 (fun _ => by rfl)
    simp only [build, Resources.bind]
    omega
  | succ k ih =>
    have hh := nextRow_cost seed ((build seed input k).1[k]).1
      ((build seed input k).1[k]).2
    simp only [build, Resources.bind]
    nlinarith

/-- The query uses only prepared slots. Clipping makes every address safe even
for malformed table contents; correctness below proves clipping inactive for
prepared tables. No allocation or table writes occur in this program. -/
def query (table : Vector (Vector α n × Nat) (levels+1))
    (logTable : Vector Nat (n+1)) (start : Fin n) (len : Fin (n+1)) :
    Measured α Nat :=
  bind (TableExecution.read logTable len) fun k =>
  bind ((⟨min k levels, by omega⟩, 1) : Measured (Fin (levels+1)) Nat) fun level =>
  bind ((table[level.val], 2) : Measured (Vector α n × Nat) Nat) fun desc =>
  bind ((start.val + len.val, 1) : Measured Nat Nat) fun stop =>
  bind ((stop - desc.2, 1) : Measured Nat Nat) fun second =>
  bind ((⟨min second (n-1), by have := start.isLt; omega⟩, 1) :
    Measured (Fin n) Nat) fun right =>
  bind (TableExecution.read desc.1 start) fun a =>
  bind (TableExecution.read desc.1 right) fun b => (min a b, 1)

theorem query_cost (table : Vector (Vector α n × Nat) (levels+1))
    (logTable : Vector Nat (n+1)) (start : Fin n) (len : Fin (n+1)) :
    (query table logTable start len).2 = 10 := rfl

theorem query_correct (seed : α) (input : Vector α n) (levels : Nat)
    (start : Fin n) (len : Fin (n+1)) (hl : 0 < len.val)
    (hend : start.val + len.val ≤ n) (hk : Nat.log 2 len.val ≤ levels) :
    (query (build seed input levels).1 (logs n).1 start len).1 =
      PreparedRMQ.rangeMin (vectorRead input (Nat.zero_lt_of_lt start.isLt))
        start.val (len.val-1) := by
  have hp := Nat.two_pow_pos (Nat.log 2 len.val)
  have hpl := Nat.pow_log_le_self 2 (show len.val ≠ 0 by omega)
  have hs : start.val + 2 ^ Nat.log 2 len.val ≤ n := by omega
  have hr : start.val + len.val - 2 ^ Nat.log 2 len.val < n := by omega
  simp only [query, Resources.bind, TableExecution.read, lookup]
  simp only [logs_get, min_eq_left hk]
  simp only [build_get seed input levels ⟨Nat.log 2 len.val, by omega⟩]
  simp only [min_eq_left (show start.val + len.val - 2 ^ Nat.log 2 len.val ≤ n-1 by omega)]
  rw [finiteRow_correct input (Nat.zero_lt_of_lt start.isLt) _ start hs,
    finiteRow_correct input (Nat.zero_lt_of_lt start.isLt) _
      ⟨start.val + len.val - 2 ^ Nat.log 2 len.val, hr⟩ (by simp only; omega)]
  exact sparse_query_correct _ _ _ hl

/-- This copy-owning builder retains all rows. The descriptor arena has two
words per level; the log arena has n+1 words. Input storage is external. -/
def retainedSlots (n levels : Nat) : Nat := (levels+1)*(n+2) + (n+1)

/-- The reserved arenas are initialized once and filled in place. Construction
uses the retained arena plus the borrowed input and six scratch words. This
formula counts the simultaneously live input even after its base-row copy. -/
def peakSlots (n levels : Nat) : Nat := retainedSlots n levels + n + 6

def prepare (seed : α) (input : Vector α n) (levels : Nat) :
    Measured (Vector (Vector α n × Nat) (levels+1) × Vector Nat (n+1)) Nat :=
  bind (build seed input levels) fun table =>
  bind (logs n) fun logTable => pure (table, logTable)

theorem prepare_cost (seed : α) (input : Vector α n) (levels : Nat) :
    (prepare seed input levels).2 ≤ 8*n + 3 + levels*(7*n+5) := by
  have hb := build_cost seed input levels
  have hl := logs_cost n
  simp only [prepare, Resources.bind, Resources.pure]
  omega

/-- Concrete arena layout: each level occupies its two-word descriptor followed
by its n cells; the log arena follows the last row. -/
def rowAddress (level : Fin (levels+1)) (i : Fin n) : Fin (retainedSlots n levels) :=
  ⟨level.val*(n+2)+2+i.val, by
    have h := Nat.mul_le_mul_right (n+2) (show level.val+1 ≤ levels+1 by omega)
    unfold retainedSlots
    nlinarith [i.isLt]⟩

def descriptorAddress (n : Nat) (level : Fin (levels+1)) (field : Fin 2) :
    Fin (retainedSlots n levels) :=
  ⟨level.val*(n+2)+field.val, by
    have h := Nat.mul_le_mul_right (n+2) (show level.val+1 ≤ levels+1 by omega)
    unfold retainedSlots
    nlinarith [field.isLt]⟩

def logAddress (levels : Nat) (i : Fin (n+1)) : Fin (retainedSlots n levels) :=
  ⟨(levels+1)*(n+2)+i.val, by unfold retainedSlots; omega⟩

/-- A construction prefix retains k+1 complete rows, at most the full log
arena, the borrowed input and the six scratch words. Initialization of the
next row is included by taking its level as k. -/
theorem prefix_capacity (n levels k logWords : Nat) (hk : k ≤ levels)
    (hl : logWords ≤ n+1) :
    (k+1)*(n+2) + logWords + n + 6 ≤ peakSlots n levels := by
  have hh := Nat.mul_le_mul_right (n+2) (show k+1 ≤ levels+1 by omega)
  unfold peakSlots retainedSlots
  omega

/-- The width requirement bounds intermediate additions, not just stored
indices. Ordered payload encoding is supplied by the caller. -/
structure Eligible (n levels width capacity : Nat) : Prop where
  memory : peakSlots n levels ≤ capacity
  address : capacity ≤ 2^width
  arithmetic : n + 2^levels < 2^width

theorem row_add_fits (h : Eligible n levels width capacity)
    (i : Fin n) (k : Nat) (hk : k ≤ levels) : i.val + 2^k < 2^width := by
  have hp : 2^k ≤ 2^levels := Nat.pow_le_pow_right (by decide) hk
  have hh := h.arithmetic
  omega

theorem double_fits (h : Eligible n levels width capacity)
    (k : Nat) (hk : k < levels) : 2^k + 2^k < 2^width := by
  have hp : 2^(k+1) ≤ 2^levels := Nat.pow_le_pow_right (by decide) (by omega)
  rw [pow_succ, Nat.mul_two] at hp
  have hh := h.arithmetic
  omega

theorem address_fits (h : Eligible n levels width capacity)
    (i : Fin (retainedSlots n levels)) : i.val < 2^width := by
  have hm := h.memory
  have ha := h.address
  unfold peakSlots at hm
  omega

theorem query_prepared (seed : α) (input : Vector α n) (levels : Nat)
    (start : Fin n) (len : Fin (n+1)) (hl : 0 < len.val)
    (hend : start.val + len.val ≤ n) (hk : Nat.log 2 n ≤ levels) :
    (query (prepare seed input levels).1.1 (prepare seed input levels).1.2 start len).1 =
      PreparedRMQ.rangeMin (vectorRead input (Nat.zero_lt_of_lt start.isLt))
        start.val (len.val-1) := by
  apply query_correct seed input levels start len hl hend
  exact (Nat.log_mono_right (show len.val ≤ n by omega)).trans hk

/-- Singleton storage and arithmetic fit a concrete finite machine. -/
example : Eligible 1 0 4 12 := by constructor <;> decide
example : ¬ Eligible 1 0 4 10 := by
  intro h
  have := h.memory
  norm_num [peakSlots, retainedSlots] at this

/-- Duplicate minima and overlapping ranges retain the expected minimum. -/
example :
    (query (build (0 : Nat) #v[5,2,2,9] 2).1 (logs 4).1
      ⟨0, by decide⟩ ⟨3, by decide⟩).1 = 2 := by
  rw [query_correct 0 #v[5,2,2,9] 2 ⟨0, by decide⟩ ⟨3, by decide⟩
    (by decide) (by decide) (by decide)]
  decide

example : (logs 8).1[8] = 3 := by rw [logs_get 8 ⟨8, by decide⟩]; decide

end Sequences.LCA.SparseExecution

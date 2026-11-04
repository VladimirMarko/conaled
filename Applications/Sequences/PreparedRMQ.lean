import Applications.Resources.Prepared
import Applications.Sequences.RangeMinimum

/-! A small sparse table with power-of-two rows of lengths four, three and one.
The value order may be a lexicographic (depth,index) order for leftmost argmin.
The independent specification scans the requested inclusive interval. -/
namespace Sequences.PreparedRMQ
open Resources Resources.Prepared
variable {α : Type} [LinearOrder α]

inductive Query where
  | q00 | q01 | q02 | q03 | q11 | q12 | q13 | q22 | q23 | q33
  deriving DecidableEq, Repr

instance : Fintype Query where
  elems := {.q00, .q01, .q02, .q03, .q11, .q12, .q13, .q22, .q23, .q33}
  complete q := by cases q <;> simp

def Query.lo : Query → Fin 4
  | .q00 | .q01 | .q02 | .q03 => 0
  | .q11 | .q12 | .q13 => 1
  | .q22 | .q23 => 2
  | .q33 => 3

def Query.hi : Query → Fin 4
  | .q00 => 0
  | .q01 | .q11 => 1
  | .q02 | .q12 | .q22 => 2
  | .q03 | .q13 | .q23 | .q33 => 3

theorem Query.ordered (q : Query) : q.lo ≤ q.hi := by cases q <;> decide

abbrev Input (α : Type) := Vector α 4

def spec (xs : Input α) (q : Query) : α :=
  rangeMin (fun i => xs.get ⟨i % 4, Nat.mod_lt _ (by decide)⟩) q.lo.val (q.hi.val-q.lo.val)

structure Table (α : Type) where
  singles : Vector α 4
  pairs : Vector α 3
  whole : α

def build (xs : Input α) : Table α :=
  let pairs := #v[min xs[0] xs[1], min xs[1] xs[2], min xs[2] xs[3]]
  ⟨xs,pairs,min pairs[0] pairs[2]⟩

/-- Length-three queries deliberately overlap, requiring idempotence. -/
def lookup (t : Table α) (q : Query) : α :=
  if q.lo = q.hi then t.singles.get q.lo
  else if hlen : q.hi.val - q.lo.val = 1 then t.pairs.get ⟨q.lo.val, by
    have := q.hi.isLt; have := q.ordered; omega⟩
  else if hlen : q.hi.val - q.lo.val = 2 then
    min (t.pairs.get ⟨q.lo.val, by have := q.hi.isLt; omega⟩)
      (t.pairs.get ⟨q.hi.val-1, by have := q.hi.isLt; omega⟩)
  else t.whole

theorem overlap (a b c : α) : min (min a b) (min b c) = min (min a b) c := by
  rw [min_assoc, ← min_assoc b b c, min_self, ← min_assoc]

theorem lookup_build (xs : Input α) (q : Query) : lookup (build xs) q = spec xs q := by
  cases q with
  | q00 => rfl
  | q01 => rfl
  | q02 => exact overlap xs[0] xs[1] xs[2]
  | q03 => exact (min_assoc (min xs[0] xs[1]) xs[2] xs[3]).symm
  | q11 => rfl
  | q12 => rfl
  | q13 => exact overlap xs[1] xs[2] xs[3]
  | q22 => rfl
  | q23 => rfl
  | q33 => rfl

/-- Instrument the same inclusive scan with one cell read for the first
value, then one read and one comparison for each following value. -/
def rangeMinM (read : Nat → α) (start : Nat) : Nat → Measured α Nat
  | 0 => (read start,1)
  | n+1 => bind (rangeMinM read start n) fun a => (min a (read (start+n+1)),2)

theorem rangeMinM_exact (read : Nat → α) (start n : Nat) :
    rangeMinM read start n = (rangeMin read start n,2*n+1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rangeMinM,rangeMin,Resources.bind,ih]; omega

/-- Each materialized minimum performs two indexed reads, a comparison, and
one cell write. The input vector is retained as row zero without copying. -/
def cell (a b : α) : Measured α Nat := (min a b,4)
def buildM (xs : Input α) : Measured (Table α) Nat :=
  bind (cell xs[0] xs[1]) fun a =>
  bind (cell xs[1] xs[2]) fun b =>
  bind (cell xs[2] xs[3]) fun c =>
  bind (cell a c) fun d => pure ⟨xs,#v[a,b,c],d⟩

theorem buildM_exact (xs : Input α) : buildM xs = (build xs,16) := rfl

def direct : Ops (Input α) Query α (Input α) where
  prepare xs := (xs,0)
  answer xs q := rangeMinM (fun i => xs.get ⟨i % 4, Nat.mod_lt _ (by decide)⟩)
    q.lo.val (q.hi.val-q.lo.val)

def sparse : Ops (Input α) Query α (Table α) where
  prepare := buildM
  answer t q := (lookup t q, if q.hi.val-q.lo.val = 2 then 3 else 1)

theorem directLaws : Laws spec (direct (α := α)) (fun s r => r = s) where
  prepare _ := rfl
  answer s r h q := by subst r; simp [direct,rangeMinM_exact,spec]

theorem sparseLaws : Laws spec (sparse (α := α)) (fun s r => r = build s) where
  prepare _ := rfl
  answer s r h q := by subst r; exact lookup_build s q

/-- Abstract cells plus two scratch values; indices/control registers are
outside this cell observation. No byte-size claim for arbitrary α. -/
def directProfile : Profile (Input α) := ⟨fun _ => 0, fun _ => 7, fun _ => 0,
  fun _ => 4, fun _ => 6⟩
def sparseProfile : Profile (Input α) := ⟨fun _ => 16, fun _ => 3, fun _ => 0,
  fun _ => 8, fun _ => 10⟩

def directStorage : Storage (Input α) (Input α) := ⟨fun xs => xs.size,fun xs => xs.size,fun xs => xs.size+2⟩
def sparseStorage : Storage (Input α) (Table α) := ⟨fun t => t.singles.size+t.pairs.size+1,fun xs => xs.size+3+1+2,
  fun t => t.singles.size+t.pairs.size+1+2⟩

theorem directBounds : Bounds (direct (α := α)) (fun s r => r = s) directStorage directProfile where
  preparation _ := le_rfl
  query s r _ q := by
    simp only [direct,rangeMinM_exact,directProfile]
    have := q.hi.isLt
    omega
  retained _ _ _ := le_rfl
  preparePeak _ := by change 4 ≤ 6; omega
  queryPeak _ _ _ := le_rfl

theorem sparseBounds : Bounds (sparse (α := α)) (fun s r => r = build s) sparseStorage sparseProfile where
  preparation _ := le_rfl
  query _ _ _ q := by change (if q.hi.val-q.lo.val = 2 then 3 else 1) ≤ 3; split <;> decide
  retained _ _ _ := le_rfl
  preparePeak _ := le_rfl
  queryPeak _ _ _ := le_rfl

end Sequences.PreparedRMQ

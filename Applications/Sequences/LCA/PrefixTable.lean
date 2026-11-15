import Applications.Sequences.LCA.Sparse
import Applications.Resources.Measured

/-! Running-minimum table rows. Each next entry uses the previous minimum and
one new input, rather than recomputing a query scan from scratch. -/
namespace Sequences.LCA
open PreparedRMQ Resources
variable {α : Type} [LinearOrder α]

/-- Include the current minimum, then consume successive inputs. -/
def scanMin (read : Nat → α) (next : Nat) (current : α) : Nat → List α
  | 0 => [current]
  | n+1 => current :: scanMin read (next+1) (min current (read next)) n

theorem scanMin_length (read : Nat → α) (next : Nat) (current : α) (n : Nat) :
    (scanMin read next current n).length = n+1 := by
  induction n generalizing next current with
  | zero => rfl
  | succ n ih => simp [scanMin, ih]

theorem scanMin_eq (read : Nat → α) (start i n : Nat) :
    scanMin read (start+i+1) (rangeMin read start i) n =
      List.ofFn (fun j : Fin (n+1) => rangeMin read start (i+j.val)) := by
  induction n generalizing i with
  | zero => simp [scanMin, List.ofFn_succ]
  | succ n ih =>
    simp only [scanMin, List.ofFn_succ, Fin.val_zero, Nat.add_zero, Fin.val_succ]
    congr 1
    simpa [rangeMin, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (i+1)

/-- The target's primitives are one indexed read, one comparison, and one
output-cell write. Values flow through these primitives into the output. -/
def readCell (read : Nat → α) (i : Nat) : Measured α Nat := (read i, 1)
def minimumCell (a b : α) : Measured α Nat := (min a b, 1)
def writeCell (a : α) : Measured α Nat := (a, 1)

def scanMinM (read : Nat → α) (next : Nat) (current : α) : Nat → Measured (List α) Nat
  | 0 => bind (writeCell current) fun x => pure [x]
  | n+1 => bind (writeCell current) fun x =>
      bind (readCell read next) fun y =>
      bind (minimumCell current y) fun z =>
      bind (scanMinM read (next+1) z n) fun rest => pure (x :: rest)

theorem scanMinM_exact (read : Nat → α) (next : Nat) (current : α) (n : Nat) :
    scanMinM read next current n = (scanMin read next current n, 3*n+1) := by
  induction n generalizing next current with
  | zero => rfl
  | succ n ih => simp [scanMinM, scanMin, readCell, minimumCell, writeCell, Resources.bind, Resources.pure, ih]; omega

def prefixRow (read : Nat → α) (start n : Nat) : Vector α (n+1) :=
  ⟨(scanMin read (start+1) (read start) n).toArray, by simp [scanMin_length]⟩

theorem prefixRow_get (read : Nat → α) (start n : Nat) (i : Fin (n+1)) :
    (prefixRow read start n).get i = rangeMin read start i.val := by
  have he := scanMin_eq read start 0 n
  simp only [Nat.add_zero, rangeMin] at he
  change (scanMin read (start+1) (read start) n)[i.val]'(by rw [scanMin_length]; exact i.isLt) = _
  simp only [he, List.getElem_ofFn, Nat.zero_add]

end Sequences.LCA

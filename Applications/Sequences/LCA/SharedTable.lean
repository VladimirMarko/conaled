import Applications.Sequences.LCA.Micro
import Applications.Sequences.LCA.PrefixTable

/-! Finite shared within-block tables. Rows are built by cumulative scans;
querying the representation performs two indexed reads. -/
namespace Sequences.LCA
open PreparedRMQ

@[simp] theorem vectorGet_ofFn (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  change (Vector.ofFn f)[i.val] = _
  simp only [Vector.getElem_ofFn]


abbrev Heights (steps : Nat) := Vector Int (steps+1)
abbrev ClassTable (steps : Nat) := Vector (Vector (Int ×ₗ Nat) (steps+1)) (steps+1)
abbrev SharedTable (steps : Nat) := Vector (ClassTable steps) (2 ^ steps)

def boundedDepth (heights : Heights steps) (i : Nat) : Int :=
  heights.get ⟨min i steps, by omega⟩

def buildClass (heights : Heights steps) : ClassTable steps :=
  Vector.ofFn fun start : Fin (steps+1) =>
    prefixRow (depthKey (boundedDepth heights)) start.val steps

def lookupClass (table : ClassTable steps) (start len : Fin (steps+1)) : Nat :=
  (ofLex ((table.get start).get len)).2

theorem lookupClass_build (heights : Heights steps) (start len : Fin (steps+1)) :
    lookupClass (buildClass heights) start len =
      argmin (boundedDepth heights) start.val len.val := by
  simp [lookupClass, buildClass, prefixRow_get, argmin]

def canonicalHeights (steps code : Nat) : Heights steps :=
  Vector.ofFn fun i => relative (decodeShape steps code) i.val

theorem canonicalHeights_read (steps code i : Nat) (hi : i ≤ steps) :
    boundedDepth (canonicalHeights steps code) i = relative (decodeShape steps code) i := by
  simp [boundedDepth, canonicalHeights, Nat.min_eq_left hi]

theorem rangeMin_congr_interval {α : Type} [LinearOrder α]
    (a b : Nat → α) (start len : Nat)
    (h : ∀ i, i ≤ len → a (start+i) = b (start+i)) :
    rangeMin a start len = rangeMin b start len := by
  induction len with
  | zero => simpa [rangeMin] using h 0 (by omega)
  | succ len ih =>
    rw [rangeMin, rangeMin, ih (fun i hi => h i (by omega))]
    congr 1
    simpa [Nat.add_assoc] using h (len+1) le_rfl

def prepareShared (steps : Nat) : SharedTable steps :=
  Vector.ofFn fun code => buildClass (canonicalHeights steps code.val)

def lookupShared (table : SharedTable steps) (code : Fin (2 ^ steps))
    (start len : Fin (steps+1)) : Nat := lookupClass (table.get code) start len

theorem lookupShared_correct (depth : Nat → Int) (h : UnitSteps steps depth)
    (start len : Fin (steps+1)) (hi : start.val + len.val ≤ steps) :
    lookupShared (prepareShared steps) (classAddress steps depth) start len =
      argmin depth start.val len.val := by
  simp only [lookupShared, prepareShared, vectorGet_ofFn]
  rw [lookupClass_build]
  have he : argmin (boundedDepth (canonicalHeights steps (classAddress steps depth).val))
      start.val len.val = classQuery steps (classAddress steps depth).val start.val len.val := by
    unfold argmin classQuery
    congr 2
    apply rangeMin_congr_interval
    intro i hil
    unfold depthKey
    rw [canonicalHeights_read steps (classAddress steps depth).val (start.val+i) (by omega)]
  rw [he]
  exact classQuery_correct depth h start.val len.val hi

example : lookupShared (prepareShared 2) 1 0 2 = 0 := by decide
example : lookupShared (prepareShared 2) 1 1 1 = 2 := by decide

end Sequences.LCA

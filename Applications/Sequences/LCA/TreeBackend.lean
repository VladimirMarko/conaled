import Applications.Sequences.LCA.Tree
import Applications.Dijkstra.Store
import Applications.Resources.Measured

set_option autoImplicit false
set_option warningAsError true

namespace Sequences.LCA.TreeBackend
open Resources Dijkstra.Store

/-- One target dispatch on entry to a recursive constructor/loop instruction,
    including its terminal case. Word operations remain separately charged. -/
def dispatch {α : Type} (run : Measured α Nat) : Measured α Nat :=
  Resources.bind (((),1) : Measured Unit Nat) fun _ => run

/-- The sentinel is an out-of-tour position. Reading an input, indexed reading,
    comparing, indexed writing, and incrementing each cost one primitive event. -/
def readWord (x : Nat) : Measured Nat Nat := (x, 1)
def compareWord (a b : Nat) : Measured Bool Nat := (decide (a = b), 1)
def checkIndex (a n : Nat) : Measured (Option (Fin n)) Nat :=
  (if h : a < n then some ⟨a,h⟩ else none, 1)
def increment (i : Nat) : Measured Nat Nat := (i + 1, 1)
def readSlot {n : Nat} (mem : Store n Nat) (i : Fin n) : Measured Nat Nat := (lookup mem i, 1)
def writeSlot {n : Nat} (mem : Store n Nat) (i : Fin n) (x : Nat) : Measured (Store n Nat) Nat :=
  (write mem i x, 1)

def firstScan {n : Nat} (missing : Nat) : List Nat → Nat → Store n Nat → Store n Nat
  | [], _, mem => mem
  | a :: rest, pos, mem =>
      let mem' := if h : a < n then
        if lookup mem ⟨a,h⟩ = missing then write mem ⟨a,h⟩ pos else mem
        else mem
      firstScan missing rest (pos + 1) mem'

def firstScanM {n : Nat} (missing : Nat) : List Nat → Nat → Store n Nat → Measured (Store n Nat) Nat
  | [], _, mem => dispatch (pure mem)
  | a :: rest, pos, mem =>
      dispatch <| bind (readWord a) fun a =>
      bind (checkIndex a n) fun valid =>
      let update : Measured (Store n Nat) Nat :=
        match valid with
        | some i =>
          bind (readSlot mem i) fun old =>
          bind (compareWord old missing) fun unset =>
          if unset then writeSlot mem i pos else pure mem
        | none => pure mem
      bind update fun mem' =>
      bind (increment pos) fun pos' =>
      firstScanM missing rest pos' mem'

/-- Search specification, independent of store updates and sentinel tests. -/
def findPosition (needle missing : Nat) : List Nat → Nat → Nat
  | [], _ => missing
  | a :: rest, pos => if a = needle then pos else findPosition needle missing rest (pos + 1)

theorem firstScan_lookup {n : Nat} (xs : List Nat) (missing pos : Nat) (mem : Store n Nat)
    (j : Fin n) (hbound : pos + xs.length ≤ missing) :
    lookup (firstScan missing xs pos mem) j =
      if lookup mem j = missing then findPosition j.val missing xs pos else lookup mem j := by
  induction xs generalizing pos mem with
  | nil => simp [firstScan, findPosition]
  | cons a rest ih =>
    simp only [firstScan]
    rw [ih _ _ (by simp only [List.length_cons] at hbound; omega)]
    by_cases ha : a < n
    · simp only [ha, ↓reduceDIte]
      by_cases he : a = j.val
      · have hij : (⟨a,ha⟩ : Fin n) = j := Fin.ext he
        simp only [hij]
        by_cases hm : lookup mem j = missing
        · simp [hm, lookup_write, findPosition, he, show pos ≠ missing by simp at hbound; omega]
        · simp [hm]
      · have hij : (⟨a,ha⟩ : Fin n) ≠ j := by intro h; exact he (congrArg Fin.val h)
        by_cases hm : lookup mem ⟨a,ha⟩ = missing
        · simp [hm, lookup_write, hij, findPosition, he]
        · simp [hm, findPosition, he]
    · have he : a ≠ j.val := by intro h; subst a; exact ha j.isLt
      simp [ha, findPosition, he]

theorem firstScanM_value {n : Nat} (xs : List Nat) (missing pos : Nat) (mem : Store n Nat) :
    (firstScanM missing xs pos mem).1 = firstScan missing xs pos mem := by
  induction xs generalizing pos mem with
  | nil => rfl
  | cons a rest ih =>
    by_cases ha : a < n
    · by_cases hm : lookup mem ⟨a,ha⟩ = missing <;>
        simp [firstScanM, dispatch, firstScan, readWord, checkIndex, ha, hm, Resources.bind,
          readSlot, compareWord, writeSlot, increment, Resources.pure, ih]
    · simp [firstScanM, dispatch, firstScan, readWord, checkIndex, ha, Resources.bind,
        increment, Resources.pure, ih]

theorem firstScanM_cost {n : Nat} (xs : List Nat) (missing pos : Nat) (mem : Store n Nat) :
    (firstScanM missing xs pos mem).2 ≤ 7 * xs.length + 1 := by
  induction xs generalizing pos mem with
  | nil => simp [firstScanM, dispatch, Resources.bind, Resources.pure]
  | cons a rest ih =>
    by_cases ha : a < n
    · by_cases hm : lookup mem ⟨a,ha⟩ = missing
      · have hb := ih (pos+1) (write mem ⟨a,ha⟩ pos)
        simp only [firstScanM, dispatch, readWord, checkIndex, ha, ↓reduceDIte, Resources.bind,
          readSlot, compareWord, hm, decide_true, ↓reduceIte, writeSlot, increment,
          List.length_cons]
        omega
      · have hb := ih (pos+1) mem
        simp only [firstScanM, dispatch, readWord, checkIndex, ha, ↓reduceDIte, Resources.bind,
          readSlot, compareWord, hm, decide_false, Bool.false_eq_true, ↓reduceIte, increment,
          Resources.pure, List.length_cons]
        omega
    · have hb := ih (pos+1) mem
      simp only [firstScanM, dispatch, readWord, checkIndex, ha, ↓reduceDIte, Resources.bind,
        increment, Resources.pure, List.length_cons]
      omega


theorem findPosition_least (xs : List Nat) (needle missing pos i : Nat)
    (hi : i < xs.length) (he : xs[i] = needle)
    (hbefore : ∀ j (hj : j < i), xs[j]'(Nat.lt_trans hj hi) ≠ needle) :
    findPosition needle missing xs pos = pos + i := by
  induction xs generalizing pos i with
  | nil => simp at hi
  | cons a rest ih =>
    cases i with
    | zero => simpa [findPosition] using (show (if a = needle then pos else findPosition needle missing rest (pos+1)) = pos by simp [show a = needle from he])
    | succ i =>
      have ha : a ≠ needle := hbefore 0 (by omega)
      simp only [findPosition, ha, ↓reduceIte]
      have hri : i < rest.length := by simpa using hi
      rw [ih (pos+1) i hri (by simpa using he) (by
        intro j hj
        simpa using hbefore (j+1) (by omega))]
      omega

def growSlot {n : Nat} (mem : Store n Nat) (x : Nat) : Measured (Store (n+1) Nat) Nat :=
  (mem.push x, 1)

/-- Initialize a reserved finite arena, one slot at a time. The logical vector
    grows only up to the reserved capacity; each growth initializes one cell. -/
def fillM (value : Nat) : (n : Nat) → Measured (Store n Nat) Nat
  | 0 => dispatch (pure #v[])
  | n+1 => dispatch <| bind (fillM value n) fun mem => growSlot mem value

theorem fillM_exact (value n : Nat) : fillM value n = (Vector.replicate n value, 2*n+1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fillM, dispatch, ih, growSlot, Resources.bind, Vector.replicate_succ]; omega

/-- The initialized first-position store is computed by the instrumented scan. -/
def prepareFirstM (t : Tree) (ids : List Nat) : Measured (Store t.size Nat) Nat :=
  bind (fillM t.tour.length t.size) fun initial => firstScanM t.tour.length ids 0 initial

/-- The code stream is read from the efficient emitter. Projection and proof
    erasure do not perform comparisons, dictionary lookups, or recomputation. -/
def emittedIds (t : Tree) : List Nat := ((Tree.cache t).emit 0 0 []).map Prod.fst

theorem emittedIds_eq (t : Tree) : emittedIds t = t.tour.map Tree.code := by
  simp [emittedIds, Tree.emit_spec, List.map_map, Function.comp_def]

theorem emittedIds_length (t : Tree) : (emittedIds t).length = t.tour.length := by
  simp [emittedIds_eq]

theorem findPosition_ids (t : Tree) (j : Fin t.size) :
    findPosition j.val t.tour.length (emittedIds t) 0 = Tree.first (t.decode j) := by
  let a := t.decode j
  have ha : Tree.code a = j.val := congrArg Fin.val (Tree.encode_decode t j)
  have hf := Tree.first_lt a
  rw [← Nat.zero_add (Tree.first a)]
  refine findPosition_least (emittedIds t) j.val t.tour.length 0 (Tree.first a)
    (by simpa [emittedIds_length] using hf) ?_ ?_
  · simp [emittedIds_eq, Tree.tour_getElem, ha]
  · intro k hk
    simp only [emittedIds_eq, List.getElem_map, Tree.tour_getElem]
    intro he
    have he' : Tree.encode (t.visit k) = Tree.encode a := Fin.ext (he.trans ha.symm)
    have hn : t.visit k = a := by
      have := congrArg (t.decode) he'
      simpa using this
    have := Tree.first_le_of_visit_eq a k hn
    omega

theorem prepareFirstM_lookup (t : Tree) (j : Fin t.size) :
    lookup (prepareFirstM t (emittedIds t)).1 j = Tree.first (t.decode j) := by
  simp only [prepareFirstM, Resources.bind, fillM_exact, firstScanM_value]
  rw [firstScan_lookup _ _ _ _ j (by simp [emittedIds_length])]
  simp only [lookup, Vector.getElem_replicate, ↓reduceIte]
  exact findPosition_ids t j

theorem prepareFirstM_cost (t : Tree) :
    (prepareFirstM t (emittedIds t)).2 ≤ 2*t.size + 7*t.tour.length + 2 := by
  simp only [prepareFirstM, Resources.bind, fillM_exact]
  have := firstScanM_cost (emittedIds t) t.tour.length 0 (Vector.replicate t.size t.tour.length)
  rw [emittedIds_length] at this
  omega

end Sequences.LCA.TreeBackend

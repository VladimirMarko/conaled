import Applications.Sequences.LCA.SharedTable
import Applications.Sequences.LCA.TableExecution

/-! Running minima written into a fixed-capacity initialized row. Every output
slot has a finite address; each entry after the first reads the previous entry. -/
namespace Sequences.LCA.MicroExecution
open Resources Dijkstra.Store TableExecution PreparedRMQ
variable {α : Type} [LinearOrder α]

def minimum (a b : α) : Measured α Nat := (min a b, 1)

def rowIndex {n : Nat} (i : Fin n) : Measured (Fin n) Nat := (i, 3)
def counter (i : Nat) : Measured Nat Nat := (i, 2)

def rowFill (seed : α) (source : Nat → Measured α Nat) (capacity : Nat) :
    (len : Nat) → len ≤ capacity → Measured (Store capacity α) Nat
  | 0, _ => initStore seed capacity
  | k+1, hk => bind (rowFill seed source capacity k (by omega)) fun mem =>
      bind (rowIndex (⟨k, by omega⟩ : Fin capacity)) fun slot =>
      bind (source slot.val) fun x =>
      if hz : slot.val = 0 then store mem slot x
      else bind (read mem ⟨slot.val-1, by have := slot.isLt; omega⟩) fun previous =>
        bind (minimum previous x) fun value => store mem slot value

theorem rowFill_lookup (seed : α) (source : Nat → Measured α Nat) (capacity len : Nat)
    (h : len ≤ capacity) (j : Fin capacity) (hj : j.val < len) :
    lookup (rowFill seed source capacity len h).1 j =
      rangeMin (fun i => (source i).1) 0 j.val := by
  induction len generalizing j with
  | zero => omega
  | succ k ih =>
    dsimp only [rowFill, rowIndex, Resources.bind, store, TableExecution.read, minimum]
    by_cases hz : k = 0
    · subst k
      have hjz : j.val = 0 := by omega
      have he : (⟨0, by omega⟩ : Fin capacity) = j := Fin.ext hjz.symm
      simp [he, lookup_write, rangeMin, hjz]
    · simp only [hz, dite_false]
      rw [lookup_write]
      by_cases hje : j.val = k
      · have he : (⟨k, by omega⟩ : Fin capacity) = j := Fin.ext hje.symm
        simp only [he, ite_true]
        rw [ih (by omega) ⟨k-1, by omega⟩ (by dsimp; omega)]
        rw [hje]
        have hk : k = (k-1)+1 := by omega
        conv_rhs => rw [hk, rangeMin]
        simp [Nat.sub_add_cancel (by omega : 1 ≤ k)]
      · have he : (⟨k, by omega⟩ : Fin capacity) ≠ j := by
          intro he
          exact hje (congrArg Fin.val he).symm
        rw [ite_eq_right he]
        exact ih (by omega) j (by omega)

theorem rowFill_cost (seed : α) (source : Nat → Measured α Nat) (capacity len : Nat)
    (h : len ≤ capacity) (c : Nat) (hc : ∀ i, (source i).2 ≤ c) :
    (rowFill seed source capacity len h).2 ≤ 3*capacity + len*(c+6) := by
  induction len with
  | zero => simp [rowFill, initStore_exact]
  | succ k ih =>
    dsimp only [rowFill, rowIndex, Resources.bind, store, TableExecution.read, minimum]
    have hp := ih (by omega)
    have hx := hc k
    split_ifs <;> nlinarith

def buildRow (seed : α) (source : Nat → Measured α Nat) (n : Nat) : Measured (Store n α) Nat :=
  rowFill seed source n n le_rfl

theorem buildRow_value (seed : α) (source : Nat → Measured α Nat) (n : Nat) :
    (buildRow seed source n).1 =
      Vector.ofFn (fun j : Fin n => rangeMin (fun i => (source i).1) 0 j.val) := by
  apply Vector.ext
  intro i hi
  have hh := rowFill_lookup seed source n n le_rfl ⟨i,hi⟩ hi
  simpa [buildRow, lookup] using hh

theorem buildRow_cost (seed : α) (source : Nat → Measured α Nat) (n c : Nat)
    (hc : ∀ i, (source i).2 ≤ c) : (buildRow seed source n).2 ≤ n*(c+9) := by
  have hh := rowFill_cost seed source n n le_rfl c hc
  dsimp only [buildRow]
  nlinarith

def addIndex (a b : Nat) : Measured Nat Nat := (a+b, 1)
def clampIndex (steps i : Nat) : Measured (Fin (steps+1)) Nat :=
  (⟨min i steps, by omega⟩, 1)
/-- Two scalar fields are assembled here; the packed-word interpretation has
one multiply and one add, whose fit obligations are separate. -/
def makeKey (depth : Int) (index : Nat) : Measured (Int ×ₗ Nat) Nat := (toLex (depth,index), 2)

def keySource (heights : Heights steps) (start i : Nat) : Measured (Int ×ₗ Nat) Nat :=
  bind (addIndex start i) fun j =>
  bind (clampIndex steps j) fun bounded =>
  bind (TableExecution.read heights bounded) fun depth => makeKey depth j

theorem keySource_exact (heights : Heights steps) (start i : Nat) :
    keySource heights start i = (depthKey (boundedDepth heights) (start+i), 5) := by
  simp [keySource, addIndex, clampIndex, TableExecution.read, lookup, makeKey,
    Resources.bind, depthKey, boundedDepth, Vector.get]

theorem rangeMin_translate (read : Nat → α) (start len : Nat) :
    rangeMin (fun i => read (start+i)) 0 len = rangeMin read start len := by
  induction len with
  | zero => simp [rangeMin]
  | succ len ih => simp [rangeMin, ih, Nat.add_assoc]

def buildClassM (heights : Heights steps) : Measured (ClassTable steps) Nat :=
  bind (keySource heights 0 0) fun seed =>
  bind (initStore seed (steps+1)) fun seedRow =>
  tabulate seedRow (fun start : Fin (steps+1) =>
    buildRow seed (keySource heights start.val) (steps+1))

theorem buildClassM_value (heights : Heights steps) :
    (buildClassM heights).1 = buildClass heights := by
  simp only [buildClassM, Resources.bind, tabulate_value, buildRow_value]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn]
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn, keySource_exact]
  simp only [buildClass, Vector.getElem_ofFn]
  change rangeMin (fun k => depthKey (boundedDepth heights) (i+k)) 0 j =
    ((prefixRow (depthKey (boundedDepth heights)) i steps).get ⟨j,hj⟩)
  rw [rangeMin_translate, prefixRow_get]

theorem buildClassM_cost (heights : Heights steps) :
    (buildClassM heights).2 ≤ 28 * (steps+1) * (steps+1) := by
  simp only [buildClassM, Resources.bind, keySource_exact, initStore_exact]
  have hh := tabulate_cost (Vector.replicate (steps+1)
      (depthKey (boundedDepth heights) 0))
    (fun start : Fin (steps+1) => buildRow (depthKey (boundedDepth heights) 0)
      (keySource heights start.val) (steps+1)) ((steps+1)*14)
    (fun start => buildRow_cost _ _ _ 5 (fun i => by rw [keySource_exact]))
  nlinarith

theorem decodeShape_bit (steps code : Nat) (i : Fin steps) :
    decodeShape steps code i = code.testBit i.val := by
  induction steps generalizing code with
  | zero => exact Fin.elim0 i
  | succ steps ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [decodeShape]
    · simpa [decodeShape, Nat.testBit_succ] using ih (code/2) j

/-- Shift and low-bit comparison are declared word primitives. The eligibility
proof must ensure that code and shift count fit the selected word width. -/
def shiftWord (code shift : Nat) : Measured Nat Nat := (code / 2 ^ shift, 1)
def lowBit (word : Nat) : Measured Bool Nat := (decide (word % 2 = 1), 1)
def stepHeight (height : Int) (up : Bool) : Measured Int Nat :=
  (height + if up then 1 else -1, 1)

def relativeCodeM (code : Nat) : Nat → Measured Int Nat
  | 0 => pure 0
  | i+1 => bind (relativeCodeM code i) fun height =>
      bind (counter i) fun j =>
      bind (shiftWord code j) fun shifted =>
      bind (lowBit shifted) fun up => stepHeight height up

theorem relativeCodeM_cost (code i : Nat) : (relativeCodeM code i).2 = 5*i := by
  induction i with
  | zero => rfl
  | succ i ih => simp [relativeCodeM, Resources.bind, shiftWord, lowBit, stepHeight, counter, ih]; omega

theorem relativeCodeM_value (steps code i : Nat) (hi : i ≤ steps) :
    (relativeCodeM code i).1 = relative (decodeShape steps code) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hib : i < steps := by omega
    simp only [relativeCodeM, Resources.bind, shiftWord, lowBit, stepHeight, counter,
      ih (by omega), relative, hib, dite_true, decodeShape_bit, Nat.testBit_eq_decide_div_mod_eq]
    rfl

def canonicalM (steps code : Nat) : Measured (Heights steps) Nat :=
  tabulate 0 (fun i : Fin (steps+1) => relativeCodeM code i.val)

theorem canonicalM_value (steps code : Nat) :
    (canonicalM steps code).1 = canonicalHeights steps code := by
  rw [canonicalM, tabulate_value]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn, canonicalHeights]
  exact relativeCodeM_value steps code i (by omega)

theorem canonicalM_cost (steps code : Nat) :
    (canonicalM steps code).2 ≤ 6*(steps+1)*(steps+1) := by
  have hh := tabulate_cost (n := steps+1) (0 : Int)
    (fun i : Fin (steps+1) => relativeCodeM code i.val) (5*steps)
    (fun i => by rw [relativeCodeM_cost]; have := i.isLt; omega)
  unfold canonicalM
  nlinarith

def sharedM (steps : Nat) : Measured (SharedTable steps) Nat :=
  bind (initStore (toLex ((0 : Int), (0 : Nat))) (steps+1)) fun seedRow =>
  bind (initStore seedRow (steps+1)) fun seedClass =>
  tabulate seedClass (fun code : Fin (2^steps) =>
    bind (canonicalM steps code.val) fun heights => buildClassM heights)

theorem sharedM_value (steps : Nat) : (sharedM steps).1 = prepareShared steps := by
  simp only [sharedM, Resources.bind, tabulate_value, canonicalM_value, buildClassM_value]
  rfl

theorem sharedM_cost (steps : Nat) :
    (sharedM steps).2 ≤ 64*(steps+1)*(steps+1)*2^steps := by
  have hc : ∀ code : Fin (2^steps),
      (bind (canonicalM steps code.val) (fun heights => buildClassM heights)).2 ≤
        34*(steps+1)*(steps+1) := by
    intro code
    simp only [Resources.bind]
    have ha := canonicalM_cost steps code.val
    have hb := buildClassM_cost (canonicalM steps code.val).1
    nlinarith
  simp only [sharedM, Resources.bind, initStore_exact]
  have hh := tabulate_cost
    (Vector.replicate (steps+1) (Vector.replicate (steps+1) (toLex ((0 : Int), (0 : Nat)))))
    (fun code : Fin (2^steps) => bind (canonicalM steps code.val) (fun heights => buildClassM heights))
    (34*(steps+1)*(steps+1)) hc
  simp only [Resources.bind] at hh
  have hp : 1 ≤ 2^steps := Nat.one_le_pow _ _ (by omega)
  have h₁ : 6*(steps+1) ≤ 6*(steps+1)*(steps+1)*2^steps := by
    have ha : 6*(steps+1) ≤ 6*(steps+1)*(steps+1) := by nlinarith
    have hb := Nat.mul_le_mul_left (6*(steps+1)*(steps+1)) hp
    nlinarith
  have h₂ : 6*2^steps ≤ 6*(steps+1)*(steps+1)*2^steps :=
    Nat.mul_le_mul_right _ (by nlinarith)
  nlinarith

def goesUp (a b : Int) : Measured Bool Nat := (decide (a < b), 1)
def doubleWord (n : Nat) : Measured Nat Nat := (2*n, 1)

def codeM (source : Nat → Measured Int Nat) (offset : Nat) : Nat → Measured Nat Nat
  | 0 => pure 0
  | k+1 => bind (counter offset) fun here =>
      bind (addIndex here 1) fun next =>
      bind (source here) fun a =>
      bind (source next) fun b =>
      bind (goesUp a b) fun up =>
      bind (codeM source next k) fun rest =>
      bind (doubleWord rest) fun doubled => addIndex (if up then 1 else 0) doubled

theorem codeM_value (source : Nat → Measured Int Nat) (offset steps : Nat) :
    (codeM source offset steps).1 =
      shapeCode (classify steps (fun i => (source (offset+i)).1)) := by
  induction steps generalizing offset with
  | zero => rfl
  | succ k ih =>
    simp only [codeM, counter, addIndex, goesUp, doubleWord, Resources.bind, ih,
      shapeCode, classify, Fin.val_zero, Nat.add_zero, Fin.val_succ]
    congr 2
    congr 1
    funext i
    simp [classify, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem codeM_cost (source : Nat → Measured Int Nat) (offset steps c : Nat)
    (hc : ∀ i, (source i).2 ≤ c) :
    (codeM source offset steps).2 ≤ steps*(2*c+6) := by
  induction steps generalizing offset with
  | zero => simp [codeM, Resources.pure]
  | succ k ih =>
    simp only [codeM, counter, addIndex, goesUp, doubleWord, Resources.bind]
    have hr := ih (offset+1)
    have ha := hc offset
    have hb := hc (offset+1)
    nlinarith

end Sequences.LCA.MicroExecution

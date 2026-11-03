import Applications.Linear.Structured
import Applications.Linear.StructuredCosts

/-! Instrumentation of the staged finite-vector machine. Vector allocation and
indexed reads/writes are abstract primitives; `outputWrite m` charges all slots
of a zero-initialized output. Index enumeration and coefficient staging are
charged separately from scatter. List transcripts are observations, not target
output allocations. Costs do not model Lean's persistent-array copying, bounds
proofs, garbage collection, or compiler optimizations. -/
namespace StructuredLinear
open Costs
variable {R : Type} [CommSemiring R] {m n : Nat}

def scatterCharge : Work :=
  tick .traversal + tick .index 2 + tick .coefficientRead + tick .inputRead +
  tick .outputRead + tick .scalarMul + tick .scalarAdd + tick .outputWrite

def stageCharge : Work :=
  tick .traversal + tick .index 2 + tick .coefficientRead + tick .construct

def initializeCharge (m : Nat) : Work := tick .outputWrite m + tick .traversal m

def sparseMeasured (a : Sparse R m n) (x : Vector R n) :
    Resources.Measured (Vector R m) Work :=
  Resources.bind (Vector.replicate m 0, initializeCharge m)
    (measuredFold (scatterStep x) (fun _ => scatterCharge) a)

@[simp] theorem sparseMeasured_erases (a : Sparse R m n) (x : Vector R n) :
    (sparseMeasured a x).1 = sparseApply a x := by
  simp [sparseMeasured, Resources.bind, sparseApply]

theorem sparseMeasured_cost (a : Sparse R m n) (x : Vector R n) (e : Event) :
    (sparseMeasured a x).2 e = initializeCharge m e + a.length * scatterCharge e := by
  simp only [sparseMeasured, Resources.bind, Pi.add_apply, fold_cost_uniform]

/-- Rows are traversed in order; each coefficient creates one coordinate entry.
Flattening copies the staged lists and is charged once per entry. -/
def denseStage (a : Dense R m n) : Resources.Measured (Sparse R m n) Work :=
  let rows := traverse (fun i : Fin m =>
    measuredMap (fun j : Fin n => (⟨i, j, a[i][j]⟩ : Entry R m n))
      (fun _ => stageCharge) (List.finRange n)) (List.finRange m)
  (rows.1.flatten, rows.2 + tick .traversal m + tick .construct (m * n))

def diagonalStage (a : Diagonal R n) : Resources.Measured (Sparse R n n) Work :=
  measuredMap (fun i : Fin n => (⟨i, i, a[i]⟩ : Entry R n n))
    (fun _ => stageCharge) (List.finRange n)

@[simp] theorem denseStage_erases (a : Dense R m n) :
    (denseStage a).1 = denseEntries a := by
  simp [denseStage, denseEntries, List.flatMap_def]

@[simp] theorem diagonalStage_erases (a : Diagonal R n) :
    (diagonalStage a).1 = diagonalEntries a := by
  simp [diagonalStage, diagonalEntries]

theorem diagonalStage_cost (a : Diagonal R n) (e : Event) :
    (diagonalStage a).2 e = n * stageCharge e := by
  simpa [diagonalStage] using map_cost_uniform
    (fun i : Fin n => (⟨i, i, a[i]⟩ : Entry R n n)) stageCharge (List.finRange n) e

theorem denseStage_cost (a : Dense R m n) (e : Event) :
    (denseStage a).2 e = m * n * stageCharge e +
      tick .traversal m e + tick .construct (m * n) e := by
  have h : ∀ i : Fin m,
      (measuredMap (fun j : Fin n => (⟨i, j, a[i][j]⟩ : Entry R m n))
        (fun _ => stageCharge) (List.finRange n)).2 = fun e => n * stageCharge e := by
    intro i
    funext e
    simpa using map_cost_uniform
      (fun j : Fin n => (⟨i, j, a[i][j]⟩ : Entry R m n)) stageCharge (List.finRange n) e
  have hc := traverse_cost_uniform _ _ h (List.finRange m) e
  simpa [denseStage, Nat.mul_assoc] using
    congrArg (fun k => k + tick .traversal m e + tick .construct (m * n) e) hc

def denseMeasured (a : Dense R m n) (x : Vector R n) :
    Resources.Measured (Vector R m) Work :=
  Resources.bind (denseStage a) (fun entries => sparseMeasured entries x)

def diagonalMeasured (a : Diagonal R n) (x : Vector R n) :
    Resources.Measured (Vector R n) Work :=
  Resources.bind (diagonalStage a) (fun entries => sparseMeasured entries x)

@[simp] theorem denseMeasured_erases (a : Dense R m n) (x : Vector R n) :
    (denseMeasured a x).1 = denseApply a x := by
  simp [denseMeasured, Resources.bind, denseApply]

@[simp] theorem diagonalMeasured_erases (a : Diagonal R n) (x : Vector R n) :
    (diagonalMeasured a x).1 = diagonalApply a x := by
  simp [diagonalMeasured, Resources.bind, diagonalApply]

theorem denseMeasured_cost (a : Dense R m n) (x : Vector R n) (e : Event) :
    (denseMeasured a x).2 e = m * n * stageCharge e +
      tick .traversal m e + tick .construct (m * n) e +
      (initializeCharge m e + m * n * scatterCharge e) := by
  simp only [denseMeasured, Resources.bind, Pi.add_apply, denseStage_cost,
    sparseMeasured_cost, denseStage_erases, denseEntries_length]

theorem diagonalMeasured_cost (a : Diagonal R n) (x : Vector R n) (e : Event) :
    (diagonalMeasured a x).2 e = n * stageCharge e +
      (initializeCharge n e + n * scatterCharge e) := by
  simp only [diagonalMeasured, Resources.bind, Pi.add_apply, diagonalStage_cost,
    sparseMeasured_cost, diagonalStage_erases, diagonalEntries_length]

/-- Scan every stored coefficient. Equality testing is a scan operation; only
retained entries allocate new cells. No zero test is needed by application. -/
def compactMeasured [DecidableEq R] : Sparse R m n → Resources.Measured (Sparse R m n) Work
  | [] => ([], 0)
  | a :: as =>
    let rest := compactMeasured as
    let inspection := tick .scan + tick .traversal + tick .coefficientRead
    if a.value = 0 then (rest.1, inspection + rest.2)
    else (a :: rest.1, inspection + tick .construct + rest.2)

@[simp] theorem compactMeasured_erases [DecidableEq R] (as : Sparse R m n) :
    (compactMeasured as).1 = as.filter (fun a => a.value ≠ 0) := by
  induction as with
  | nil => rfl
  | cons a as ih => by_cases h : a.value = 0 <;> simp [compactMeasured, h, ih]

theorem compactMeasured_cost [DecidableEq R] (as : Sparse R m n) (e : Event) :
    (compactMeasured as).2 e =
      as.length * (tick .scan + tick .traversal + tick .coefficientRead) e +
      (compactMeasured as).1.length * (tick .construct) e := by
  induction as with
  | nil => simp [compactMeasured]
  | cons a as ih =>
    by_cases h : a.value = 0 <;>
      simp [compactMeasured, h, Nat.add_mul, ih] <;> omega

/-- Conversion from dense includes staging and a full scan, including zeros. -/
def denseToSparseMeasured [DecidableEq R] (a : Dense R m n) :
    Resources.Measured (Sparse R m n) Work :=
  Resources.bind (denseStage a) compactMeasured

@[simp] theorem denseToSparseMeasured_erases [DecidableEq R] (a : Dense R m n) :
    (denseToSparseMeasured a).1 = denseToSparse a := by
  simp [denseToSparseMeasured, Resources.bind, denseToSparse, compact]

/-- Tabulation evaluates the measured cell operation at every finite index.
The value/counter pairs are instrumentation; erasure projects the value array. -/
def measuredTabulate {A : Type} (n : Nat) (f : Fin n → Resources.Measured A Work) :
    Resources.Measured (Vector A n) Work :=
  let cells := Vector.ofFn f
  (Vector.ofFn (fun i => cells[i].1), (cells.toList.map Prod.snd).sum)

@[simp] theorem measuredTabulate_erases {A : Type} (n : Nat)
    (f : Fin n → Resources.Measured A Work) :
    (measuredTabulate n f).1 = Vector.ofFn (fun i => (f i).1) := by
  apply Vector.ext
  intro i hi
  simp [measuredTabulate]

theorem measuredTabulate_cost {A : Type} (n : Nat)
    (f : Fin n → Resources.Measured A Work) (charge : Work)
    (h : ∀ i, (f i).2 = charge) (e : Event) :
    (measuredTabulate n f).2 e = n * charge e := by
  simp [measuredTabulate, Vector.toList_ofFn, List.map_ofFn, Function.comp_def, h,
    List.ofFn_const, List.sum_replicate, nsmul_eq_mul]

def materializeCellCharge : Work :=
  tick .scan + tick .index 2 + tick .construct + tick .traversal

/-- Every coordinate query is evaluated and charged by the nested tabulation. -/
def materializeMeasured (a : Matrix (Fin m) (Fin n) R) :
    Resources.Measured (Dense R m n) Work :=
  measuredTabulate m fun i =>
    Resources.bind ((), tick .traversal) fun _ =>
      measuredTabulate n fun j => (a i j, materializeCellCharge)

@[simp] theorem materializeMeasured_erases (a : Matrix (Fin m) (Fin n) R) :
    denseMatrix (materializeMeasured a).1 = a := by
  simp only [materializeMeasured, measuredTabulate_erases, Resources.bind]
  exact materialize_correct a

theorem materializeMeasured_cost (a : Matrix (Fin m) (Fin n) R) (e : Event) :
    (materializeMeasured a).2 e =
      m * ((tick .traversal) e + n * materializeCellCharge e) := by
  apply measuredTabulate_cost
  intro i
  funext e
  simp only [Resources.bind, Pi.add_apply]
  rw [measuredTabulate_cost n _ materializeCellCharge (fun _ => rfl)]

def denseScatterCharge : Work :=
  tick .traversal + tick .index 2 + tick .coefficientRead + tick .outputRead +
    tick .scalarAdd + tick .outputWrite

/-- Materialize a dense coefficient array by accumulating coordinate entries. -/
def sparseToDenseMeasured (a : Sparse R m n) : Resources.Measured (Dense R m n) Work :=
  Resources.bind (Vector.replicate m (Vector.replicate n 0), initializeCharge (m * n))
    (measuredFold scatterDenseStep (fun _ => denseScatterCharge) a)

@[simp] theorem sparseToDenseMeasured_erases (a : Sparse R m n) :
    (sparseToDenseMeasured a).1 = sparseToDense a := by
  simp [sparseToDenseMeasured, Resources.bind, sparseToDense]

theorem sparseToDenseMeasured_cost (a : Sparse R m n) (e : Event) :
    (sparseToDenseMeasured a).2 e =
      initializeCharge (m * n) e + a.length * denseScatterCharge e := by
  simp only [sparseToDenseMeasured, Resources.bind, Pi.add_apply, fold_cost_uniform]

/-- Storage uses scalar slots plus two index slots for each coordinate entry. -/
def sparseStorage (a : Sparse R m n) : Nat := 3 * a.length

def denseStorage (_a : Dense R m n) : Nat := m * n

def diagonalStorage (_a : Diagonal R n) : Nat := n

/-- Conservative live-slot allowance: source, staged entries, compact destination.
This intentionally allows all three to remain live during conversion. -/
def denseToSparseLive [DecidableEq R] (a : Dense R m n) : Nat :=
  max (denseStorage a + 6 * (denseEntries a).length)
    (denseStorage a + 3 * (denseEntries a).length +
      sparseStorage (denseToSparseMeasured a).1)

end StructuredLinear

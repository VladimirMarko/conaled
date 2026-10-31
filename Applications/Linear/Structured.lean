import Applications.Linear.Matrix
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-! Exact finite coordinates with concrete array-backed dense and diagonal storage,
and coordinate entries with additive duplicate semantics. All execution uses
finite vectors; coordinate functions occur only at the observation boundary. -/
namespace StructuredLinear

variable {R : Type} [CommSemiring R] {m n p : Nat}

abbrev Dense (R : Type) (m n : Nat) := Vector (Vector R n) m
abbrev Diagonal (R : Type) (n : Nat) := Vector R n

structure Entry (R : Type) (m n : Nat) where
  row : Fin m
  col : Fin n
  value : R
  deriving DecidableEq

abbrev Sparse (R : Type) (m n : Nat) := List (Entry R m n)

def observe (x : Vector R n) : Fin n → R := fun i => x[i]
def denseMatrix (a : Dense R m n) : Matrix (Fin m) (Fin n) R := fun i j => a[i][j]
def diagonalMatrix (a : Diagonal R n) : Matrix (Fin n) (Fin n) R :=
  Matrix.diagonal (observe a)
def entryMatrix (a : Entry R m n) : Matrix (Fin m) (Fin n) R :=
  fun i j => if i = a.row ∧ j = a.col then a.value else 0

def sparseMatrix : Sparse R m n → Matrix (Fin m) (Fin n) R
  | [] => 0
  | e :: es => entryMatrix e + sparseMatrix es

/-- Each list entry performs one random-access accumulator update. -/
def scatterStep (x : Vector R n) (y : Vector R m) (e : Entry R m n) : Vector R m :=
  y.set e.row.val (y[e.row] + e.value * x[e.col])

def sparseApply (a : Sparse R m n) (x : Vector R n) : Vector R m :=
  a.foldl (scatterStep x) (Vector.replicate m 0)

theorem entry_action (e : Entry R m n) (x : Vector R n) (i : Fin m) :
    (entryMatrix e).mulVec (observe x) i = if i = e.row then e.value * x[e.col] else 0 := by
  by_cases h : i = e.row <;> simp [Matrix.mulVec, dotProduct, entryMatrix, h, observe]

theorem scatterStep_observe (x : Vector R n) (y : Vector R m) (e : Entry R m n) :
    observe (scatterStep x y e) = observe y + (entryMatrix e).mulVec (observe x) := by
  funext i
  rw [Pi.add_apply, entry_action]
  change (y.set e.row.val (y[e.row] + e.value * x[e.col]))[i.val] =
    y[i.val] + if i = e.row then e.value * x[e.col] else 0
  rw [Vector.getElem_set]
  by_cases h : i = e.row
  · subst i; simp
  · have h' : e.row.val ≠ i.val := fun he => h (Fin.ext he.symm)
    simp [h, h']

theorem scatter_fold (es : Sparse R m n) (x : Vector R n) (y : Vector R m) :
    observe (es.foldl (scatterStep x) y) = observe y + (sparseMatrix es).mulVec (observe x) := by
  induction es generalizing y with
  | nil => simp [sparseMatrix]
  | cons e es ih =>
    simp only [List.foldl_cons, ih, scatterStep_observe, sparseMatrix, Matrix.add_mulVec]
    exact add_assoc _ _ _

theorem sparseApply_correct (a : Sparse R m n) (x : Vector R n) :
    observe (sparseApply a x) = (sparseMatrix a).mulVec (observe x) := by
  have hz : observe (Vector.replicate m (0 : R)) = 0 := by funext i; simp [observe]
  simpa [sparseApply, hz] using scatter_fold a x (Vector.replicate m 0)

/-- Dense staging enumerates every coordinate, including zero coefficients. -/
def denseEntries (a : Dense R m n) : Sparse R m n :=
  (List.finRange m).flatMap fun i => (List.finRange n).map fun j => ⟨i, j, a[i][j]⟩

def diagonalEntries (a : Diagonal R n) : Sparse R n n :=
  (List.finRange n).map fun i => ⟨i, i, a[i]⟩

def denseApply (a : Dense R m n) (x : Vector R n) : Vector R m :=
  sparseApply (denseEntries a) x

def diagonalApply (a : Diagonal R n) (x : Vector R n) : Vector R n :=
  sparseApply (diagonalEntries a) x

theorem sparseMatrix_eq_sum (a : Sparse R m n) (i : Fin m) (j : Fin n) :
    sparseMatrix a i j = (a.map (fun e => entryMatrix e i j)).sum := by
  induction a with
  | nil => rfl
  | cons e es ih => simp [sparseMatrix, ih]

omit [CommSemiring R] in
@[simp] theorem denseEntries_length (a : Dense R m n) : (denseEntries a).length = m * n := by
  simp [denseEntries]

omit [CommSemiring R] in
@[simp] theorem diagonalEntries_length (a : Diagonal R n) :
    (diagonalEntries a).length = n := by simp [diagonalEntries]

@[simp] theorem denseEntries_correct (a : Dense R m n) :
    sparseMatrix (denseEntries a) = denseMatrix a := by
  funext i j
  simp [sparseMatrix_eq_sum, denseEntries, List.flatMap_def, List.sum_flatten,
    List.finRange, List.map_ofFn, List.sum_ofFn, entryMatrix, denseMatrix, Function.comp_def, ite_and]

@[simp] theorem diagonalEntries_correct (a : Diagonal R n) :
    sparseMatrix (diagonalEntries a) = diagonalMatrix a := by
  funext i j
  simp [sparseMatrix_eq_sum, diagonalEntries, List.finRange, List.map_ofFn,
    List.sum_ofFn, entryMatrix, diagonalMatrix, Matrix.diagonal, observe, Function.comp_def, ite_and, eq_comm]

theorem denseApply_correct (a : Dense R m n) (x : Vector R n) :
    observe (denseApply a x) = (denseMatrix a).mulVec (observe x) := by
  simpa [denseApply] using sparseApply_correct (denseEntries a) x

theorem diagonalApply_correct (a : Diagonal R n) (x : Vector R n) :
    observe (diagonalApply a x) = (diagonalMatrix a).mulVec (observe x) := by
  simpa [diagonalApply] using sparseApply_correct (diagonalEntries a) x

/-- The client needs only application and its coordinate observation law. -/
structure Realization (R : Type) [CommSemiring R] (m n : Nat) where
  Storage : Type
  matrix : Storage → Matrix (Fin m) (Fin n) R
  apply : Storage → Vector R n → Vector R m
  correct : ∀ a x, observe (apply a x) = (matrix a).mulVec (observe x)

@[reducible] def sparseRealization : Realization R m n :=
  ⟨Sparse R m n, sparseMatrix, sparseApply, sparseApply_correct⟩
@[reducible] def denseRealization : Realization R m n :=
  ⟨Dense R m n, denseMatrix, denseApply, denseApply_correct⟩
@[reducible] def diagonalRealization : Realization R n n :=
  ⟨Diagonal R n, diagonalMatrix, diagonalApply, diagonalApply_correct⟩

@[reducible] def vectorRep (R : Type) (n : Nat) : Squares.Rep :=
  ⟨Vector R n, Fin n → R, fun x i => x[i]⟩

@[reducible] def Realization.representation (r : Realization R m n) : Squares.Rep :=
  ⟨r.Storage, (Fin n → R) →ₗ[R] (Fin m → R), fun a => Matrix.toLin' (r.matrix a)⟩

def Realization.applicationSquare (r : Realization R m n) :
    Squares.Square (Squares.product r.representation (vectorRep R n)) (vectorRep R m) where
  impl q := r.apply q.1 q.2
  spec q := q.1 q.2
  commutes q := r.correct q.1 q.2

/-- A batch reuses one immutable realization; the client proof is representation-independent. -/
def Realization.batch (r : Realization R m n) (a : r.Storage) (xs : List (Vector R n)) :=
  xs.map (r.apply a)

theorem Realization.batch_correct (r : Realization R m n) (a : r.Storage)
    (xs : List (Vector R n)) :
    (r.batch a xs).map observe = xs.map (fun x => (r.matrix a).mulVec (observe x)) := by
  simp only [Realization.batch, List.map_map]
  congr 1
  funext x
  exact r.correct a x

/-- Repeated endomorphism application, including zero iterations. -/
def Realization.repeat (r : Realization R n n) (a : r.Storage) : Nat → Vector R n → Vector R n
  | 0, x => x
  | k + 1, x => r.apply a (r.repeat a k x)

theorem Realization.repeat_correct (r : Realization R n n) (a : r.Storage)
    (k : Nat) (x : Vector R n) :
    observe (r.repeat a k x) = (r.matrix a ^ k).mulVec (observe x) := by
  induction k with
  | zero => simp [Realization.repeat]
  | succ k ih =>
    rw [Realization.repeat, r.correct, ih, Matrix.mulVec_mulVec, pow_succ']

/-- Different storage formats compose without a shared universal operation class. -/
theorem Realization.twoStage_correct (first : Realization R m n) (second : Realization R p m)
    (a : first.Storage) (b : second.Storage) (x : Vector R n) :
    observe (second.apply b (first.apply a x)) =
      (second.matrix b * first.matrix a).mulVec (observe x) := by
  rw [second.correct, first.correct, Matrix.mulVec_mulVec]

/-- Dense conversion materializes the independently specified coordinates. -/
def materialize (a : Matrix (Fin m) (Fin n) R) : Dense R m n :=
  Vector.ofFn fun i => Vector.ofFn fun j => a i j

omit [CommSemiring R] in
@[simp] theorem materialize_correct (a : Matrix (Fin m) (Fin n) R) :
    denseMatrix (materialize a) = a := by funext i j; simp [denseMatrix, materialize]

/-- Zero elimination is optional and is the only adapter needing decidable scalar equality. -/
def compact [DecidableEq R] (a : Sparse R m n) : Sparse R m n :=
  a.filter fun e => e.value ≠ 0

@[simp] theorem compact_correct [DecidableEq R] (a : Sparse R m n) :
    sparseMatrix (compact a) = sparseMatrix a := by
  induction a with
  | nil => rfl
  | cons e es ih =>
    by_cases h : e.value = 0
    · have he : entryMatrix e = 0 := by funext i j; simp [entryMatrix, h]
      simp [compact, h, sparseMatrix, he, ← ih]
    · simp [compact, h, sparseMatrix, ← ih]

def denseToSparse [DecidableEq R] (a : Dense R m n) : Sparse R m n := compact (denseEntries a)

@[simp] theorem denseToSparse_correct [DecidableEq R] (a : Dense R m n) :
    sparseMatrix (denseToSparse a) = denseMatrix a := by simp [denseToSparse]

/-- Scalar/index raw input is validated once; all subsequent entries have bounded indices. -/
def validateEntry (a : Nat × Nat × R) : Option (Entry R m n) :=
  if hi : a.1 < m then
    if hj : a.2.1 < n then some ⟨⟨a.1, hi⟩, ⟨a.2.1, hj⟩, a.2.2⟩ else none
  else none

/-- Diagonal composition remains diagonal in the same chosen coordinates. -/
def diagonalCompose (b a : Diagonal R n) : Diagonal R n :=
  Vector.ofFn fun i => b[i] * a[i]

theorem diagonalCompose_correct (b a : Diagonal R n) :
    diagonalMatrix (diagonalCompose b a) = diagonalMatrix b * diagonalMatrix a := by
  rw [diagonalMatrix, diagonalMatrix, diagonalMatrix, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  simp [observe, diagonalCompose]

def diagonalAdd (a b : Diagonal R n) : Diagonal R n := Vector.ofFn fun i => a[i] + b[i]

theorem diagonalAdd_correct (a b : Diagonal R n) :
    diagonalMatrix (diagonalAdd a b) = diagonalMatrix a + diagonalMatrix b := by
  rw [diagonalMatrix, diagonalMatrix, diagonalMatrix, Matrix.diagonal_add]
  congr 1
  funext i
  simp [observe, diagonalAdd]

/-- Mixed composition returns a general dense realization. This is a semantic
materialization operation, not a measured sparse matrix-multiplication kernel. -/
def composeDense (first : Realization R m n) (second : Realization R p m)
    (a : first.Storage) (b : second.Storage) : Dense R p n :=
  materialize (second.matrix b * first.matrix a)

theorem composeDense_correct (first : Realization R m n) (second : Realization R p m)
    (a : first.Storage) (b : second.Storage) (x : Vector R n) :
    observe (denseApply (composeDense first second a b) x) =
      observe (second.apply b (first.apply a x)) := by
  rw [denseApply_correct, composeDense, materialize_correct, Realization.twoStage_correct]

/-- Accumulate one coordinate into a dense destination, preserving duplicates. -/
def scatterDenseStep (y : Dense R m n) (e : Entry R m n) : Dense R m n :=
  y.set e.row.val ((y[e.row]).set e.col.val (y[e.row][e.col] + e.value))

def sparseToDense (a : Sparse R m n) : Dense R m n :=
  a.foldl scatterDenseStep (Vector.replicate m (Vector.replicate n 0))

theorem scatterDenseStep_observe (y : Dense R m n) (e : Entry R m n) :
    denseMatrix (scatterDenseStep y e) = denseMatrix y + entryMatrix e := by
  funext i j
  change (y.set e.row.val ((y[e.row]).set e.col.val (y[e.row][e.col] + e.value)))[i.val][j.val] =
    y[i.val][j.val] + if i = e.row ∧ j = e.col then e.value else 0
  rw [Vector.getElem_set]
  by_cases hi : e.row.val = i.val
  · have hi' : i = e.row := Fin.ext hi.symm
    subst i
    simp only [ite_true]
    rw [Vector.getElem_set]
    by_cases hj : e.col.val = j.val
    · have hj' : j = e.col := Fin.ext hj.symm
      subst j
      simp
    · have hj' : j ≠ e.col := fun h => hj (congrArg Fin.val h.symm)
      simp [hj, hj']
  · have hi' : i ≠ e.row := fun h => hi (congrArg Fin.val h.symm)
    simp [hi, hi']

theorem sparseToDense_fold (a : Sparse R m n) (y : Dense R m n) :
    denseMatrix (a.foldl scatterDenseStep y) = denseMatrix y + sparseMatrix a := by
  induction a generalizing y with
  | nil => simp [sparseMatrix]
  | cons e es ih =>
    simp only [List.foldl_cons, ih, scatterDenseStep_observe, sparseMatrix]
    exact add_assoc _ _ _

@[simp] theorem sparseToDense_correct (a : Sparse R m n) :
    denseMatrix (sparseToDense a) = sparseMatrix a := by
  have hz : denseMatrix (Vector.replicate m (Vector.replicate n (0 : R))) = 0 := by
    funext i j; simp [denseMatrix]
  simpa [sparseToDense, hz] using
    sparseToDense_fold a (Vector.replicate m (Vector.replicate n 0))

end StructuredLinear

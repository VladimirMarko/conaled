import Applications.Linear.Structured

/-! Public clients instantiated at dense, diagonal and coordinate-entry storage.
The independently calculated diagonal action is (2*4, 3*5) = (8,15).
The second stage swaps coordinates, distinguishing composition order. -/
namespace StructuredLinear.Examples
open StructuredLinear

def diagonal : Diagonal ℤ 2 := #v[2, 3]
def dense : Dense ℤ 2 2 := #v[#v[2, 0], #v[0, 3]]
def sparse : Sparse ℤ 2 2 := [⟨0, 0, 2⟩, ⟨1, 1, 3⟩]
def input : Vector ℤ 2 := #v[4, 5]
def swap : Dense ℤ 2 2 := #v[#v[0, 1], #v[1, 0]]

theorem dense_matches_diagonal : denseMatrix dense = diagonalMatrix diagonal := by
  funext i j; fin_cases i <;> fin_cases j <;> decide

theorem sparse_matches_diagonal : sparseMatrix sparse = diagonalMatrix diagonal := by
  funext i j; fin_cases i <;> fin_cases j <;> decide

theorem diagonal_result : observe (diagonalRealization.apply diagonal input) = ![8, 15] := by
  rw [diagonalRealization.correct]
  funext i; fin_cases i <;> norm_num [diagonalRealization, diagonalMatrix, observe,
    diagonal, input, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem dense_result : observe (denseRealization.apply dense input) = ![8, 15] := by
  rw [denseRealization.correct]
  change (denseMatrix dense).mulVec (observe input) = _
  rw [dense_matches_diagonal]
  exact diagonalApply_correct diagonal input ▸ diagonal_result

theorem sparse_result : observe (sparseRealization.apply sparse input) = ![8, 15] := by
  rw [sparseRealization.correct]
  change (sparseMatrix sparse).mulVec (observe input) = _
  rw [sparse_matches_diagonal]
  exact diagonalApply_correct diagonal input ▸ diagonal_result

/-- One shared batch proof for each realization, with exact equality of public observations. -/
theorem batch_agreement (xs : List (Vector ℤ 2)) :
    (denseRealization.batch dense xs).map observe =
      (sparseRealization.batch sparse xs).map observe ∧
    (sparseRealization.batch sparse xs).map observe =
      (diagonalRealization.batch diagonal xs).map observe := by
  simp only [Realization.batch_correct]
  change xs.map (fun x => (denseMatrix dense).mulVec (observe x)) =
      xs.map (fun x => (sparseMatrix sparse).mulVec (observe x)) ∧ _
  simp [dense_matches_diagonal, sparse_matches_diagonal]

/-- Repeated application gives (2²*4,3²*5), not merely repeated independent inputs. -/
theorem repeated_result : observe (diagonalRealization.repeat diagonal 2 input) = ![16, 45] := by
  rw [Realization.repeat_correct]
  funext i; fin_cases i <;>
    norm_num [diagonalRealization, diagonalMatrix, observe, diagonal, input, pow_two,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem composed_result :
    observe (denseRealization.apply swap (sparseRealization.apply sparse input)) = ![15, 8] := by
  rw [Realization.twoStage_correct]
  funext i; fin_cases i <;>
    norm_num [denseRealization, sparseRealization, denseMatrix, sparseMatrix, entryMatrix,
      swap, sparse, input, observe, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- No stored entries and explicit stored zero have identical meaning. -/
theorem explicit_zero : sparseMatrix ([⟨0, 0, 0⟩] : Sparse ℤ 1 1) = sparseMatrix [] := by
  funext i j; simp [sparseMatrix, entryMatrix]

/-- Duplicate coordinates can cancel; decoder injectivity is neither assumed nor true. -/
theorem duplicate_cancellation :
    sparseMatrix ([⟨0, 0, 7⟩, ⟨0, 0, -7⟩] : Sparse ℤ 1 1) = 0 := by
  funext i j; fin_cases i; fin_cases j; decide

theorem cancellation_application (x : Vector ℤ 1) :
    observe (sparseApply ([⟨0, 0, 7⟩, ⟨0, 0, -7⟩] : Sparse ℤ 1 1) x) = 0 := by
  rw [sparseApply_correct, duplicate_cancellation, Matrix.zero_mulVec]

/-- Empty input shape still materializes two zero output coordinates. -/
theorem empty_input :
    observe (denseApply (#v[#v[], #v[]] : Dense ℤ 2 0) #v[]) = 0 := by
  rw [denseApply_correct]
  funext i; simp [Matrix.mulVec, dotProduct]

/-- Empty output shape has no observable coordinates. -/
theorem empty_output (x : Vector ℤ 2) :
    observe (denseApply (#v[] : Dense ℤ 0 2) x) = 0 := by
  funext i; exact Fin.elim0 i

theorem invalid_row : validateEntry (m := 2) (n := 2) (2, 0, (7 : ℤ)) = none := by decide
theorem invalid_col : validateEntry (m := 2) (n := 2) (0, 2, (7 : ℤ)) = none := by decide
theorem valid_raw : validateEntry (m := 2) (n := 2) (1, 0, (7 : ℤ)) =
    some ⟨1, 0, 7⟩ := by decide

/-- Optional zero elimination preserves an application, including input-dependent zeros. -/
theorem converted_dense (x : Vector ℤ 2) :
    observe (sparseApply (denseToSparse dense) x) = observe (denseApply dense x) := by
  rw [sparseApply_correct, denseToSparse_correct, denseApply_correct]

theorem dense_materialization (a : Sparse ℤ 2 2) (x : Vector ℤ 2) :
    observe (denseApply (materialize (sparseMatrix a)) x) = observe (sparseApply a x) := by
  rw [denseApply_correct, materialize_correct, sparseApply_correct]

example : diagonalCompose diagonal diagonal = (#v[4, 9] : Diagonal ℤ 2) := by decide
example : diagonalAdd diagonal diagonal = (#v[4, 6] : Diagonal ℤ 2) := by decide

example : diagonalMatrix (diagonalCompose diagonal diagonal) =
    diagonalMatrix diagonal * diagonalMatrix diagonal := diagonalCompose_correct _ _

example : diagonalMatrix (diagonalAdd diagonal diagonal) =
    diagonalMatrix diagonal + diagonalMatrix diagonal := diagonalAdd_correct _ _

example : observe (denseApply (composeDense sparseRealization denseRealization sparse swap) input) =
    ![15, 8] := by rw [composeDense_correct]; exact composed_result

/-- Executed COO-to-dense conversion agrees even when duplicates cancel. -/
example : denseMatrix (sparseToDense ([⟨0, 0, 7⟩, ⟨0, 0, -7⟩] : Sparse ℤ 1 1)) = 0 := by
  rw [sparseToDense_correct, duplicate_cancellation]

example (a : Sparse ℤ 2 2) (x : Vector ℤ 2) :
    observe (denseApply (sparseToDense a) x) = observe (sparseApply a x) := by
  rw [denseApply_correct, sparseToDense_correct, sparseApply_correct]

end StructuredLinear.Examples

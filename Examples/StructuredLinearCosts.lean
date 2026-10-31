import Applications.Linear.StructuredMeasured

/-! A fixed exact diagonal map, admitted dense and coordinate implementations,
and a target without a diagonal kernel. All work profiles below come from
measured constructors and applications. The examples compare this finite family;
they make no global optimality or physical running-time claim. -/
namespace StructuredLinearCostExamples
open StructuredLinear StructuredLinear.Costs

def coefficients : Diagonal Nat 2 := ⟨#[1, 2], rfl⟩
def input : Vector Nat 2 := ⟨#[3, 4], rfl⟩
def matrix : Matrix (Fin 2) (Fin 2) Nat := diagonalMatrix coefficients

def prepareDense := materializeMeasured matrix
def prepareSparse := Resources.bind prepareDense denseToSparseMeasured

def runDense (n : Nat) := workload prepareDense denseMeasured (List.replicate n input)
def runSparse (n : Nat) := workload prepareSparse sparseMeasured (List.replicate n input)

def uniform : Work := fun _ => 1
def expensiveScan : Work := fun e => if e = .scan then 10 else 1

/-- Three candidates denote the same map; target support excludes the third. -/
inductive Candidate where | dense | sparse | diagonal
  deriving DecidableEq

def plan : Candidate → Plan
  | .dense => ⟨.dense, prepareDense.2,
      (denseMeasured prepareDense.1 input).2, denseStorage prepareDense.1, 6 * denseStorage prepareDense.1 + 2 + 2⟩
  | .sparse => ⟨.coordinate, prepareSparse.2,
      (sparseMeasured prepareSparse.1 input).2, sparseStorage prepareSparse.1, denseToSparseLive prepareDense.1 + 2 + 2⟩
  | .diagonal => ⟨.diagonal, tick .construct 2,
      (diagonalMeasured coefficients input).2, diagonalStorage coefficients, 3 * diagonalStorage coefficients + 2 + 2⟩

def target : Target := ⟨(fun f => f ≠ .diagonal), True, 100⟩
@[reducible] def admitted : Set Candidate := fun c => eligible target (plan c)
def cost (prices : Work) (n : Nat) (c : Candidate) := objective prices n (plan c)

theorem diagonal_unavailable : ¬ admitted .diagonal := by
  unfold admitted eligible target plan
  decide
theorem accepted : admitted .dense ∧ admitted .sparse := by
  unfold admitted eligible target plan
  decide

/-- The sparse result retains only two coefficients, but includes their indices. -/
example : prepareSparse.1.length = 2 ∧ (plan .sparse).retained = 6 ∧
    (plan .dense).retained = 4 ∧ denseToSparseLive prepareDense.1 = 28 := by decide

/-- Conversion inspects all four coordinates, including the two zeros. -/
example : (denseToSparseMeasured prepareDense.1).2 .scan = 4 := by decide

/-- Independent expected output: (3,4) maps to (3,8). -/
example : (runDense 2).1 = [⟨#[3, 8], rfl⟩, ⟨#[3, 8], rfl⟩] ∧
    (runSparse 2).1 = (runDense 2).1 := by decide

/-- The objective includes constructor and conversion work, and matches execution. -/
example : tariff expensiveScan (runDense 1).2 = cost expensiveScan 1 .dense ∧
    tariff expensiveScan (runSparse 10).2 = cost expensiveScan 10 .sparse := by decide

theorem dense_objective_is_execution (prices : Work) (n : Nat) :
    tariff prices (runDense n).2 = cost prices n .dense := by
  unfold runDense cost objective plan
  congr 1
  funext e
  exact workload_repeat_cost prepareDense denseMeasured input n e

theorem sparse_objective_is_execution (prices : Work) (n : Nat) :
    tariff prices (runSparse n).2 = cost prices n .sparse := by
  unfold runSparse cost objective plan
  congr 1
  funext e
  exact workload_repeat_cost prepareSparse sparseMeasured input n e

/-- One application cannot repay conversion under the expensive scan tariff. -/
example : cost expensiveScan 1 .dense < cost expensiveScan 1 .sparse := by decide

/-- Reuse repays conversion; changing the tariff also reverses the single-use choice. -/
example : cost expensiveScan 10 .sparse < cost expensiveScan 10 .dense ∧
    cost uniform 1 .sparse < cost uniform 1 .dense := by decide

theorem repeated_sparse_minimizes :
    Candidate.sparse ∈ Optimization.minimizers admitted (cost expensiveScan 10) := by
  refine ⟨accepted.2, ?_⟩
  intro c hc
  change cost expensiveScan 10 .sparse ≤ cost expensiveScan 10 c
  cases c with
  | dense => decide
  | sparse => exact le_rfl
  | diagonal => exact False.elim (diagonal_unavailable hc)

/-- Transport is restricted to the image of the admitted family of realizations. -/
example : plan .sparse ∈ Optimization.minimizers (plan '' admitted)
    (objective expensiveScan 10) :=
  transport_choice admitted plan (cost expensiveScan 10) expensiveScan 10 id
    monotone_id (fun _ _ => rfl) repeated_sparse_minimizes

/-- Time and retained storage form a partial order. Neither representation
improves both coordinates, so a least-time result is not a unique Pareto choice. -/
def tradeoff (c : Candidate) : Nat × Nat := (cost expensiveScan 10 c, (plan c).retained)

theorem dense_pareto : Candidate.dense ∈ Optimization.pareto admitted tradeoff := by
  refine ⟨accepted.1, ?_⟩
  intro c hc hle
  cases c with
  | dense => exact le_rfl
  | sparse =>
    have h : (plan .dense).retained < (plan .sparse).retained := by decide
    exact False.elim (Nat.not_le_of_gt h hle.2)
  | diagonal => exact False.elim (diagonal_unavailable hc)

theorem sparse_pareto : Candidate.sparse ∈ Optimization.pareto admitted tradeoff := by
  refine ⟨accepted.2, ?_⟩
  intro c hc hle
  cases c with
  | sparse => exact le_rfl
  | dense =>
    have h : cost expensiveScan 10 .sparse < cost expensiveScan 10 .dense := by decide
    exact False.elim (Nat.not_le_of_gt h hle.1)
  | diagonal => exact False.elim (diagonal_unavailable hc)

/-- The candidate family shares the same independent coordinate semantics. -/
theorem prepared_agreement : denseMatrix prepareDense.1 = matrix ∧
    sparseMatrix prepareSparse.1 = matrix ∧ diagonalMatrix coefficients = matrix := by
  refine ⟨materializeMeasured_erases matrix, ?_, rfl⟩
  change sparseMatrix (denseToSparseMeasured prepareDense.1).1 = matrix
  rw [denseToSparseMeasured_erases, denseToSparse_correct]
  exact materializeMeasured_erases matrix

/-- Common application correctness is inherited through measured erasure. -/
example (x : Vector Nat 2) :
    observe (denseMeasured prepareDense.1 x).1 = matrix.mulVec (observe x) ∧
    observe (sparseMeasured prepareSparse.1 x).1 = matrix.mulVec (observe x) := by
  simp only [denseMeasured_erases, sparseMeasured_erases, denseApply_correct,
    sparseApply_correct, prepared_agreement.1, prepared_agreement.2.1, and_self]

/-- Two measured stages compose through the existing matrix application laws. -/
example (a : Sparse Nat 2 2) (b : Dense Nat 2 2) (x : Vector Nat 2) :
    observe (Resources.bind (sparseMeasured a x) (denseMeasured b)).1 =
      (denseMatrix b * sparseMatrix a).mulVec (observe x) := by
  simp only [Resources.bind, denseMeasured_erases, sparseMeasured_erases,
    denseApply_correct, sparseApply_correct, Matrix.mulVec_mulVec]

/-- A producer applies the map once and retains its matrix for a later consumer. -/
def denseProducer := Resources.bind prepareDense fun a =>
  Resources.bind (denseMeasured a input) fun y => ((a, y), (0 : Work))

def sparseProducer := Resources.bind prepareSparse fun a =>
  Resources.bind (sparseMeasured a input) fun y => ((a, y), (0 : Work))

/-- The downstream operation accepts dense coefficient storage. -/
def denseConsumer (p : Dense Nat 2 2 × Vector Nat 2) := denseMeasured p.1 p.2

def densePipeline := Resources.bind denseProducer denseConsumer

def sparsePipeline := Resources.bind sparseProducer fun p =>
  Resources.bind (sparseToDenseMeasured p.1) fun a => denseConsumer (a, p.2)

/-- COO wins locally at this tariff, but loses after the required format bridge. -/
example : tariff uniform sparseProducer.2 < tariff uniform denseProducer.2 ∧
    tariff uniform densePipeline.2 < tariff uniform sparsePipeline.2 ∧
    sparsePipeline.1 = densePipeline.1 ∧ densePipeline.1 = ⟨#[3, 16], rfl⟩ := by decide

/-- The measured bridge uses the proved storage conversion, including duplicates. -/
example (a : Sparse Nat 2 2) :
    denseMatrix (sparseToDenseMeasured a).1 = sparseMatrix a := by
  rw [sparseToDenseMeasured_erases, sparseToDense_correct]

/-- Explicit zeros and cancelling duplicates still execute multiplication steps. -/
example : (sparseMeasured ([] : Sparse Int 1 1) ⟨#[7], rfl⟩).2 .scalarMul = 0 ∧
    (sparseMeasured ([⟨0, 0, 0⟩] : Sparse Int 1 1) (⟨#[7], rfl⟩ : Vector Int 1)).2 .scalarMul = 1 ∧
    (sparseMeasured ([⟨0, 0, 3⟩, ⟨0, 0, -3⟩] : Sparse Int 1 1)
      (⟨#[7], rfl⟩ : Vector Int 1)).2 .scalarMul = 2 := by
  simp only [sparseMeasured_cost]
  decide

example : (denseMeasured (⟨#[], rfl⟩ : Dense Nat 0 0) ⟨#[], rfl⟩).2 = 0 := by
  funext e
  rw [denseMeasured_cost]
  cases e <;> rfl

end StructuredLinearCostExamples

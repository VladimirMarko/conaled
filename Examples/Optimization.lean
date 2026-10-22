import Applications.Optimization.Transport
import Applications.Optimization.Relations
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Checked optimization specifications

The matrix alternatives are exactly two parenthesizations of dense exact
semiring multiplication. Work counts scalar multiplications at unit cost and
excludes additions. Storage counts only scalar slots in the first product,
excluding inputs, final output, kernel workspace and overlapping lifetimes.
No claim concerns all matrix algorithms, bit costs, or floating-point arithmetic.
-/

namespace Examples.Optimization

open _root_.Optimization

inductive Plan | left | right deriving DecidableEq
@[simp] theorem Plan.forall {p : Plan → Prop} : (∀ x, p x) ↔ p .left ∧ p .right := by
  constructor
  · exact fun h => ⟨h .left, h .right⟩
  · intro h x
    cases x
    · exact h.1
    · exact h.2

/-- Exact denotation for arbitrary matrices and dimensions. -/
def evaluate {S : Type*} [Semiring S] {a b c d : ℕ}
    (A : Matrix (Fin a) (Fin b) S) (B : Matrix (Fin b) (Fin c) S)
    (C : Matrix (Fin c) (Fin d) S) : Plan → Matrix (Fin a) (Fin d) S
  | .left => (A * B) * C
  | .right => A * (B * C)

theorem evaluate_eq {S : Type*} [Semiring S] {a b c d : ℕ}
    (A : Matrix (Fin a) (Fin b) S) (B : Matrix (Fin b) (Fin c) S)
    (C : Matrix (Fin c) (Fin d) S) (p : Plan) : evaluate A B C p = A * (B * C) := by
  cases p
  · exact Matrix.mul_assoc A B C
  · rfl

def work (a b c d : ℕ) : Plan → ℕ
  | .left => a*b*c + a*c*d
  | .right => b*c*d + a*b*d

def storage (a b c d : ℕ) : Plan → ℕ
  | .left => a*c
  | .right => b*d

theorem matrix_counts :
    work 2 5 20 5 .left = 400 ∧ work 2 5 20 5 .right = 550 ∧
    storage 2 5 20 5 .left = 40 ∧ storage 2 5 20 5 .right = 25 := by decide

/-- Reusable two-candidate least-cost proof, independent of a cost model. -/
theorem left_minimizes {K : Type*} [Preorder K] (J : Plan → K)
    (h : J .left ≤ J .right) : Plan.left ∈ minimizers Set.univ J := by
  refine ⟨Set.mem_univ _, ?_⟩
  intro p _
  cases p
  · exact le_rfl
  · exact h

theorem right_minimizes {K : Type*} [Preorder K] (J : Plan → K)
    (h : J .right ≤ J .left) : Plan.right ∈ minimizers Set.univ J := by
  refine ⟨Set.mem_univ _, ?_⟩
  intro p _
  cases p
  · exact h
  · exact le_rfl

theorem work_optimum : Plan.left ∈ minimizers Set.univ (work 2 5 20 5) :=
  left_minimizes _ (by decide)

theorem storage_optimum : Plan.right ∈ minimizers Set.univ (storage 2 5 20 5) :=
  right_minimizes _ (by decide)

/-- An ordinary algebraic proof establishes the target admissible set, and an
ordinary cost equality transports the choice. No compiler syntax is involved. -/
theorem matrix_work_transport {S : Type*} [Semiring S]
    (A : Matrix (Fin 2) (Fin 5) S) (B : Matrix (Fin 5) (Fin 20) S)
    (C : Matrix (Fin 20) (Fin 5) S) :
    Plan.left ∈ minimizers {p | evaluate A B C p = A * (B * C)} (work 2 5 20 5) :=
  minimizer_transport_of_surjOn (c := work 2 5 20 5) id id monotone_id
    (fun p _ => evaluate_eq A B C p) (fun _ _ => rfl)
    (fun p _ => ⟨p, Set.mem_univ _, rfl⟩) work_optimum

/-- Work and intermediate storage have no jointly least plan in product order. -/
theorem matrix_pareto :
    pareto Set.univ (fun p => (work 2 5 20 5 p, storage 2 5 20 5 p)) = Set.univ ∧
    minimizers Set.univ (fun p => (work 2 5 20 5 p, storage 2 5 20 5 p)) = ∅ := by
  constructor
  · ext p
    cases p <;> simp [pareto, work, storage, Plan.forall]
  · ext p
    cases p <;> simp [minimizers, isMinOn_iff, work, storage, Plan.forall]

/-- Workload maps compose in the same order as candidate maps. -/
theorem workload_composition :
    pullbackWorkload (fun n : ℕ => n + 1) (fun w : ℕ => w * 2)
      (pullbackWorkload (fun n => n * 3) (fun w => w + 5) (fun n w => n + w)) 2 4 = 22 := by
  rw [← pullbackWorkload_comp]
  rfl

/-- The positive real ray has infimum zero, but it has no least-cost candidate. -/
theorem positive_glb : IsGLB ((id : ℝ → ℝ) '' Set.Ioi 0) 0 := by
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    exact le_of_lt hx
  · intro b hb
    by_contra h
    have hpos : 0 < b := lt_of_not_ge h
    have hhalf := hb ⟨b/2, by change 0 < b/2; linarith, rfl⟩
    change b ≤ b/2 at hhalf
    linarith

theorem positive_infimum : sInf ((id : ℝ → ℝ) '' Set.Ioi 0) = 0 :=
  positive_glb.csInf_eq ⟨(1 : ℝ), (1 : ℝ), (show (0 : ℝ) < 1 from zero_lt_one), rfl⟩

theorem positive_not_attained : ¬ Attained (Set.Ioi (0 : ℝ)) id :=
  not_attained_of_improves (fun p hp => by
    refine ⟨p/2, ?_, ?_⟩
    · change 0 < p/2
      change 0 < p at hp
      linarith
    · change p/2 < p
      change 0 < p at hp
      linarith)

/-- Approximation can realize a positive bound despite nonattainment. The index
retains both an arbitrary problem label and its positive tolerance workload. -/
noncomputable def positiveApproximation :
    Relational.RelSquare (inputRep (ℕ × {ε : ℝ // 0 < ε}))
      (boundRep (fun _ : ℕ × {ε : ℝ // 0 < ε} => Set.Ioi (0 : ℝ))
        (fun _ => id) id) :=
  boundSquare _ _ id (fun i => i.2.val / 2) (fun i => i.2.val)
    (fun i => by change 0 < i.2.val / 2; linarith [i.2.property])
    (fun i => by change i.2.val / 2 ≤ i.2.val; linarith [i.2.property])

/-- Same returned value, reversed cost ranking. -/
def sourceCost : Plan → ℕ | .left => 1 | .right => 2
def targetCost : Plan → ℕ | .left => 100 | .right => 1

def constantSemantics : Squares.Rep where
  R := Plan
  S := ℕ
  decode _ := 0

def semanticOnly : Squares.Square constantSemantics constantSemantics where
  impl := id
  spec := id
  commutes _ := rfl

theorem semantic_only_not_optimal :
    Plan.left ∈ minimizers Set.univ sourceCost ∧
    semanticOnly.impl Plan.left ∉ minimizers Set.univ targetCost := by
  refine ⟨left_minimizes _ (by decide), ?_⟩
  intro h
  have bad := h.2 (Set.mem_univ Plan.right)
  change 100 ≤ 1 at bad
  omega

/-- A dominating lift can suffice even when the compiler is not surjective. -/
theorem dominating_lift_global :
    (0 : ℕ) ∈ minimizers Set.univ id := by
  have source : () ∈ minimizers Set.univ (fun _ : Unit => (0 : ℕ)) :=
    ⟨Set.mem_univ _, by intro q hq; exact (Nat.le_refl 0)⟩
  exact minimizer_transport (c := fun _ : Unit => (0 : ℕ))
    (fun _ => 0) id monotone_id (fun _ _ => Set.mem_univ _)
    (fun _ _ => rfl) (fun t _ => ⟨(), Set.mem_univ _, Nat.zero_le t⟩) source

/-- Exact image costs alone do not cover a cheaper target candidate. -/
theorem image_not_global :
    (1 : ℕ) ∈ minimizers ((fun _ : Unit => (1 : ℕ)) '' Set.univ) id ∧
    (1 : ℕ) ∉ minimizers Set.univ id := by
  constructor
  · exact minimizer_image (c := fun _ : Unit => (1 : ℕ)) (fun _ => 1) id
      monotone_id (fun _ _ => rfl) ⟨Set.mem_univ (), by intro q hq; exact (Nat.le_refl 1)⟩
  · intro h
    have bad := h.2 (Set.mem_univ 0)
    change 1 ≤ 0 at bad
    omega

/-- Reflection rules out selecting the expensive plan even in the cost
representation, which forgets plan syntax. -/
theorem reflected_nonoptimal :
    sourceCost Plan.right ∉ minimizers (sourceCost '' Set.univ) id := by
  intro h
  have source := minimizer_reflect (A := Set.univ) (B := sourceCost '' Set.univ)
    (c := sourceCost) (J := id) sourceCost (OrderIso.refl ℕ).toOrderEmbedding
    (fun p hp => ⟨p, hp, rfl⟩) (fun _ _ => rfl) (Set.mem_univ Plan.right) h
  have bad := source.2 (Set.mem_univ Plan.left)
  change 2 ≤ 1 at bad
  omega

/-- Complete-lattice objectives can describe sets of required resources. -/
def resourceCost : Plan → Set ℕ | .left => ∅ | .right => {0}

theorem resource_value_transport :
    value (resourceCost '' Set.univ) id = value Set.univ resourceCost := by
  exact value_transport resourceCost (sInfHom.id (Set ℕ))
    (fun p hp => ⟨p, hp, rfl⟩) (fun _ _ => rfl) (fun _ h => h)

theorem resource_value_attained : value Set.univ resourceCost = ∅ :=
  (minimizer_cost_eq_value (left_minimizes resourceCost (Set.empty_subset _))).symm

theorem empty_value : value (∅ : Set Plan) resourceCost = Set.univ := by
  simp [value]

/-- The resource observation requested by a matrix workload. -/
inductive Criterion | work | storage

/-- The matrix resource interpretation is part of the workload index. -/
def matrixObjective (i : ℕ × Criterion) : Plan → ℕ :=
  match i.2 with
  | .work => work 2 5 20 5
  | .storage => storage 2 5 20 5

def matrixSelection :
    Relational.RelSquare (inputRep (ℕ × Criterion))
      (membershipRep (I := ℕ × Criterion) (id : Plan → Plan)) :=
  selectionSquare (fun _ => Set.univ) matrixObjective id
    (fun i => match i.2 with
      | .work => Plan.left
      | .storage => Plan.right) (by
      rintro ⟨label, criterion⟩
      cases criterion
      · exact work_optimum
      · exact storage_optimum)

theorem selected_matrix_membership (label : ℕ) (criterion : Criterion) :
    (matrixSelection.impl (label, criterion)).1 = (label, criterion) ∧
    (matrixSelection.impl (label, criterion)).2 ∈
      minimizers Set.univ (matrixObjective (label, criterion)) :=
  matrixSelection.preserves rfl

/-- The classical selector is usable on the attained matrix problem without
claiming a particular tie-breaker or an algorithm. -/
theorem classical_matrix_selection :
    ((attainedSelectionSquare (fun _ : Unit => (Set.univ : Set Plan))
      (fun _ => work 2 5 20 5)).impl ⟨(), ⟨Plan.left, work_optimum⟩⟩).2 ∈
      minimizers Set.univ (work 2 5 20 5) :=
  ((attainedSelectionSquare (fun _ : Unit => (Set.univ : Set Plan))
    (fun _ => work 2 5 20 5)).preserves (r := ⟨(), ⟨Plan.left, work_optimum⟩⟩) rfl).2

theorem approximate_positive_bound (label : ℕ) (ε : {ε : ℝ // 0 < ε}) :
    (positiveApproximation.impl (label, ε)).1 = (label, ε) ∧
    0 < (positiveApproximation.impl (label, ε)).2 ∧
    (positiveApproximation.impl (label, ε)).2 ≤ ε.val :=
  positiveApproximation.preserves rfl

end Examples.Optimization

import Mathlib.Order.Filter.Extr
import Mathlib.Order.Hom.CompleteLattice

/-!
# Optimization specifications

Admissibility and objectives are ordinary sets and functions. Least-cost
minimizers require only a preorder; Pareto candidates need not have least cost.
An infimum in a complete lattice exists even for an empty feasible set.
Selection is a separate, potentially noncomputable operation requiring attainment.
-/

namespace Optimization

universe u v w

variable {P : Type u} {K : Type v}

/-- Feasible candidates whose cost is below every feasible cost. -/
def minimizers [Preorder K] (A : Set P) (J : P → K) : Set P :=
  {p | p ∈ A ∧ IsMinOn J A p}

/-- Nondominated costs: improving a candidate weakly cannot improve it strictly.
This is not the assertion that its cost is below every feasible cost. -/
def pareto [Preorder K] (A : Set P) (J : P → K) : Set P :=
  {p | p ∈ A ∧ ∀ q ∈ A, J q ≤ J p → J p ≤ J q}

theorem minimizers_subset_pareto [Preorder K] (A : Set P) (J : P → K) :
    minimizers A J ⊆ pareto A J := by
  intro p hp
  exact ⟨hp.1, fun q hq _ => hp.2 hq⟩

theorem mem_minimizers_iff_isLeast [Preorder K] {A : Set P} {J : P → K} {p : P} :
    p ∈ minimizers A J ↔ p ∈ A ∧ IsLeast (J '' A) (J p) := by
  constructor
  · rintro ⟨hp, h⟩
    exact ⟨hp, ⟨p, hp, rfl⟩, fun _ ⟨q, hq, heq⟩ => heq ▸ h hq⟩
  · rintro ⟨hp, _, h⟩
    exact ⟨hp, fun _ hq => h ⟨_, hq, rfl⟩⟩

/-- Existence of a least-cost feasible candidate, without a chosen witness. -/
def Attained [Preorder K] (A : Set P) (J : P → K) : Prop :=
  (minimizers A J).Nonempty

/-- A strictly cheaper feasible alternative for every candidate rules out
attainment, regardless of whether a greatest lower bound exists. -/
theorem not_attained_of_improves [Preorder K] {A : Set P} {J : P → K}
    (improve : ∀ p ∈ A, ∃ q ∈ A, J q < J p) : ¬ Attained A J := by
  rintro ⟨p, hp, hmin⟩
  obtain ⟨q, hq, hlt⟩ := improve p hp
  exact (not_le_of_gt hlt) (hmin hq)

noncomputable def select [Preorder K] {A : Set P} {J : P → K}
    (h : Attained A J) : P := Classical.choose h

theorem select_mem [Preorder K] {A : Set P} {J : P → K} (h : Attained A J) :
    select h ∈ minimizers A J := Classical.choose_spec h

/-- General infimum value. Conditional completeness requires separate hypotheses;
for example real-valued clients can instead establish `IsGLB (J '' A) v`. -/
noncomputable def value [CompleteLattice K] (A : Set P) (J : P → K) : K :=
  sInf (J '' A)

theorem minimizer_cost_eq_value [CompleteLattice K] {A : Set P} {J : P → K}
    {p : P} (hp : p ∈ minimizers A J) : J p = value A J := by
  apply le_antisymm
  · exact le_sInf (fun _ ⟨q, hq, heq⟩ => heq ▸ hp.2 hq)
  · exact sInf_le ⟨p, hp.1, rfl⟩

theorem mem_minimizers_iff_cost_eq_value [CompleteLattice K]
    {A : Set P} {J : P → K} {p : P} :
    p ∈ minimizers A J ↔ p ∈ A ∧ J p = value A J := by
  constructor
  · intro hp
    exact ⟨hp.1, minimizer_cost_eq_value hp⟩
  · rintro ⟨hp, heq⟩
    refine ⟨hp, fun q hq => ?_⟩
    rw [heq]
    exact sInf_le ⟨q, hq, rfl⟩

/-- Ordinary objective precomposition; no evaluation or optimization algorithm. -/
def pullback {Q : Type w} (C : P → Q) (J : Q → K) : P → K := J ∘ C

@[simp] theorem pullback_id (J : P → K) : pullback id J = J := rfl

theorem pullback_comp {Q R : Type*} (C : P → Q) (D : Q → R) (J : R → K) :
    pullback (D ∘ C) J = pullback C (pullback D J) := rfl

/-- Change both candidate interpretation and workload. -/
def pullbackWorkload {Q W V : Type*} (C : P → Q) (e : W → V)
    (J : Q → V → K) : P → W → K := fun p w => J (C p) (e w)

@[simp] theorem pullbackWorkload_id {W : Type*} (J : P → W → K) :
    pullbackWorkload id id J = J := rfl

theorem pullbackWorkload_comp {Q R W V U : Type*}
    (C : P → Q) (D : Q → R) (e : W → V) (f : V → U) (J : R → U → K) :
    pullbackWorkload (D ∘ C) (f ∘ e) J =
      pullbackWorkload C e (pullbackWorkload D f J) := rfl

end Optimization

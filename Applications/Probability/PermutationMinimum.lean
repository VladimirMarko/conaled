import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Set.Card
import Mathlib.Probability.UniformOn

/-!
# Fixed-subset minima under a uniform permutation

An ordinary permutation assigns each key index a distinct priority label.
Every observed subset uses that same permutation. For an injective priority
function into a linear order, each member of a fixed nonempty finite subset
has the same probability of being its minimum.

The event records membership as well as comparison. Its elementary laws do
not require finite indices, injective priorities or a probability space.
The probability law uses the existing uniform measure on permutations and
keeps its measurable structure explicit. No measurable structure or order
is required on the index type, and the priority target may be infinite.

Right composition by a key transposition exchanges two members' minimum
events. Their equal masses sum to one because distinct assigned priorities
give a unique minimum in every sample. This law concerns fixed subsets;
conditional histories and the full induced relative order are separate
claims. In particular, overlapping subsets still share their random input.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Applications.Probability.PermutationMinimum

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

universe u v w

variable {I : Type u} {P : Type v}

/-- The candidate is a member of the subset and has no larger assigned
priority than any of its members. The permutation maps keys to labels. -/
def minimumEvent [LE P] (priority : I → P) (S : Finset I) (a : I) :
    Set (Equiv.Perm I) :=
  {π | a ∈ S ∧ ∀ b ∈ S, priority (π a) ≤ priority (π b)}

@[simp] theorem mem_minimumEvent [LE P] (priority : I → P) (S : Finset I)
    (a : I) (π : Equiv.Perm I) :
    π ∈ minimumEvent priority S a ↔
      a ∈ S ∧ ∀ b ∈ S, priority (π a) ≤ priority (π b) :=
  Iff.rfl

/-- An empty subset has no minimum member. -/
@[simp] theorem minimumEvent_empty [LE P] (priority : I → P) (a : I) :
    minimumEvent priority ∅ a = ∅ := by
  simp [minimumEvent]

/-- Comparisons alone do not turn an outsider into a minimum member. -/
theorem minimumEvent_of_not_mem [LE P] (priority : I → P) (S : Finset I)
    (a : I) (ha : a ∉ S) : minimumEvent priority S a = ∅ := by
  simp [minimumEvent, ha]

/-- The sole member of a singleton is a minimum in every sample. -/
@[simp] theorem minimumEvent_singleton [Preorder P] (priority : I → P) (a : I) :
    minimumEvent priority {a} a = Set.univ := by
  simp [minimumEvent]

/-- Two minimum observations of the same member and the same permutation
combine into the minimum observation on the union. -/
theorem minimumEvent_inter [LE P] [DecidableEq I] (priority : I → P)
    (S T : Finset I) (a : I) (haS : a ∈ S) (haT : a ∈ T) :
    minimumEvent priority S a ∩ minimumEvent priority T a =
      minimumEvent priority (S ∪ T) a := by
  apply Set.ext
  intro π
  constructor
  · rintro ⟨hS, hT⟩
    refine ⟨Finset.mem_union.mpr (Or.inl haS), ?_⟩
    intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact hS.2 b hb
    · exact hT.2 b hb
  · intro h
    constructor
    · exact ⟨haS, fun b hb => h.2 b (Finset.mem_union.mpr (Or.inl hb))⟩
    · exact ⟨haT, fun b hb => h.2 b (Finset.mem_union.mpr (Or.inr hb))⟩

private theorem swap_mem_iff [DecidableEq I] (S : Finset I) (a b : I)
    (ha : a ∈ S) (hb : b ∈ S) (x : I) :
    Equiv.swap a b x ∈ S ↔ x ∈ S := by
  by_cases hxa : x = a
  · subst x
    simp [ha, hb]
  by_cases hxb : x = b
  · subst x
    simp [ha, hb]
  simp only [Equiv.swap_apply_of_ne_of_ne hxa hxb]

private theorem minimumEvent_swap_preimage [LE P] [DecidableEq I]
    (priority : I → P) (S : Finset I) (a b : I) (ha : a ∈ S) (hb : b ∈ S) :
    (fun π : Equiv.Perm I => π * Equiv.swap a b) ⁻¹'
        minimumEvent priority S b =
      minimumEvent priority S a := by
  apply Set.ext
  intro π
  change
    (b ∈ S ∧ ∀ x ∈ S,
      priority ((π * Equiv.swap a b) b) ≤ priority ((π * Equiv.swap a b) x)) ↔
    (a ∈ S ∧ ∀ x ∈ S, priority (π a) ≤ priority (π x))
  constructor
  · intro h
    refine ⟨ha, ?_⟩
    intro x hx
    have hx' := (swap_mem_iff S a b ha hb x).2 hx
    have hcompare := h.2 (Equiv.swap a b x) hx'
    simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_self] using hcompare
  · intro h
    refine ⟨hb, ?_⟩
    intro x hx
    have hx' := (swap_mem_iff S a b ha hb x).2 hx
    have hcompare := h.2 (Equiv.swap a b x) hx'
    simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_right] using hcompare

private theorem uniformOn_univ_preimage {Ω : Type w} [Finite Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (e : Ω ≃ Ω) (E : Set Ω) :
    uniformOn Set.univ (e ⁻¹' E) = uniformOn Set.univ E := by
  classical
  let := Fintype.ofFinite Ω
  rw [uniformOn_univ, uniformOn_univ,
    Measure.count_apply (e ⁻¹' E).toFinite.measurableSet,
    Measure.count_apply E.toFinite.measurableSet,
    Set.encard_preimage_of_bijective e.bijective E]

private theorem uniformOn_minimumEvent_eq [Finite I] [LE P]
    [MeasurableSpace (Equiv.Perm I)] [MeasurableSingletonClass (Equiv.Perm I)]
    (priority : I → P) (S : Finset I) (a b : I) (ha : a ∈ S) (hb : b ∈ S) :
    uniformOn Set.univ (minimumEvent priority S a) =
      uniformOn Set.univ (minimumEvent priority S b) := by
  classical
  let := Fintype.ofFinite I
  have h := uniformOn_univ_preimage
    (Equiv.mulRight (Equiv.swap a b)) (minimumEvent priority S b)
  simpa only [Equiv.coe_mulRight,
    minimumEvent_swap_preimage priority S a b ha hb] using h

private theorem minimumEvent_iUnion [LinearOrder P] (priority : I → P)
    (S : Finset I) (hS : S.Nonempty) :
    (⋃ a ∈ S, minimumEvent priority S a) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro π
  obtain ⟨a, ha, hmin⟩ :=
    Finset.exists_min_image S (fun b => priority (π b)) hS
  exact Set.mem_iUnion.mpr
    ⟨a, Set.mem_iUnion.mpr ⟨ha, ⟨ha, hmin⟩⟩⟩

private theorem minimumEvent_pairwiseDisjoint [PartialOrder P]
    (priority : I → P) (hinj : Function.Injective priority) (S : Finset I) :
    Set.PairwiseDisjoint (↑S) (minimumEvent priority S) := by
  intro a ha b hb hab
  apply Set.disjoint_left.mpr
  intro π hπa hπb
  exact hab (π.injective (hinj
    (le_antisymm (hπa.2 b hb) (hπb.2 a ha))))

/-- Under one uniform global permutation, every member of a fixed subset
has reciprocal-cardinality probability of being its minimum. Membership
supplies nonemptiness; injectivity of the priority function excludes ties. -/
theorem uniformOn_minimumEvent [Finite I] [LinearOrder P]
    [MeasurableSpace (Equiv.Perm I)] [MeasurableSingletonClass (Equiv.Perm I)]
    (priority : I → P) (hinj : Function.Injective priority)
    (S : Finset I) (a : I) (ha : a ∈ S) :
    uniformOn (Set.univ : Set (Equiv.Perm I)) (minimumEvent priority S a) =
      (S.card : ℝ≥0∞)⁻¹ := by
  classical
  let := Fintype.ofFinite I
  have hpartition :=
    measure_biUnion_finset (μ := uniformOn (Set.univ : Set (Equiv.Perm I)))
      (minimumEvent_pairwiseDisjoint priority hinj S)
      (fun b _ => (minimumEvent priority S b).toFinite.measurableSet)
  rw [minimumEvent_iUnion priority S ⟨a, ha⟩, measure_univ] at hpartition
  have hsum :
      (∑ b ∈ S, uniformOn Set.univ (minimumEvent priority S b)) =
        (S.card : ℝ≥0∞) * uniformOn Set.univ (minimumEvent priority S a) := by
    calc
      _ = ∑ _b ∈ S, uniformOn Set.univ (minimumEvent priority S a) := by
        apply Finset.sum_congr rfl
        intro b hb
        exact uniformOn_minimumEvent_eq priority S b a hb ha
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  apply ENNReal.eq_inv_of_mul_eq_one_left
  calc
    uniformOn Set.univ (minimumEvent priority S a) * (S.card : ℝ≥0∞) =
        (S.card : ℝ≥0∞) * uniformOn Set.univ (minimumEvent priority S a) :=
      mul_comm _ _
    _ = ∑ b ∈ S, uniformOn Set.univ (minimumEvent priority S b) := hsum.symm
    _ = 1 := hpartition.symm

end Applications.Probability.PermutationMinimum

import Applications.Probability.PermutationTail
import Applications.Resources.QuickSortTransport
import Applications.Resources.QuickSortMean
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Order.Interval.Finset.Fin

/-!
# The actual first-pivot mean under uniform input order

Every observation below is the exercise-cost coordinate of the existing
two-filter execution. The original permutation is sampled once. Revealing its
selected head conditions that same measure; both recursive inputs are filters
of its actual tail. Only their individual restricted-order laws are used.

The integral equation is first proved for an arbitrary Boolean comparator.
Distinct ordered keys enter when ranking the selected key image. Cardinal
induction stays in the fixed finite environment. The arbitrary-payload wrapper
then varies the occurrence environment with input length, giving a genuine
Nat-indexed asymptotic family without a measure or equality instance on payloads.
Mapping and occurrence lookup transport observations and are not charged work.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.UniformQuickSortMean

open MeasureTheory ProbabilityTheory
open Applications.Probability.PermutationOrder
open Applications.Probability.PermutationTail
open scoped ENNReal BigOperators

universe u v w

variable {I : Type u} {α : Type v} {κ : Type w}

section Labels

variable [DecidableEq I]

/-- The two source filters use true and false outcomes of the same comparator. -/
def leftChild (lt : I → I → Bool) (S : Finset I) (a : I) : Finset I :=
  (S.erase a).filter (fun b => lt b a = true)

def rightChild (lt : I → I → Bool) (S : Finset I) (a : I) : Finset I :=
  (S.erase a).filter (fun b => lt b a = false)

@[simp] theorem mem_leftChild (lt : I → I → Bool) (S : Finset I) (a b : I) :
    b ∈ leftChild lt S a ↔ b ≠ a ∧ b ∈ S ∧ lt b a = true := by
  simp [leftChild, and_assoc]

@[simp] theorem mem_rightChild (lt : I → I → Bool) (S : Finset I) (a b : I) :
    b ∈ rightChild lt S a ↔ b ≠ a ∧ b ∈ S ∧ lt b a = false := by
  simp [rightChild, and_assoc]

theorem leftChild_subset_erase (lt : I → I → Bool) (S : Finset I) (a : I) :
    leftChild lt S a ⊆ S.erase a := Finset.filter_subset _ _

theorem rightChild_subset_erase (lt : I → I → Bool) (S : Finset I) (a : I) :
    rightChild lt S a ⊆ S.erase a := Finset.filter_subset _ _

theorem children_disjoint (lt : I → I → Bool) (S : Finset I) (a : I) :
    Disjoint (leftChild lt S a) (rightChild lt S a) := by
  apply Finset.disjoint_left.mpr
  intro b hbL hbR
  have ht := (mem_leftChild lt S a b).mp hbL
  have hf := (mem_rightChild lt S a b).mp hbR
  rw [ht.2.2] at hf
  exact Bool.noConfusion hf.2.2

theorem children_union (lt : I → I → Bool) (S : Finset I) (a : I) :
    leftChild lt S a ∪ rightChild lt S a = S.erase a := by
  ext b
  cases h : lt b a <;> simp [leftChild, rightChild, h]

theorem children_card (lt : I → I → Bool) (S : Finset I) (a : I) (ha : a ∈ S) :
    (leftChild lt S a).card + (rightChild lt S a).card = S.card - 1 := by
  rw [← Finset.card_union_of_disjoint (children_disjoint lt S a),
    children_union, Finset.card_erase_of_mem ha]

theorem leftChild_card_lt (lt : I → I → Bool) (S : Finset I) (a : I) (ha : a ∈ S) :
    (leftChild lt S a).card < S.card := by
  have hle := Finset.card_le_card (leftChild_subset_erase lt S a)
  have he := Finset.card_erase_add_one ha
  omega

theorem rightChild_card_lt (lt : I → I → Bool) (S : Finset I) (a : I) (ha : a ∈ S) :
    (rightChild lt S a).card < S.card := by
  have hle := Finset.card_le_card (rightChild_subset_erase lt S a)
  have he := Finset.card_erase_add_one ha
  omega

/-- The real observation of the existing measured execution on the actual order. -/
def observedCost (positions : List I) (lt : I → I → Bool) (S : Finset I)
    (π : Equiv.Perm I) : ℝ :=
  QuickSort.exerciseCost lt (restrictedOrder positions S π)

/-- On a revealed-head event, the actual left filter is the original child
projection of the same sampled permutation. -/
theorem left_filter_on_first (positions : List I) (hnd : positions.Nodup)
    (lt : I → I → Bool) (S : Finset I) (a : I) (π : Equiv.Perm I)
    (hπ : π ∈ firstEvent (restrictedOrder positions S) a) :
    (restrictedOrder positions S π).tail.filter (fun b => lt b a) =
      restrictedOrder positions (leftChild lt S a) π := by
  calc
    _ = (restrictedOrder positions S π).tail.filter
        (fun b => decide (b ∈ leftChild lt S a)) := by
      apply List.filter_congr
      intro b hb
      rw [tail_restrictedOrder_eq positions hnd S a π hπ] at hb
      have hbrem := ((mem_restrictedOrder positions (S.erase a) π b).mp hb).2
      cases h : lt b a <;> simp [leftChild, hbrem, h]
    _ = _ := filter_tail_restrictedOrder_eq positions hnd S a π hπ
      (leftChild lt S a) (leftChild_subset_erase lt S a)

theorem right_filter_on_first (positions : List I) (hnd : positions.Nodup)
    (lt : I → I → Bool) (S : Finset I) (a : I) (π : Equiv.Perm I)
    (hπ : π ∈ firstEvent (restrictedOrder positions S) a) :
    (restrictedOrder positions S π).tail.filter (fun b => !(lt b a)) =
      restrictedOrder positions (rightChild lt S a) π := by
  calc
    _ = (restrictedOrder positions S π).tail.filter
        (fun b => decide (b ∈ rightChild lt S a)) := by
      apply List.filter_congr
      intro b hb
      rw [tail_restrictedOrder_eq positions hnd S a π hπ] at hb
      have hbrem := ((mem_restrictedOrder positions (S.erase a) π b).mp hb).2
      cases h : lt b a <;> simp [rightChild, hbrem, h]
    _ = _ := filter_tail_restrictedOrder_eq positions hnd S a π hπ
      (rightChild lt S a) (rightChild_subset_erase lt S a)

/-- This pointwise recurrence is derived from the source's actual cons equation.
It asserts neither independent child inputs nor an unconditional tail equation. -/
theorem observedCost_on_first (positions : List I) (hnd : positions.Nodup)
    (hcomplete : ∀ b, b ∈ positions) (lt : I → I → Bool) (S : Finset I)
    (a : I) (π : Equiv.Perm I)
    (hπ : π ∈ firstEvent (restrictedOrder positions S) a) :
    observedCost positions lt S π =
      observedCost positions lt (leftChild lt S a) π +
        observedCost positions lt (rightChild lt S a) π +
          ((4 * (S.card - 1) + 3 : Nat) : ℝ) := by
  obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp hπ
  have hlen := restrictedOrder_length positions hnd hcomplete S π
  rw [hys, List.length_cons] at hlen
  have htail : ys.length = S.card - 1 := by omega
  have hleft := left_filter_on_first positions hnd lt S a π hπ
  have hright := right_filter_on_first positions hnd lt S a π hπ
  rw [hys, List.tail_cons] at hleft hright
  have hcost := QuickSort.exerciseCost_cons lt a ys
  rw [hleft, hright, htail] at hcost
  unfold observedCost
  rw [hys, hcost]
  push_cast
  ring

section Probability

variable [MeasurableSpace (Equiv.Perm I)] [MeasurableSingletonClass (Equiv.Perm I)]

/-- The original uniform-input mean, before any head is exposed. -/
noncomputable def meanBy (positions : List I) (lt : I → I → Bool) (S : Finset I) : ℝ :=
  ∫ π, observedCost positions lt S π ∂uniformOn (Set.univ : Set (Equiv.Perm I))

theorem integrable_observedCost (positions : List I) (hcomplete : ∀ b, b ∈ positions)
    (lt : I → I → Bool) (S : Finset I) :
    Integrable (observedCost positions lt S)
      (uniformOn (Set.univ : Set (Equiv.Perm I))) := by
  let := Fintype.ofList positions hcomplete
  exact Integrable.of_finite

theorem firstEvent_positive_finite (positions : List I) (hnd : positions.Nodup)
    (hcomplete : ∀ b, b ∈ positions) (S : Finset I) (a : I) (ha : a ∈ S) :
    0 < uniformOn (Set.univ : Set (Equiv.Perm I))
        (firstEvent (restrictedOrder positions S) a) ∧
      uniformOn (Set.univ : Set (Equiv.Perm I))
        (firstEvent (restrictedOrder positions S) a) ≠ ∞ := by
  simp only [uniformOn_firstEvent positions hnd hcomplete S a ha]
  have hn : S.card ≠ 0 := Nat.ne_of_gt (Finset.card_pos.mpr ⟨a, ha⟩)
  simp [hn]

/-- Original and conditioned integrability both concern the same finite sample
space. No integrability of a hypothetical independent recursion is used. -/
theorem integrable_observedCost_cond (positions : List I) (hnd : positions.Nodup)
    (hcomplete : ∀ b, b ∈ positions) (lt : I → I → Bool)
    (S : Finset I) (a : I) (ha : a ∈ S) (T : Finset I) :
    Integrable (observedCost positions lt T)
      ((uniformOn (Set.univ : Set (Equiv.Perm I)))[|
        firstEvent (restrictedOrder positions S) a]) := by
  let := Fintype.ofList positions hcomplete
  let : IsProbabilityMeasure
      ((uniformOn (Set.univ : Set (Equiv.Perm I)))[|
        firstEvent (restrictedOrder positions S) a]) :=
    cond_isProbabilityMeasure
      (ne_of_gt (firstEvent_positive_finite positions hnd hcomplete S a ha).1)
  exact Integrable.of_finite

@[simp] theorem meanBy_empty (positions : List I) (hcomplete : ∀ b, b ∈ positions)
    (lt : I → I → Bool) : meanBy positions lt ∅ = 1 := by
  let := Fintype.ofList positions hcomplete
  simp [meanBy, observedCost, restrictedOrder]

theorem meanBy_singleton (positions : List I) (hnd : positions.Nodup)
    (hcomplete : ∀ b, b ∈ positions) (lt : I → I → Bool) (a : I) :
    meanBy positions lt {a} = 5 := by
  let := Fintype.ofList positions hcomplete
  have horder : ∀ π : Equiv.Perm I, restrictedOrder positions {a} π = [a] := by
    intro π
    apply List.perm_singleton.mp
    apply (List.perm_ext_iff_of_nodup
      (restrictedOrder_nodup positions hnd {a} π) (by simp)).mpr
    intro b
    simp [mem_restrictedOrder_of_complete positions hcomplete]
  simp [meanBy, observedCost, horder]

/-- All-false behavior on selected keys is an actual quadratic execution
family. Distinct occurrences by themselves do not imply distinct sort keys. -/
theorem observedCost_of_all_false (positions : List I) (hnd : positions.Nodup)
    (hcomplete : ∀ b, b ∈ positions) (lt : I → I → Bool) (S : Finset I)
    (hfalse : ∀ a ∈ S, ∀ b ∈ S, lt b a = false) (π : Equiv.Perm I) :
    observedCost positions lt S π = ((2 * S.card ^ 2 + 2 * S.card + 1 : Nat) : ℝ) := by
  have hs : (restrictedOrder positions S π).Pairwise (fun a b => lt b a = false) := by
    apply List.pairwise_of_forall_mem_list
    intro a ha b hb
    exact hfalse a ((mem_restrictedOrder positions S π a).mp ha).2
      b ((mem_restrictedOrder positions S π b).mp hb).2
  have hc := (QuickSort.costs_of_all_right lt (restrictedOrder positions S π) hs).1
  rw [restrictedOrder_length positions hnd hcomplete S π] at hc
  exact_mod_cast hc

theorem meanBy_of_all_false (positions : List I) (hnd : positions.Nodup)
    (hcomplete : ∀ b, b ∈ positions) (lt : I → I → Bool) (S : Finset I)
    (hfalse : ∀ a ∈ S, ∀ b ∈ S, lt b a = false) :
    meanBy positions lt S = ((2 * S.card ^ 2 + 2 * S.card + 1 : Nat) : ℝ) := by
  let := Fintype.ofList positions hcomplete
  unfold meanBy
  simp_rw [observedCost_of_all_false positions hnd hcomplete lt S hfalse]
  simp

/-- A fixed remaining subset has the same cost expectation under conditioning.
The two HasLaw records share a target order law; no joint law is required. -/
theorem child_integral_cond (positions : List I) (hnd : positions.Nodup)
    (hcomplete : ∀ b, b ∈ positions) (lt : I → I → Bool)
    (S : Finset I) (a : I) (ha : a ∈ S) (T : Finset I) (hT : T ⊆ S.erase a) :
    (∫ π, observedCost positions lt T π ∂
      (uniformOn (Set.univ : Set (Equiv.Perm I)))[|
        firstEvent (restrictedOrder positions S) a]) = meanBy positions lt T := by
  classical
  let := Fintype.ofList positions hcomplete
  let : MeasurableSpace (List I) := ⊤
  let : MeasurableSingletonClass (List I) := ⟨fun _ => trivial⟩
  have hc : HasLaw (restrictedOrder positions T)
      (uniformOn (orders positions T : Set (List I)))
      ((uniformOn (Set.univ : Set (Equiv.Perm I)))[|
        firstEvent (restrictedOrder positions S) a]) := {
    aemeasurable := (measurable_of_finite _).aemeasurable
    map_eq := map_restrictedOrder_cond_first positions hnd hcomplete S a ha T hT
  }
  have hu : HasLaw (restrictedOrder positions T)
      (uniformOn (orders positions T : Set (List I)))
      (uniformOn (Set.univ : Set (Equiv.Perm I))) := {
    aemeasurable := (measurable_of_finite _).aemeasurable
    map_eq := map_restrictedOrder_uniformOn positions hnd hcomplete T
  }
  have hf : AEStronglyMeasurable (fun ys : List I => (QuickSort.exerciseCost lt ys : ℝ))
      (uniformOn (orders positions T : Set (List I))) :=
    AEStronglyMeasurable.of_discrete
  exact (hc.integral_comp hf).trans (hu.integral_comp hf).symm

theorem conditional_mean (positions : List I) (hnd : positions.Nodup)
    (hcomplete : ∀ b, b ∈ positions) (lt : I → I → Bool)
    (S : Finset I) (a : I) (ha : a ∈ S) :
    (∫ π, observedCost positions lt S π ∂
      (uniformOn (Set.univ : Set (Equiv.Perm I)))[|
        firstEvent (restrictedOrder positions S) a]) =
      meanBy positions lt (leftChild lt S a) +
        meanBy positions lt (rightChild lt S a) + ((4 * (S.card - 1) + 3 : Nat) : ℝ) := by
  let := Fintype.ofList positions hcomplete
  let : IsProbabilityMeasure
      ((uniformOn (Set.univ : Set (Equiv.Perm I)))[|
        firstEvent (restrictedOrder positions S) a]) :=
    cond_isProbabilityMeasure
      (ne_of_gt (firstEvent_positive_finite positions hnd hcomplete S a ha).1)
  have hE : MeasurableSet (firstEvent (restrictedOrder positions S) a) :=
    (Set.toFinite _).measurableSet
  have heq := ae_cond_of_forall_mem hE
    (fun π hπ => observedCost_on_first positions hnd hcomplete lt S a π hπ)
  rw [integral_congr_ae heq]
  rw [integral_add
    ((integrable_observedCost_cond positions hnd hcomplete lt S a ha _).add
      (integrable_observedCost_cond positions hnd hcomplete lt S a ha _))
    (integrable_const _)]
  rw [integral_add
    (integrable_observedCost_cond positions hnd hcomplete lt S a ha _)
    (integrable_observedCost_cond positions hnd hcomplete lt S a ha _)]
  rw [child_integral_cond positions hnd hcomplete lt S a ha _
    (leftChild_subset_erase lt S a),
    child_integral_cond positions hnd hcomplete lt S a ha _
    (rightChild_subset_erase lt S a)]
  simp

theorem firstEvents_disjoint (positions : List I) (S : Finset I) :
    Set.Pairwise (S : Set I)
      (Disjoint on (fun a => firstEvent (restrictedOrder positions S) a)) := by
  intro a _ b _ hab
  apply Set.disjoint_left.mpr
  intro π hπa hπb
  exact hab (Option.some.inj (hπa.symm.trans hπb))

theorem firstEvents_cover (positions : List I) (hnd : positions.Nodup)
    (hcomplete : ∀ b, b ∈ positions) (S : Finset I) (hS : S.Nonempty) :
    (⋃ a ∈ S, firstEvent (restrictedOrder positions S) a) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro π
  have hlen := restrictedOrder_length positions hnd hcomplete S π
  have hpos := Finset.card_pos.mpr hS
  cases hxs : restrictedOrder positions S π with
  | nil => simp [hxs] at hlen; omega
  | cons a ys =>
      have ha : a ∈ S := ((mem_restrictedOrder positions S π a).mp
        (by rw [hxs]; exact List.mem_cons_self)).2
      exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨ha, by simp [firstEvent, hxs]⟩⟩

/-- Normalization of one restricted integral uses the positive, finite head
mass. Division at zero is never used to recover the original expectation. -/
theorem first_integral (positions : List I) (hnd : positions.Nodup)
    (hcomplete : ∀ b, b ∈ positions) (lt : I → I → Bool)
    (S : Finset I) (a : I) (ha : a ∈ S) :
    (∫ π in firstEvent (restrictedOrder positions S) a,
      observedCost positions lt S π ∂uniformOn (Set.univ : Set (Equiv.Perm I))) =
      (1 / (S.card : ℝ)) * (meanBy positions lt (leftChild lt S a) +
        meanBy positions lt (rightChild lt S a) + ((4 * (S.card - 1) + 3 : Nat) : ℝ)) := by
  have hn : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.card_pos.mpr ⟨a, ha⟩))
  have hc := conditional_mean positions hnd hcomplete lt S a ha
  unfold ProbabilityTheory.cond at hc
  rw [integral_smul_measure,
    uniformOn_firstEvent positions hnd hcomplete S a ha, inv_inv] at hc
  simp only [ENNReal.toReal_natCast, smul_eq_mul] at hc
  rw [one_div, ← hc]
  field_simp [hn]

/-- The actual first-pivot integral equation, with no key-order hypothesis. -/
theorem meanBy_recurrence (positions : List I) (hnd : positions.Nodup)
    (hcomplete : ∀ b, b ∈ positions) (lt : I → I → Bool)
    (S : Finset I) (hS : S.Nonempty) :
    meanBy positions lt S = (1 / (S.card : ℝ)) *
      ∑ a ∈ S, (meanBy positions lt (leftChild lt S a) +
        meanBy positions lt (rightChild lt S a) + ((4 * (S.card - 1) + 3 : Nat) : ℝ)) := by
  let := Fintype.ofList positions hcomplete
  have hsplit := integral_biUnion_finset S
    (fun a _ => (Set.toFinite (firstEvent (restrictedOrder positions S) a)).measurableSet)
    (firstEvents_disjoint positions S)
    (fun _ _ => (integrable_observedCost positions hcomplete lt S).integrableOn)
  rw [firstEvents_cover positions hnd hcomplete S hS, Measure.restrict_univ] at hsplit
  change meanBy positions lt S = _ at hsplit
  rw [hsplit, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun a ha => first_integral positions hnd hcomplete lt S a ha)

end Probability

section Keys

variable [LinearOrder κ]

theorem injOn_leftChild (key : I → κ) (lt : I → I → Bool) (S : Finset I)
    (hinj : Set.InjOn key (S : Set I)) (a : I) :
    Set.InjOn key (leftChild lt S a : Set I) := by
  intro b hb c hc h
  exact hinj ((mem_leftChild lt S a b).mp hb).2.1
    ((mem_leftChild lt S a c).mp hc).2.1 h

theorem injOn_rightChild (key : I → κ) (lt : I → I → Bool) (S : Finset I)
    (hinj : Set.InjOn key (S : Set I)) (a : I) :
    Set.InjOn key (rightChild lt S a : Set I) := by
  intro b hb c hc h
  exact hinj ((mem_rightChild lt S a b).mp hb).2.1
    ((mem_rightChild lt S a c).mp hc).2.1 h

/-- Key distinctness is local to the selected support, including each child. -/
theorem restrictedOrder_keys_nodup (positions : List I) (hnd : positions.Nodup)
    (key : I → κ) (S : Finset I) (hinj : Set.InjOn key (S : Set I))
    (π : Equiv.Perm I) : ((restrictedOrder positions S π).map key).Nodup := by
  apply List.Nodup.map_on _ (restrictedOrder_nodup positions hnd S π)
  intro a ha b hb h
  exact hinj ((mem_restrictedOrder positions S π a).mp ha).2
    ((mem_restrictedOrder positions S π b).mp hb).2 h

/-- Under distinct keys the actual false filter becomes strict greater-than
on the erased support. The generic source definition remains a complement. -/
theorem mem_rightChild_key (key : I → κ) (S : Finset I)
    (hinj : Set.InjOn key (S : Set I)) (a : I) (ha : a ∈ S) (b : I) :
    b ∈ rightChild (fun x y => decide (key x < key y)) S a ↔
      b ∈ S ∧ key a < key b := by
  rw [mem_rightChild]
  simp only [decide_eq_false_iff_not, not_lt]
  constructor
  · rintro ⟨hba, hb, hle⟩
    refine ⟨hb, lt_of_le_of_ne hle ?_⟩
    intro h
    exact hba (hinj hb ha h.symm)
  · rintro ⟨hb, hlt⟩
    refine ⟨?_, hb, hlt.le⟩
    intro h
    subst b
    exact (lt_irrefl _ hlt)

private noncomputable def keyEquiv (key : I → κ) (S : Finset I)
    (hinj : Set.InjOn key (S : Set I)) : S ≃ S.image key :=
  Equiv.ofBijective
    (fun a : S => (⟨key a, Finset.mem_image_of_mem key a.property⟩ : S.image key))
    ⟨by
      intro a b h
      apply Subtype.ext
      exact hinj a.property b.property (congrArg Subtype.val h),
    by
      intro b
      obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp b.property
      exact ⟨⟨a, ha⟩, Subtype.ext hab⟩⟩

/-- Rank the finite key image, then recover its selected label. No order on
the label type, or key injectivity outside S, is introduced. -/
noncomputable def rankEquiv (key : I → κ) (S : Finset I)
    (hinj : Set.InjOn key (S : Set I)) : Fin S.card ≃ S :=
  ((S.image key).orderIsoOfFin (Finset.card_image_of_injOn hinj)).toEquiv.trans
    (keyEquiv key S hinj).symm

theorem rankEquiv_key (key : I → κ) (S : Finset I)
    (hinj : Set.InjOn key (S : Set I)) (k : Fin S.card) :
    key (rankEquiv key S hinj k) =
      (S.image key).orderEmbOfFin (Finset.card_image_of_injOn hinj) k := by
  exact congrArg Subtype.val ((keyEquiv key S hinj).apply_symm_apply
    ((S.image key).orderIsoOfFin (Finset.card_image_of_injOn hinj) k))

theorem leftChild_key_image (key : I → κ) (S : Finset I)
    (hinj : Set.InjOn key (S : Set I)) (k : Fin S.card) :
    (leftChild (fun x y => decide (key x < key y)) S (rankEquiv key S hinj k)).image key =
      (Finset.Iio k).map
        ((S.image key).orderEmbOfFin (Finset.card_image_of_injOn hinj)).toEmbedding := by
  classical
  let K := S.image key
  let hc : K.card = S.card := Finset.card_image_of_injOn hinj
  let emb := K.orderEmbOfFin hc
  change _ = (Finset.Iio k).map emb.toEmbedding
  ext z
  constructor
  · intro hz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
    have hparts := (mem_leftChild (fun x y => decide (key x < key y))
      S (rankEquiv key S hinj k) b).mp hb
    let j := (K.orderIsoOfFin hc).symm ⟨key b, Finset.mem_image_of_mem key hparts.2.1⟩
    have hj : emb j = key b := congrArg Subtype.val
      ((K.orderIsoOfFin hc).apply_symm_apply
        ⟨key b, Finset.mem_image_of_mem key hparts.2.1⟩)
    have hkey : key (rankEquiv key S hinj k) = emb k := rankEquiv_key key S hinj k
    have hlt : key b < key (rankEquiv key S hinj k) := by simpa using hparts.2.2
    have hjk : j < k := emb.lt_iff_lt.mp (by rw [hj, ← hkey]; exact hlt)
    exact Finset.mem_map.mpr ⟨j, Finset.mem_Iio.mpr hjk, hj⟩
  · intro hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hz
    have hlt : key (rankEquiv key S hinj j) < key (rankEquiv key S hinj k) := by
      rw [rankEquiv_key, rankEquiv_key]
      exact emb.strictMono (Finset.mem_Iio.mp hj)
    have hne : (rankEquiv key S hinj j).val ≠ (rankEquiv key S hinj k).val := by
      intro h
      exact (ne_of_lt hlt) (congrArg key h)
    refine Finset.mem_image.mpr ⟨(rankEquiv key S hinj j).val, ?_,
      rankEquiv_key key S hinj j⟩
    exact (mem_leftChild _ _ _ _).mpr
      ⟨hne, (rankEquiv key S hinj j).property, by simpa using hlt⟩

theorem leftChild_card_rank (key : I → κ) (S : Finset I)
    (hinj : Set.InjOn key (S : Set I)) (k : Fin S.card) :
    (leftChild (fun x y => decide (key x < key y)) S (rankEquiv key S hinj k)).card =
      k.val := by
  rw [← Finset.card_image_of_injOn
    (injOn_leftChild key (fun x y => decide (key x < key y)) S hinj
      (rankEquiv key S hinj k)), leftChild_key_image, Finset.card_map, Fin.card_Iio]

theorem rightChild_card_rank (key : I → κ) (S : Finset I)
    (hinj : Set.InjOn key (S : Set I)) (k : Fin S.card) :
    (rightChild (fun x y => decide (key x < key y)) S (rankEquiv key S hinj k)).card =
      S.card - 1 - k.val := by
  have hsum := children_card (fun x y => decide (key x < key y)) S
    (rankEquiv key S hinj k) (rankEquiv key S hinj k).property
  rw [leftChild_card_rank] at hsum
  omega

/-- Reindex both child-size observations by the rank of the actual selected
pivot. Complementary ranks contribute a second copy of the same prefix sum. -/
theorem sum_child_cards (key : I → κ) (S : Finset I)
    (hinj : Set.InjOn key (S : Set I)) (f : Nat → ℝ) :
    (∑ a ∈ S, (f (leftChild (fun x y => decide (key x < key y)) S a).card +
      f (rightChild (fun x y => decide (key x < key y)) S a).card)) =
      2 * (∑ k ∈ Finset.range S.card, f k) := by
  classical
  calc
    _ = ∑ a : S, (f (leftChild (fun x y => decide (key x < key y)) S a).card +
        f (rightChild (fun x y => decide (key x < key y)) S a).card) :=
      (Finset.sum_coe_sort S _).symm
    _ = ∑ k : Fin S.card, (f k.val + f (S.card - 1 - k.val)) := by
      symm
      apply Fintype.sum_equiv (rankEquiv key S hinj)
      intro k
      rw [leftChild_card_rank, rightChild_card_rank]
    _ = 2 * (∑ k ∈ Finset.range S.card, f k) := by
      rw [Finset.sum_add_distrib, Fin.sum_univ_eq_sum_range,
        Fin.sum_univ_eq_sum_range, Finset.sum_range_reflect]
      ring

variable [MeasurableSpace (Equiv.Perm I)] [MeasurableSingletonClass (Equiv.Perm I)]

/-- Fixed-environment cardinal induction connects the actual integral to the
proved numerical expression. There is no assumed execution-mean recurrence. -/
theorem meanBy_eq_closedForm (positions : List I) (hnd : positions.Nodup)
    (hcomplete : ∀ b, b ∈ positions) (key : I → κ)
    (S : Finset I) (hinj : Set.InjOn key (S : Set I)) :
    meanBy positions (fun x y => decide (key x < key y)) S = QuickSortMean.closedForm S.card := by
  classical
  have all : ∀ n : Nat, ∀ T : Finset I, T.card = n → Set.InjOn key (T : Set I) →
      meanBy positions (fun x y => decide (key x < key y)) T = QuickSortMean.closedForm n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro T hcard hinjT
        by_cases hn : n = 0
        · subst n
          have hT : T = ∅ := Finset.card_eq_zero.mp hcard
          subst T
          rw [meanBy_empty positions hcomplete, QuickSortMean.closedForm_zero]
        · have hpos : 0 < n := Nat.pos_of_ne_zero hn
          have hT : T.Nonempty := Finset.card_pos.mp (by omega)
          have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
          have htoll : ((4 * (n - 1) + 3 : Nat) : ℝ) = 4 * (n : ℝ) - 1 := by
            have hp : n - 1 + 1 = n := by omega
            have hpR : ((n - 1 : Nat) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hp
            push_cast
            linarith
          calc
            meanBy positions (fun x y => decide (key x < key y)) T =
                (1 / (n : ℝ)) * ∑ a ∈ T,
                  (QuickSortMean.closedForm
                      (leftChild (fun x y => decide (key x < key y)) T a).card +
                    QuickSortMean.closedForm
                      (rightChild (fun x y => decide (key x < key y)) T a).card +
                        ((4 * (n - 1) + 3 : Nat) : ℝ)) := by
              rw [meanBy_recurrence positions hnd hcomplete _ T hT, ← hcard]
              congr 1
              apply Finset.sum_congr rfl
              intro a ha
              rw [ih _ (by rw [← hcard]; exact leftChild_card_lt _ T a ha) _ rfl
                  (injOn_leftChild key _ T hinjT a),
                ih _ (by rw [← hcard]; exact rightChild_card_lt _ T a ha) _ rfl
                  (injOn_rightChild key _ T hinjT a)]
            _ = (1 / (n : ℝ)) *
                (2 * (∑ k ∈ Finset.range n, QuickSortMean.closedForm k) +
                  (n : ℝ) * ((4 * (n - 1) + 3 : Nat) : ℝ)) := by
              rw [Finset.sum_add_distrib, sum_child_cards key T hinjT,
                Finset.sum_const, nsmul_eq_mul, hcard]
            _ = (2 / (n : ℝ)) * (∑ k ∈ Finset.range n, QuickSortMean.closedForm k) +
                4 * (n : ℝ) - 1 := by
              rw [htoll]
              field_simp [hnR] <;> ring
            _ = QuickSortMean.closedForm n := (QuickSortMean.closedForm_recurrence n hpos).symm
  exact all S.card S rfl hinj

theorem meanBy_nonneg (positions : List I) (hnd : positions.Nodup)
    (hcomplete : ∀ b, b ∈ positions) (key : I → κ)
    (S : Finset I) (hinj : Set.InjOn key (S : Set I)) :
    0 ≤ meanBy positions (fun x y => decide (key x < key y)) S := by
  rw [meanBy_eq_closedForm positions hnd hcomplete key S hinj]
  exact QuickSortMean.closedForm_nonneg S.card

theorem meanBy_le_nlogb (positions : List I) (hnd : positions.Nodup)
    (hcomplete : ∀ b, b ∈ positions) (key : I → κ)
    (S : Finset I) (hinj : Set.InjOn key (S : Set I)) (hn : 2 ≤ S.card) :
    meanBy positions (fun x y => decide (key x < key y)) S ≤
      32 * ((S.card : ℝ) * Real.logb 2 (S.card : ℝ)) := by
  rw [meanBy_eq_closedForm positions hnd hcomplete key S hinj]
  exact QuickSortMean.closedForm_le_nlogb S.card hn

end Keys

end Labels

section Occurrences

/-- Uniformly order occurrence indices, then read the same input payloads.
The lookup may identify equal payloads; it retains every occurrence. -/
def occurrenceInput (xs : List α) (π : Equiv.Perm (Fin xs.length)) : List α :=
  (restrictedOrder (List.finRange xs.length) Finset.univ π).map xs.get

theorem occurrenceInput_perm (xs : List α) (π : Equiv.Perm (Fin xs.length)) :
    (occurrenceInput xs π).Perm xs := by
  have hmap : (List.finRange xs.length).map xs.get = xs :=
    (List.ofFn_eq_map (f := xs.get)).symm.trans (List.ofFn_get xs)
  have h := (restrictedOrder_perm (List.finRange xs.length) (List.nodup_finRange _)
    (fun i => by simp) Finset.univ π).map xs.get
  simpa only [Finset.mem_univ, decide_true, List.filter_true, hmap] using h

theorem occurrenceInput_length (xs : List α) (π : Equiv.Perm (Fin xs.length)) :
    (occurrenceInput xs π).length = xs.length := (occurrenceInput_perm xs π).length_eq

/-- This is equality of existing observations, without charging the map or lookup. -/
theorem occurrenceInput_cost (lt : α → α → Bool) (xs : List α)
    (π : Equiv.Perm (Fin xs.length)) :
    QuickSort.exerciseCost lt (occurrenceInput xs π) =
      QuickSort.exerciseCost (fun i j => lt (xs.get i) (xs.get j))
        (restrictedOrder (List.finRange xs.length) Finset.univ π) :=
  QuickSort.exerciseCost_map xs.get lt _

local instance occurrenceMeasurableSpace (n : Nat) :
    MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

local instance occurrenceMeasurableSingletons (n : Nat) :
    MeasurableSingletonClass (Equiv.Perm (Fin n)) := ⟨fun _ => trivial⟩

/-- Actual payload execution, sampled on its finite occurrence environment. -/
noncomputable def inputMeanBy (lt : α → α → Bool) (xs : List α) : ℝ :=
  ∫ π, (QuickSort.exerciseCost lt (occurrenceInput xs π) : ℝ)
    ∂uniformOn (Set.univ : Set (Equiv.Perm (Fin xs.length)))

theorem integrable_inputCost (lt : α → α → Bool) (xs : List α) :
    Integrable (fun π => (QuickSort.exerciseCost lt (occurrenceInput xs π) : ℝ))
      (uniformOn (Set.univ : Set (Equiv.Perm (Fin xs.length)))) := Integrable.of_finite

theorem inputMeanBy_eq_meanBy (lt : α → α → Bool) (xs : List α) :
    inputMeanBy lt xs = meanBy (List.finRange xs.length)
      (fun i j => lt (xs.get i) (xs.get j)) Finset.univ := by
  unfold inputMeanBy meanBy observedCost
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun π => by rw [occurrenceInput_cost])

@[simp] theorem inputMeanBy_nil (lt : α → α → Bool) : inputMeanBy lt [] = 1 := by
  simp [inputMeanBy, occurrenceInput, restrictedOrder]

@[simp] theorem inputMeanBy_singleton (lt : α → α → Bool) (x : α) :
    inputMeanBy lt [x] = 5 := by
  have hx : ∀ π : Equiv.Perm (Fin [x].length), occurrenceInput [x] π = [x] :=
    fun π => List.perm_singleton.mp (occurrenceInput_perm [x] π)
  simp [inputMeanBy, hx]

variable [LinearOrder κ]

noncomputable def inputMean (key : α → κ) (xs : List α) : ℝ :=
  inputMeanBy (fun a b => decide (key a < key b)) xs

/-- Distinct input keys give an injective key map on occurrence labels, with
independent payload and key universes and no payload equality instance. -/
theorem occurrence_key_injective (key : α → κ) (xs : List α)
    (hkeys : (xs.map key).Nodup) : Function.Injective (fun i : Fin xs.length => key (xs.get i)) := by
  apply List.nodup_ofFn.mp
  rw [List.ofFn_comp', List.ofFn_get]
  exact hkeys

theorem occurrenceInput_keys_nodup (key : α → κ) (xs : List α)
    (hkeys : (xs.map key).Nodup) (π : Equiv.Perm (Fin xs.length)) :
    ((occurrenceInput xs π).map key).Nodup :=
  ((occurrenceInput_perm xs π).map key).nodup_iff.mpr hkeys

/-- The book's exact exercise-cost mean for arbitrary distinct-key payloads. -/
theorem inputMean_eq_closedForm (key : α → κ) (xs : List α)
    (hkeys : (xs.map key).Nodup) : inputMean key xs = QuickSortMean.closedForm xs.length := by
  unfold inputMean
  rw [inputMeanBy_eq_meanBy]
  have hinj : Set.InjOn (fun i : Fin xs.length => key (xs.get i))
      (Finset.univ : Set (Fin xs.length)) :=
    (occurrence_key_injective key xs hkeys).injOn
  simpa only [Finset.card_univ, Fintype.card_fin] using
    meanBy_eq_closedForm (List.finRange xs.length) (List.nodup_finRange _)
      (fun i => by simp) (fun i => key (xs.get i)) Finset.univ hinj

@[simp] theorem inputMean_nil (key : α → κ) : inputMean key [] = 1 := inputMeanBy_nil _

@[simp] theorem inputMean_singleton (key : α → κ) (x : α) :
    inputMean key [x] = 5 := inputMeanBy_singleton _ x

/-- The all-equal-key boundary is quadratic for every sampled order, even when
payload records are distinct. This theorem does not assume distinct keys. -/
theorem inputMean_of_equal_keys (key : α → κ) (xs : List α) (k : κ)
    (hall : ∀ x ∈ xs, key x = k) :
    inputMean key xs = ((2 * xs.length ^ 2 + 2 * xs.length + 1 : Nat) : ℝ) := by
  unfold inputMean
  rw [inputMeanBy_eq_meanBy]
  have hfalse : ∀ i ∈ (Finset.univ : Finset (Fin xs.length)),
      ∀ j ∈ (Finset.univ : Finset (Fin xs.length)),
        decide (key (xs.get j) < key (xs.get i)) = false := by
    intro i _ j _
    rw [hall (xs.get j) (List.getElem_mem j.isLt),
      hall (xs.get i) (List.getElem_mem i.isLt)]
    simp
  simpa only [Finset.card_univ, Fintype.card_fin] using
    meanBy_of_all_false (List.finRange xs.length) (List.nodup_finRange _)
      (fun i => by simp) (fun i j => decide (key (xs.get i) < key (xs.get j)))
        Finset.univ hfalse

theorem inputMean_nonneg (key : α → κ) (xs : List α) (hkeys : (xs.map key).Nodup) :
    0 ≤ inputMean key xs := by
  rw [inputMean_eq_closedForm key xs hkeys]
  exact QuickSortMean.closedForm_nonneg xs.length

theorem inputMean_le_log (key : α → κ) (xs : List α)
    (hkeys : (xs.map key).Nodup) (hn : 1 ≤ xs.length) :
    inputMean key xs ≤ 16 * (xs.length : ℝ) * (1 + Real.log (xs.length : ℝ)) := by
  rw [inputMean_eq_closedForm key xs hkeys]
  exact QuickSortMean.closedForm_le_log xs.length hn

theorem inputMean_le_nlogb (key : α → κ) (xs : List α)
    (hkeys : (xs.map key).Nodup) (hn : 2 ≤ xs.length) :
    inputMean key xs ≤ 32 * ((xs.length : ℝ) * Real.logb 2 (xs.length : ℝ)) := by
  rw [inputMean_eq_closedForm key xs hkeys]
  exact QuickSortMean.closedForm_le_nlogb xs.length hn

/-- The environment varies with the actual input length. This is an unbounded
Nat-indexed family, rather than an eventual assertion inside one fixed I. -/
theorem inputMean_family_isBigO (key : α → κ) (family : Nat → List α)
    (hlength : ∀ n, (family n).length = n) (hkeys : ∀ n, ((family n).map key).Nodup) :
    Asymptotics.IsBigO Filter.atTop (fun n : Nat => inputMean key (family n))
      (fun n : Nat => (n : ℝ) * Real.logb 2 (n : ℝ)) := by
  have heq : (fun n : Nat => inputMean key (family n)) = QuickSortMean.closedForm := by
    funext n
    rw [inputMean_eq_closedForm key (family n) (hkeys n), hlength n]
  rw [heq]
  exact QuickSortMean.closedForm_isBigO_logb

/-- The append-inclusive observation has an inequality transport, not the same
exact harmonic formula. It uses the very same occurrence samples. -/
noncomputable def inputLiteralMean (key : α → κ) (xs : List α) : ℝ :=
  ∫ π, (QuickSort.literalCost (fun a b => decide (key a < key b)) (occurrenceInput xs π) : ℝ)
    ∂uniformOn (Set.univ : Set (Equiv.Perm (Fin xs.length)))

theorem inputLiteralMean_bounds (key : α → κ) (xs : List α) :
    inputMean key xs ≤ inputLiteralMean key xs ∧
      inputLiteralMean key xs ≤ 2 * inputMean key xs := by
  have hT := integrable_inputCost (fun a b => decide (key a < key b)) xs
  have hF : Integrable
      (fun π => (QuickSort.literalCost (fun a b => decide (key a < key b))
        (occurrenceInput xs π) : ℝ))
      (uniformOn (Set.univ : Set (Equiv.Perm (Fin xs.length)))) := Integrable.of_finite
  constructor
  · apply integral_mono hT hF
    intro π
    exact_mod_cast QuickSort.exerciseCost_le_literalCost
      (fun a b => decide (key a < key b)) (occurrenceInput xs π)
  · unfold inputLiteralMean inputMean inputMeanBy
    rw [← integral_const_mul]
    apply integral_mono hF (hT.const_mul 2)
    intro π
    exact_mod_cast QuickSort.literalCost_le_twice
      (fun a b => decide (key a < key b)) (occurrenceInput xs π)

theorem inputLiteralMean_le_nlogb (key : α → κ) (xs : List α)
    (hkeys : (xs.map key).Nodup) (hn : 2 ≤ xs.length) :
    inputLiteralMean key xs ≤ 64 * ((xs.length : ℝ) * Real.logb 2 (xs.length : ℝ)) := by
  have hb := (inputLiteralMean_bounds key xs).2
  have ht := inputMean_le_nlogb key xs hkeys hn
  linarith

end Occurrences

end Resources.UniformQuickSortMean

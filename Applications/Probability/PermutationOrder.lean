import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Permutation
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.List
import Mathlib.Probability.HasLaw
import Mathlib.Probability.UniformOn

/-!
# Relative orders induced on fixed subsets

The list `positions` gives a chosen order of priority labels. A permutation
maps keys to their assigned labels, so its inverse maps this label list to
the ordered keys. Filtering that list observes the relative order of one
fixed subset. The observation is an ordinary list operation and uses the
same sampled permutation for every subset.

The value laws retain membership, distinctness, ordering and composition
of restrictions. Completeness of the label list supplies finite enumeration
locally in the probability proofs. No public finite-type enumeration, index
order, inhabited index type or index measurable space is required.

For a complete label list with no duplicates, every whole output order has
reciprocal-factorial mass under the uniform global permutation. The source
fiber formula needs measurable structure only on that permutation space.
Its pushforward corollary uses the caller's measurable structure on lists.
For two fixed disjoint subsets, the actual pair of restrictions has the
product of those uniform laws. Pair filtering transports this conclusion
from any observation with the specified whole-order law, under its current
environment measure. The subsets need not cover the population and may be
empty. These results do not assert a law after an arbitrary history.
Matching this label order to numeric priorities and algorithmic work remains
a separate source correspondence.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Applications.Probability.PermutationOrder

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

universe u

variable {I : Type u} [DecidableEq I]

/-- Read the keys in label order, then retain exactly those in the subset. -/
def restrictedOrder (positions : List I) (S : Finset I) (π : Equiv.Perm I) : List I :=
  (positions.map π.symm).filter (fun a => decide (a ∈ S))

/-- The existing finite set of permutations of the subset's base list. -/
def orders (positions : List I) (S : Finset I) : Finset (List I) :=
  (positions.filter (fun a => decide (a ∈ S))).permutations.toFinset

/-- Without completeness, an included key must have its assigned label listed. -/
@[simp] theorem mem_restrictedOrder (positions : List I) (S : Finset I)
    (π : Equiv.Perm I) (a : I) :
    a ∈ restrictedOrder positions S π ↔ π a ∈ positions ∧ a ∈ S := by
  simp [restrictedOrder, List.mem_map, Equiv.symm_apply_eq]

theorem mem_restrictedOrder_of_complete (positions : List I)
    (hcomplete : ∀ a, a ∈ positions) (S : Finset I) (π : Equiv.Perm I) (a : I) :
    a ∈ restrictedOrder positions S π ↔ a ∈ S := by
  simp only [mem_restrictedOrder, hcomplete, true_and]

theorem restrictedOrder_nodup (positions : List I) (hnd : positions.Nodup)
    (S : Finset I) (π : Equiv.Perm I) :
    (restrictedOrder positions S π).Nodup := by
  unfold restrictedOrder
  exact (hnd.map π.symm.injective).filter _

theorem restrictedOrder_toFinset (positions : List I)
    (hcomplete : ∀ a, a ∈ positions) (S : Finset I) (π : Equiv.Perm I) :
    (restrictedOrder positions S π).toFinset = S := by
  apply Finset.ext
  intro a
  simp only [List.mem_toFinset,
    mem_restrictedOrder_of_complete positions hcomplete S π a]

theorem restrictedOrder_length (positions : List I) (hnd : positions.Nodup)
    (hcomplete : ∀ a, a ∈ positions) (S : Finset I) (π : Equiv.Perm I) :
    (restrictedOrder positions S π).length = S.card := by
  rw [← List.toFinset_card_of_nodup (restrictedOrder_nodup positions hnd S π),
    restrictedOrder_toFinset positions hcomplete S π]

theorem restrictedOrder_perm (positions : List I) (hnd : positions.Nodup)
    (hcomplete : ∀ a, a ∈ positions) (S : Finset I) (π : Equiv.Perm I) :
    (restrictedOrder positions S π).Perm
      (positions.filter (fun a => decide (a ∈ S))) := by
  apply (List.perm_ext_iff_of_nodup
    (restrictedOrder_nodup positions hnd S π) (hnd.filter _)).mpr
  intro a
  rw [mem_restrictedOrder_of_complete positions hcomplete S π a]
  simp [hcomplete a]

/-- Mapping the observed keys back to labels preserves their positions' order. -/
theorem map_restrictedOrder_sublist (positions : List I) (S : Finset I)
    (π : Equiv.Perm I) :
    (restrictedOrder positions S π).map π <+ positions := by
  have h := List.Sublist.map π
    (List.filter_sublist (p := fun a => decide (a ∈ S))
      (l := positions.map π.symm))
  simpa [restrictedOrder, List.map_map, Function.comp_def] using h

/-- Restricting twice retains the intersection, in the same sampled order. -/
theorem filter_restrictedOrder (positions : List I) (S T : Finset I)
    (π : Equiv.Perm I) :
    (restrictedOrder positions S π).filter (fun a => decide (a ∈ T)) =
      restrictedOrder positions (S ∩ T) π := by
  unfold restrictedOrder
  rw [List.filter_filter]
  apply List.filter_congr
  intro a _
  by_cases hS : a ∈ S <;> by_cases hT : a ∈ T <;> simp [hS, hT]

theorem filter_restrictedOrder_of_subset (positions : List I) (S T : Finset I)
    (π : Equiv.Perm I) (hTS : T ⊆ S) :
    (restrictedOrder positions S π).filter (fun a => decide (a ∈ T)) =
      restrictedOrder positions T π := by
  rw [filter_restrictedOrder, Finset.inter_eq_right.mpr hTS]

@[simp] theorem mem_orders (positions : List I) (S : Finset I) (xs : List I) :
    xs ∈ orders positions S ↔
      xs.Perm (positions.filter (fun a => decide (a ∈ S))) := by
  simp [orders, List.mem_permutations]

/-- Even the empty base list has its one empty permutation. -/
theorem orders_nonempty (positions : List I) (S : Finset I) :
    (orders positions S).Nonempty := by
  refine ⟨positions.filter (fun a => decide (a ∈ S)), ?_⟩
  exact (mem_orders positions S _).2 (List.Perm.refl _)

theorem restrictedOrder_mem_orders (positions : List I) (hnd : positions.Nodup)
    (hcomplete : ∀ a, a ∈ positions) (S : Finset I) (π : Equiv.Perm I) :
    restrictedOrder positions S π ∈ orders positions S :=
  (mem_orders positions S _).2 (restrictedOrder_perm positions hnd hcomplete S π)

theorem orders_card (positions : List I) (hnd : positions.Nodup)
    (hcomplete : ∀ a, a ∈ positions) (S : Finset I) :
    (orders positions S).card = Nat.factorial S.card := by
  let base := positions.filter (fun a => decide (a ∈ S))
  have hbase : base.Nodup := hnd.filter _
  have hlength : base.length = S.card := by
    simpa [base, restrictedOrder] using
      restrictedOrder_length positions hnd hcomplete S (Equiv.refl I)
  change base.permutations.toFinset.card = Nat.factorial S.card
  rw [List.toFinset_card_of_nodup (List.nodup_permutations base hbase),
    List.length_permutations, hlength]

private theorem exists_map_eq_of_nodup (xs ys : List I)
    (hxs : xs.Nodup) (hys : ys.Nodup) (hlength : xs.length = ys.length) :
    ∃ σ : Equiv.Perm I, xs.map σ = ys := by
  let g : Fin xs.length → I := fun i => ys.get ⟨i.val, hlength ▸ i.isLt⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply Fin.ext
    exact congrArg Fin.val (hys.injective_get hij)
  obtain ⟨σ, hσ⟩ :=
    Equiv.Perm.exists_extending_pair xs.get g hxs.injective_get hg
  refine ⟨σ, List.ext_getElem (by simpa only [List.length_map] using hlength) ?_⟩
  intro n hnmap _hnys
  rw [List.getElem_map]
  exact hσ ⟨n, by simpa only [List.length_map] using hnmap⟩

private theorem exists_relabel_orders (positions : List I) (hnd : positions.Nodup)
    (hcomplete : ∀ a, a ∈ positions) (S : Finset I) (xs ys : List I)
    (hxs : xs ∈ orders positions S) (hys : ys ∈ orders positions S) :
    ∃ σ : Equiv.Perm I, xs.map σ = ys ∧ ∀ a, σ a ∈ S ↔ a ∈ S := by
  have hxsPerm := (mem_orders positions S xs).1 hxs
  have hysPerm := (mem_orders positions S ys).1 hys
  have hbase : (positions.filter (fun a => decide (a ∈ S))).Nodup := hnd.filter _
  have hxsMem (a : I) : a ∈ xs ↔ a ∈ S :=
    hxsPerm.mem_iff.trans (by simp [hcomplete a])
  have hysMem (a : I) : a ∈ ys ↔ a ∈ S :=
    hysPerm.mem_iff.trans (by simp [hcomplete a])
  obtain ⟨σ, hmap⟩ := exists_map_eq_of_nodup xs ys
    (hxsPerm.nodup_iff.mpr hbase) (hysPerm.nodup_iff.mpr hbase)
    (hxsPerm.length_eq.trans hysPerm.length_eq.symm)
  refine ⟨σ, hmap, ?_⟩
  intro a
  have hmem : σ a ∈ ys ↔ a ∈ xs := by
    rw [← hmap, List.mem_map_of_injective σ.injective]
  exact (hysMem (σ a)).symm.trans (hmem.trans (hxsMem a))

private theorem restrictedOrder_relabel (positions : List I) (S : Finset I)
    (π σ : Equiv.Perm I) (hS : ∀ a, σ a ∈ S ↔ a ∈ S) :
    restrictedOrder positions S (π * σ.symm) =
      (restrictedOrder positions S π).map σ := by
  have hglobal : positions.map (π * σ.symm).symm =
      (positions.map π.symm).map σ := by
    simp only [List.map_map]
  unfold restrictedOrder
  rw [hglobal, List.filter_map]
  apply congrArg (List.map σ)
  apply List.filter_congr
  intro a _
  simp only [Function.comp_apply, hS a]

private theorem fiber_mass_eq
    [MeasurableSpace (Equiv.Perm I)] [MeasurableSingletonClass (Equiv.Perm I)]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ a, a ∈ positions)
    (S : Finset I) (xs ys : List I)
    (hxs : xs ∈ orders positions S) (hys : ys ∈ orders positions S) :
    uniformOn Set.univ {π | restrictedOrder positions S π = xs} =
      uniformOn Set.univ {π | restrictedOrder positions S π = ys} := by
  classical
  letI := Fintype.ofList positions hcomplete
  obtain ⟨σ, hmap, hS⟩ := exists_relabel_orders positions hnd hcomplete S xs ys hxs hys
  have hpre : (fun π : Equiv.Perm I => π * σ.symm) ⁻¹'
      {π | restrictedOrder positions S π = ys} =
      {π | restrictedOrder positions S π = xs} := by
    apply Set.ext
    intro π
    change restrictedOrder positions S (π * σ.symm) = ys ↔
      restrictedOrder positions S π = xs
    rw [restrictedOrder_relabel positions S π σ hS, ← hmap]
    exact (List.map_injective_iff.mpr σ.injective).eq_iff
  have hcard : ({π : Equiv.Perm I | restrictedOrder positions S π = xs}).encard =
      ({π : Equiv.Perm I | restrictedOrder positions S π = ys}).encard := by
    rw [← hpre]
    exact Set.encard_preimage_of_bijective (Group.mulRight_bijective σ.symm) _
  have hmeasx : MeasurableSet {π : Equiv.Perm I | restrictedOrder positions S π = xs} :=
    (Set.toFinite _).measurableSet
  have hmeasy : MeasurableSet {π : Equiv.Perm I | restrictedOrder positions S π = ys} :=
    (Set.toFinite _).measurableSet
  rw [uniformOn_univ, uniformOn_univ, Measure.count_apply hmeasx,
    Measure.count_apply hmeasy, hcard]

/-- Every supported whole order has reciprocal-factorial mass under the
actual global uniform law; every unsupported list has mass zero. -/
theorem uniformOn_restrictedOrder_eq
    [MeasurableSpace (Equiv.Perm I)] [MeasurableSingletonClass (Equiv.Perm I)]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ a, a ∈ positions)
    (S : Finset I) (xs : List I) :
    uniformOn (Set.univ : Set (Equiv.Perm I))
        {π | restrictedOrder positions S π = xs} =
      if xs ∈ orders positions S
      then (Nat.factorial S.card : ℝ≥0∞)⁻¹
      else 0 := by
  classical
  letI := Fintype.ofList positions hcomplete
  by_cases hxs : xs ∈ orders positions S
  · rw [if_pos hxs]
    have hpre : (restrictedOrder positions S) ⁻¹'
        (orders positions S : Set (List I)) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro π
      exact restrictedOrder_mem_orders positions hnd hcomplete S π
    have hpartition := sum_measure_preimage_singleton
      (μ := uniformOn (Set.univ : Set (Equiv.Perm I)))
      (f := restrictedOrder positions S) (orders positions S)
      (fun ys _ => (Set.toFinite _).measurableSet)
    rw [hpre, measure_univ] at hpartition
    change (∑ ys ∈ orders positions S,
      uniformOn Set.univ {π | restrictedOrder positions S π = ys}) = 1 at hpartition
    have hsum :
        (∑ ys ∈ orders positions S,
          uniformOn Set.univ {π | restrictedOrder positions S π = ys}) =
        ((orders positions S).card : ℝ≥0∞) *
          uniformOn Set.univ {π | restrictedOrder positions S π = xs} := by
      calc
        _ = ∑ _ys ∈ orders positions S,
            uniformOn Set.univ {π | restrictedOrder positions S π = xs} := by
          apply Finset.sum_congr rfl
          intro ys hys
          exact fiber_mass_eq positions hnd hcomplete S ys xs hys hxs
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hmass : uniformOn Set.univ {π | restrictedOrder positions S π = xs} =
        ((orders positions S).card : ℝ≥0∞)⁻¹ := by
      apply ENNReal.eq_inv_of_mul_eq_one_left
      calc
        uniformOn Set.univ {π | restrictedOrder positions S π = xs} *
            ((orders positions S).card : ℝ≥0∞) =
            ((orders positions S).card : ℝ≥0∞) *
              uniformOn Set.univ {π | restrictedOrder positions S π = xs} := mul_comm _ _
        _ = ∑ ys ∈ orders positions S,
            uniformOn Set.univ {π | restrictedOrder positions S π = ys} := hsum.symm
        _ = 1 := hpartition
    simpa only [orders_card positions hnd hcomplete S] using hmass
  · rw [if_neg hxs]
    have hempty : ({π : Equiv.Perm I | restrictedOrder positions S π = xs}) = ∅ := by
      apply Set.ext
      intro π
      change (restrictedOrder positions S π = xs) ↔ False
      constructor
      · intro hπ
        exact hxs (hπ ▸ restrictedOrder_mem_orders positions hnd hcomplete S π)
      · exact False.elim
    rw [hempty]
    exact measure_empty

/-- The actual restriction map has the existing uniform law on whole target
orders. Output measurability is separate from the source-fiber formula. -/
theorem map_restrictedOrder_uniformOn
    [MeasurableSpace (Equiv.Perm I)] [MeasurableSingletonClass (Equiv.Perm I)]
    [MeasurableSpace (List I)] [MeasurableSingletonClass (List I)]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ a, a ∈ positions)
    (S : Finset I) :
    (uniformOn (Set.univ : Set (Equiv.Perm I))).map (restrictedOrder positions S) =
      uniformOn (orders positions S : Set (List I)) := by
  classical
  letI := Fintype.ofList positions hcomplete
  apply Measure.ext_of_singleton
  intro xs
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton xs)]
  change uniformOn Set.univ {π | restrictedOrder positions S π = xs} =
    uniformOn (orders positions S : Set (List I)) {xs}
  have htarget : uniformOn (orders positions S : Set (List I)) {xs} =
      (((orders positions S) ∩ {xs}).card : ℝ≥0∞) /
        ((orders positions S).card : ℝ≥0∞) := by
    simpa only [Finset.coe_singleton] using
      (uniformOn_apply_finset (s := orders positions S) (t := ({xs} : Finset (List I))))
  rw [uniformOn_restrictedOrder_eq positions hnd hcomplete S xs, htarget]
  by_cases hxs : xs ∈ orders positions S
  · simp [hxs, orders_card positions hnd hcomplete S, one_div]
  · simp [hxs]

private theorem exists_relabel_order_pair (positions : List I)
    (hnd : positions.Nodup) (hcomplete : ∀ a, a ∈ positions)
    (A B : Finset I) (hAB : Disjoint A B)
    (xs ys xs' ys' : List I)
    (hxs : xs ∈ orders positions A) (hys : ys ∈ orders positions B)
    (hxs' : xs' ∈ orders positions A) (hys' : ys' ∈ orders positions B) :
    ∃ σ : Equiv.Perm I,
      xs.map σ = xs' ∧ ys.map σ = ys' ∧
        (∀ a, σ a ∈ A ↔ a ∈ A) ∧ (∀ a, σ a ∈ B ↔ a ∈ B) := by
  have hmem (T : Finset I) (zs : List I) (hzs : zs ∈ orders positions T) (a : I) :
      a ∈ zs ↔ a ∈ T :=
    ((mem_orders positions T zs).1 hzs).mem_iff.trans (by simp [hcomplete a])
  have hxsPerm := (mem_orders positions A xs).1 hxs
  have hysPerm := (mem_orders positions B ys).1 hys
  have hxs'Perm := (mem_orders positions A xs').1 hxs'
  have hys'Perm := (mem_orders positions B ys').1 hys'
  have hlengthA : xs.length = xs'.length :=
    hxsPerm.length_eq.trans hxs'Perm.length_eq.symm
  have hlengthB : ys.length = ys'.length :=
    hysPerm.length_eq.trans hys'Perm.length_eq.symm
  have hdisjoint : List.Disjoint xs ys := by
    apply List.disjoint_left.mpr
    intro a hax hay
    exact Finset.disjoint_left.mp hAB
      ((hmem A xs hxs a).mp hax) ((hmem B ys hys a).mp hay)
  have hdisjoint' : List.Disjoint xs' ys' := by
    apply List.disjoint_left.mpr
    intro a hax hay
    exact Finset.disjoint_left.mp hAB
      ((hmem A xs' hxs' a).mp hax) ((hmem B ys' hys' a).mp hay)
  obtain ⟨σ, hmap⟩ := exists_map_eq_of_nodup (xs ++ ys) (xs' ++ ys')
    ((hxsPerm.nodup_iff.mpr (hnd.filter _)).append
      (hysPerm.nodup_iff.mpr (hnd.filter _)) hdisjoint)
    ((hxs'Perm.nodup_iff.mpr (hnd.filter _)).append
      (hys'Perm.nodup_iff.mpr (hnd.filter _)) hdisjoint')
    (by simp only [List.length_append, hlengthA, hlengthB])
  rw [List.map_append] at hmap
  obtain ⟨hmapA, hmapB⟩ := List.append_inj hmap
    (by simpa only [List.length_map] using hlengthA)
  refine ⟨σ, hmapA, hmapB, ?_, ?_⟩
  · intro a
    have hmemMap : σ a ∈ xs' ↔ a ∈ xs := by
      rw [← hmapA, List.mem_map_of_injective σ.injective]
    exact (hmem A xs' hxs' (σ a)).symm.trans (hmemMap.trans (hmem A xs hxs a))
  · intro a
    have hmemMap : σ a ∈ ys' ↔ a ∈ ys := by
      rw [← hmapB, List.mem_map_of_injective σ.injective]
    exact (hmem B ys' hys' (σ a)).symm.trans (hmemMap.trans (hmem B ys hys a))

private theorem pair_fiber_mass_eq
    [MeasurableSpace (Equiv.Perm I)] [MeasurableSingletonClass (Equiv.Perm I)]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ a, a ∈ positions)
    (A B : Finset I) (hAB : Disjoint A B) (p q : List I × List I)
    (hp : p ∈ (orders positions A).product (orders positions B))
    (hq : q ∈ (orders positions A).product (orders positions B)) :
    uniformOn Set.univ
        {π | (restrictedOrder positions A π, restrictedOrder positions B π) = p} =
      uniformOn Set.univ
        {π | (restrictedOrder positions A π, restrictedOrder positions B π) = q} := by
  classical
  letI := Fintype.ofList positions hcomplete
  obtain ⟨σ, hmapA, hmapB, hA, hB⟩ :=
    exists_relabel_order_pair positions hnd hcomplete A B hAB p.1 p.2 q.1 q.2
      (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2
      (Finset.mem_product.mp hq).1 (Finset.mem_product.mp hq).2
  have hpre : (fun π : Equiv.Perm I => π * σ.symm) ⁻¹'
      {π | (restrictedOrder positions A π, restrictedOrder positions B π) = q} =
      {π | (restrictedOrder positions A π, restrictedOrder positions B π) = p} := by
    apply Set.ext
    intro π
    change (restrictedOrder positions A (π * σ.symm),
      restrictedOrder positions B (π * σ.symm)) = q ↔
        (restrictedOrder positions A π, restrictedOrder positions B π) = p
    rw [Prod.ext_iff, Prod.ext_iff]
    change (restrictedOrder positions A (π * σ.symm) = q.1 ∧
      restrictedOrder positions B (π * σ.symm) = q.2) ↔
        (restrictedOrder positions A π = p.1 ∧ restrictedOrder positions B π = p.2)
    rw [restrictedOrder_relabel positions A π σ hA,
      restrictedOrder_relabel positions B π σ hB, ← hmapA, ← hmapB]
    exact and_congr (List.map_injective_iff.mpr σ.injective).eq_iff
      (List.map_injective_iff.mpr σ.injective).eq_iff
  have hcard :
      ({π : Equiv.Perm I |
        (restrictedOrder positions A π, restrictedOrder positions B π) = p}).encard =
      ({π : Equiv.Perm I |
        (restrictedOrder positions A π, restrictedOrder positions B π) = q}).encard := by
    rw [← hpre]
    exact Set.encard_preimage_of_bijective (Group.mulRight_bijective σ.symm) _
  have hmeasp : MeasurableSet
      {π : Equiv.Perm I |
        (restrictedOrder positions A π, restrictedOrder positions B π) = p} :=
    (Set.toFinite _).measurableSet
  have hmeasq : MeasurableSet
      {π : Equiv.Perm I |
        (restrictedOrder positions A π, restrictedOrder positions B π) = q} :=
    (Set.toFinite _).measurableSet
  rw [uniformOn_univ, uniformOn_univ, Measure.count_apply hmeasp,
    Measure.count_apply hmeasq, hcard]

/-- Two fixed disjoint restrictions of the same global permutation have
reciprocal-factorial-product mass at every supported pair, and zero otherwise. -/
theorem uniformOn_restrictedOrder_pair_eq
    [MeasurableSpace (Equiv.Perm I)] [MeasurableSingletonClass (Equiv.Perm I)]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ a, a ∈ positions)
    (A B : Finset I) (hAB : Disjoint A B) (xs ys : List I) :
    uniformOn (Set.univ : Set (Equiv.Perm I))
        {π | (restrictedOrder positions A π, restrictedOrder positions B π) = (xs, ys)} =
      if xs ∈ orders positions A ∧ ys ∈ orders positions B then
        ((Nat.factorial A.card * Nat.factorial B.card : ℕ) : ℝ≥0∞)⁻¹
      else 0 := by
  classical
  letI := Fintype.ofList positions hcomplete
  let C := (orders positions A).product (orders positions B)
  let observation : Equiv.Perm I → List I × List I :=
    fun π => (restrictedOrder positions A π, restrictedOrder positions B π)
  by_cases hxy : xs ∈ orders positions A ∧ ys ∈ orders positions B
  · rw [if_pos hxy]
    have hxyC : (xs, ys) ∈ C := Finset.mem_product.mpr hxy
    have hpre : observation ⁻¹' (C : Set (List I × List I)) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro π
      exact Finset.mem_product.mpr
        ⟨restrictedOrder_mem_orders positions hnd hcomplete A π,
          restrictedOrder_mem_orders positions hnd hcomplete B π⟩
    have hpartition := sum_measure_preimage_singleton
      (μ := uniformOn (Set.univ : Set (Equiv.Perm I)))
      (f := observation) C (fun p _ => (Set.toFinite _).measurableSet)
    rw [hpre, measure_univ] at hpartition
    change (∑ p ∈ C, uniformOn Set.univ {π | observation π = p}) = 1 at hpartition
    have hsum : (∑ p ∈ C, uniformOn Set.univ {π | observation π = p}) =
        (C.card : ℝ≥0∞) * uniformOn Set.univ {π | observation π = (xs, ys)} := by
      calc
        _ = ∑ _p ∈ C, uniformOn Set.univ {π | observation π = (xs, ys)} := by
          apply Finset.sum_congr rfl
          intro p hp
          exact pair_fiber_mass_eq positions hnd hcomplete A B hAB p (xs, ys) hp hxyC
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hmass : uniformOn Set.univ {π | observation π = (xs, ys)} =
        (C.card : ℝ≥0∞)⁻¹ := by
      apply ENNReal.eq_inv_of_mul_eq_one_left
      calc
        uniformOn Set.univ {π | observation π = (xs, ys)} * (C.card : ℝ≥0∞) =
            (C.card : ℝ≥0∞) * uniformOn Set.univ {π | observation π = (xs, ys)} :=
          mul_comm _ _
        _ = ∑ p ∈ C, uniformOn Set.univ {π | observation π = p} := hsum.symm
        _ = 1 := hpartition
    have hC : C.card = Nat.factorial A.card * Nat.factorial B.card := by
      dsimp only [C]
      rw [Finset.card_product, orders_card positions hnd hcomplete A,
        orders_card positions hnd hcomplete B]
    change uniformOn Set.univ {π | observation π = (xs, ys)} =
      ((Nat.factorial A.card * Nat.factorial B.card : ℕ) : ℝ≥0∞)⁻¹
    simpa only [hC] using hmass
  · rw [if_neg hxy]
    have hempty :
        ({π : Equiv.Perm I |
          (restrictedOrder positions A π, restrictedOrder positions B π) = (xs, ys)}) =
          ∅ := by
      apply Set.ext
      intro π
      change ((restrictedOrder positions A π, restrictedOrder positions B π) =
        (xs, ys)) ↔ False
      constructor
      · intro hπ
        have hA : restrictedOrder positions A π = xs := congrArg Prod.fst hπ
        have hB : restrictedOrder positions B π = ys := congrArg Prod.snd hπ
        exact hxy ⟨hA ▸ restrictedOrder_mem_orders positions hnd hcomplete A π,
          hB ▸ restrictedOrder_mem_orders positions hnd hcomplete B π⟩
      · exact False.elim
    rw [hempty]
    exact measure_empty

/-- The actual joint observation of fixed disjoint subsets has the product
of their existing uniform whole-order laws, including empty subsets. -/
theorem map_restrictedOrder_pair_uniformOn
    [MeasurableSpace (Equiv.Perm I)] [MeasurableSingletonClass (Equiv.Perm I)]
    [MeasurableSpace (List I)] [MeasurableSingletonClass (List I)]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ a, a ∈ positions)
    (A B : Finset I) (hAB : Disjoint A B) :
    (uniformOn (Set.univ : Set (Equiv.Perm I))).map
        (fun π => (restrictedOrder positions A π, restrictedOrder positions B π)) =
      (uniformOn (orders positions A : Set (List I))).prod
        (uniformOn (orders positions B : Set (List I))) := by
  classical
  letI := Fintype.ofList positions hcomplete
  letI : IsProbabilityMeasure (uniformOn (orders positions A : Set (List I))) :=
    isProbabilityMeasure_uniformOn (orders positions A).finite_toSet
      (orders_nonempty positions A)
  letI : IsProbabilityMeasure (uniformOn (orders positions B : Set (List I))) :=
    isProbabilityMeasure_uniformOn (orders positions B).finite_toSet
      (orders_nonempty positions B)
  letI : SFinite (uniformOn (orders positions A : Set (List I))) := inferInstance
  letI : SFinite (uniformOn (orders positions B : Set (List I))) := inferInstance
  have htarget (T : Finset I) (zs : List I) :
      uniformOn (orders positions T : Set (List I)) {zs} =
        if zs ∈ orders positions T then (Nat.factorial T.card : ℝ≥0∞)⁻¹ else 0 := by
    rw [← map_restrictedOrder_uniformOn positions hnd hcomplete T,
      Measure.map_apply (measurable_of_finite _) (measurableSet_singleton zs)]
    exact uniformOn_restrictedOrder_eq positions hnd hcomplete T zs
  have hfactor :
      ((Nat.factorial A.card * Nat.factorial B.card : ℕ) : ℝ≥0∞)⁻¹ =
        (Nat.factorial A.card : ℝ≥0∞)⁻¹ * (Nat.factorial B.card : ℝ≥0∞)⁻¹ := by
    rw [Nat.cast_mul]
    exact ENNReal.mul_inv
      (Or.inl (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero A.card)))
      (Or.inl (ENNReal.natCast_ne_top (Nat.factorial A.card)))
  apply Measure.ext_of_singleton
  rintro ⟨xs, ys⟩
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton (xs, ys))]
  change uniformOn Set.univ
      {π | (restrictedOrder positions A π, restrictedOrder positions B π) = (xs, ys)} =
    ((uniformOn (orders positions A : Set (List I))).prod
      (uniformOn (orders positions B : Set (List I)))) {(xs, ys)}
  rw [uniformOn_restrictedOrder_pair_eq positions hnd hcomplete A B hAB xs ys,
    ← Set.singleton_prod_singleton, Measure.prod_prod, htarget A xs, htarget B ys]
  rw [hfactor]
  by_cases hxs : xs ∈ orders positions A <;>
    by_cases hys : ys ∈ orders positions B <;> simp [hxs, hys]

private theorem filter_pair_hasLaw_orders
    [MeasurableSpace (List I)] [MeasurableSingletonClass (List I)]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ a, a ∈ positions)
    (S A B : Finset I) (hAS : A ⊆ S) (hBS : B ⊆ S) (hAB : Disjoint A B) :
    HasLaw
      (fun xs : List I => (xs.filter (fun a => decide (a ∈ A)),
        xs.filter (fun b => decide (b ∈ B))))
      ((uniformOn (orders positions A : Set (List I))).prod
        (uniformOn (orders positions B : Set (List I))))
      (uniformOn (orders positions S : Set (List I))) := by
  classical
  letI := Fintype.ofList positions hcomplete
  letI : MeasurableSpace (Equiv.Perm I) := ⊤
  letI : MeasurableSingletonClass (Equiv.Perm I) := ⟨fun _ => trivial⟩
  refine {
    aemeasurable := (measurable_of_countable _).aemeasurable
    map_eq := ?_
  }
  rw [← map_restrictedOrder_uniformOn positions hnd hcomplete S,
    Measure.map_map (measurable_of_countable _) (measurable_of_finite _)]
  have hfun :
      (fun xs : List I => (xs.filter (fun a => decide (a ∈ A)),
        xs.filter (fun b => decide (b ∈ B)))) ∘ restrictedOrder positions S =
      (fun π => (restrictedOrder positions A π, restrictedOrder positions B π)) := by
    funext π
    exact Prod.ext (filter_restrictedOrder_of_subset positions S A π hAS)
      (filter_restrictedOrder_of_subset positions S B π hBS)
  rw [hfun]
  exact map_restrictedOrder_pair_uniformOn positions hnd hcomplete A B hAB

/-- Fixed disjoint filters of a uniformly distributed observed whole order
have the product law under that same current environment. The observation
need only have the almost-everywhere measurability recorded by `HasLaw`. -/
theorem hasLaw_filter_pair {Ω : Type*}
    [MeasurableSpace Ω] [MeasurableSpace (List I)] [MeasurableSingletonClass (List I)]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ a, a ∈ positions)
    (S : Finset I) {μ : Measure Ω} {Y : Ω → List I}
    (hY : HasLaw Y (uniformOn (orders positions S : Set (List I))) μ)
    (A B : Finset I) (hAS : A ⊆ S) (hBS : B ⊆ S) (hAB : Disjoint A B) :
    HasLaw
      (fun ω => ((Y ω).filter (fun a => decide (a ∈ A)),
        (Y ω).filter (fun b => decide (b ∈ B))))
      ((uniformOn (orders positions A : Set (List I))).prod
        (uniformOn (orders positions B : Set (List I)))) μ :=
  (filter_pair_hasLaw_orders positions hnd hcomplete S A B hAS hBS hAB).fun_comp hY

end Applications.Probability.PermutationOrder

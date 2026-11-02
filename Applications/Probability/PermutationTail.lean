import Applications.Probability.PermutationOrder
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.HasLaw

/-!
# Conditional remaining order

Revealing the optional head of an observed list conditions the existing
environment measure. Under a uniform whole-order law, the actual tail has
the uniform law on the remaining keys. The reusable statements take
Mathlib's `HasLaw`, so a later step may use an already conditioned
environment without asserting that the full environment is uniform again.

The global-permutation specializations observe the same `restrictedOrder`
as the unconditional law. Their source-event statements require measurable
structure only on permutations; their map statements use the caller's
measurable structure on lists. On the revealed-head event, the actual tail
equals restriction to the erased subset. This is not an equality on every
sample. Fixed remaining-subset filtering composes through that bridge.

Null conditioning is the zero measure. No default key, independently sampled
tail, conditional executor, or assertion about arbitrary histories is used.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Applications.Probability.PermutationTail

open MeasureTheory ProbabilityTheory PermutationOrder
open scoped ENNReal BigOperators

universe u v

variable {I : Type u} {Ω : Type v}

/-- Reveal an actual optional head, without adding a default element. -/
def firstEvent (Y : Ω → List I) (a : I) : Set Ω :=
  {ω | (Y ω).head? = some a}

/-- Specifying the revealed head and the actual tail specifies the whole list. -/
theorem firstEvent_inter_tail (Y : Ω → List I) (a : I) (xs : List I) :
    firstEvent Y a ∩ {ω | (Y ω).tail = xs} = {ω | Y ω = a :: xs} := by
  apply Set.ext
  intro ω
  change ((Y ω).head? = some a ∧ (Y ω).tail = xs) ↔ Y ω = a :: xs
  cases Y ω <;> simp

section Decidable

variable [DecidableEq I]

/-- Prefixing the exposed key restores exactly the full supported orders. -/
theorem cons_mem_orders (positions : List I) (hnd : positions.Nodup)
    (S : Finset I) (a : I) (haPositions : a ∈ positions) (ha : a ∈ S)
    (xs : List I) :
    a :: xs ∈ orders positions S ↔ xs ∈ orders positions (S.erase a) := by
  have hrem : (positions.filter (fun b => decide (b ∈ S.erase a))).Nodup :=
    hnd.filter _
  have hanot : a ∉ positions.filter (fun b => decide (b ∈ S.erase a)) := by
    simp
  have hbase :
      (a :: positions.filter (fun b => decide (b ∈ S.erase a))).Perm
        (positions.filter (fun b => decide (b ∈ S))) := by
    apply (List.perm_ext_iff_of_nodup (List.Nodup.cons hanot hrem) (hnd.filter _)).mpr
    intro b
    by_cases hba : b = a
    · subst b
      simp [haPositions, ha]
    · simp [hba]
  rw [mem_orders, mem_orders]
  constructor
  · intro h
    exact (List.perm_cons a).1 (h.trans hbase.symm)
  · intro h
    exact (h.cons a).trans hbase

/-- On the revealed-head event, removing the head is restriction to the
erased subset. Completeness is not needed for this pointwise identity. -/
theorem tail_restrictedOrder_eq (positions : List I) (hnd : positions.Nodup)
    (S : Finset I) (a : I) (π : Equiv.Perm I)
    (hfirst : π ∈ firstEvent (restrictedOrder positions S) a) :
    (restrictedOrder positions S π).tail =
      restrictedOrder positions (S.erase a) π := by
  obtain ⟨xs, hxs⟩ := List.head?_eq_some_iff.mp hfirst
  have hxsnd : (a :: xs).Nodup := by
    rw [← hxs]
    exact restrictedOrder_nodup positions hnd S π
  have hfilter : xs.filter (fun b => decide (b ∈ S.erase a)) = xs := by
    apply List.filter_eq_self.mpr
    intro b hb
    have hbne : b ≠ a := by
      intro hba
      subst b
      exact hxsnd.notMem hb
    have hbS : b ∈ S := by
      have hbin : b ∈ restrictedOrder positions S π := by
        rw [hxs]
        exact List.mem_cons_of_mem a hb
      exact ((mem_restrictedOrder positions S π b).mp hbin).2
    simp only [decide_eq_true_eq, Finset.mem_erase]
    exact ⟨hbne, hbS⟩
  calc
    (restrictedOrder positions S π).tail = xs := by rw [hxs]; rfl
    _ = (restrictedOrder positions S π).filter (fun b => decide (b ∈ S.erase a)) := by
      rw [hxs]
      simp [hfilter]
    _ = restrictedOrder positions (S.erase a) π :=
      filter_restrictedOrder_of_subset positions S (S.erase a) π (Finset.erase_subset a S)

theorem filter_tail_restrictedOrder_eq (positions : List I) (hnd : positions.Nodup)
    (S : Finset I) (a : I) (π : Equiv.Perm I)
    (hfirst : π ∈ firstEvent (restrictedOrder positions S) a)
    (T : Finset I) (hT : T ⊆ S.erase a) :
    (restrictedOrder positions S π).tail.filter (fun b => decide (b ∈ T)) =
      restrictedOrder positions T π := by
  rw [tail_restrictedOrder_eq positions hnd S a π hfirst]
  exact filter_restrictedOrder_of_subset positions (S.erase a) T π hT

/-- An actual restriction never reveals a key outside its fixed subset. -/
theorem firstEvent_restrictedOrder_of_not_mem (positions : List I)
    (S : Finset I) (a : I) (ha : a ∉ S) :
    firstEvent (restrictedOrder positions S) a = ∅ := by
  apply Set.ext
  intro π
  change ((restrictedOrder positions S π).head? = some a) ↔ False
  constructor
  · intro h
    exact ha ((mem_restrictedOrder positions S π a).mp (List.mem_of_head? h)).2
  · exact False.elim

theorem cond_firstEvent_restrictedOrder_of_not_mem
    [MeasurableSpace (Equiv.Perm I)]
    (positions : List I) (S : Finset I) (a : I) (ha : a ∉ S)
    (μ : Measure (Equiv.Perm I)) :
    μ[|firstEvent (restrictedOrder positions S) a] = 0 := by
  rw [firstEvent_restrictedOrder_of_not_mem positions S a ha, cond_empty]

private theorem factorial_card_erase (S : Finset I) (a : I) (ha : a ∈ S) :
    (Nat.factorial S.card : ℝ≥0∞) =
      (S.card : ℝ≥0∞) * (Nat.factorial (S.erase a).card : ℝ≥0∞) := by
  have h : Nat.factorial S.card = S.card * Nat.factorial (S.erase a).card := by
    rw [← Finset.card_erase_add_one ha, Nat.factorial_succ]
  simpa only [Nat.cast_mul] using congrArg (fun n : ℕ => (n : ℝ≥0∞)) h

private theorem factorial_ratio_head (S : Finset I) (a : I) (ha : a ∈ S) :
    (Nat.factorial (S.erase a).card : ℝ≥0∞) *
        (Nat.factorial S.card : ℝ≥0∞)⁻¹ = (S.card : ℝ≥0∞)⁻¹ := by
  have hm0 : (S.card : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem ha)
  have hn0 : (Nat.factorial (S.erase a).card : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [factorial_card_erase S a ha,
    ENNReal.mul_inv (Or.inl hm0) (Or.inl (ENNReal.natCast_ne_top S.card)),
    mul_left_comm, ENNReal.mul_inv_cancel hn0 (ENNReal.natCast_ne_top _), mul_one]

private theorem factorial_ratio_tail (S : Finset I) (a : I) (ha : a ∈ S) :
    (S.card : ℝ≥0∞) * (Nat.factorial S.card : ℝ≥0∞)⁻¹ =
      (Nat.factorial (S.erase a).card : ℝ≥0∞)⁻¹ := by
  have hm0 : (S.card : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem ha)
  rw [factorial_card_erase S a ha,
    ENNReal.mul_inv (Or.inl hm0) (Or.inl (ENNReal.natCast_ne_top S.card))]
  exact ENNReal.mul_inv_cancel_left hm0 (ENNReal.natCast_ne_top S.card)

/-- The first key within the selected subset has the reciprocal-cardinality
mass under the original global permutation law. -/
theorem uniformOn_firstEvent
    [MeasurableSpace (Equiv.Perm I)] [MeasurableSingletonClass (Equiv.Perm I)]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ b, b ∈ positions)
    (S : Finset I) (a : I) (ha : a ∈ S) :
    uniformOn (Set.univ : Set (Equiv.Perm I))
        (firstEvent (restrictedOrder positions S) a) = (S.card : ℝ≥0∞)⁻¹ := by
  classical
  letI := Fintype.ofList positions hcomplete
  let C := (orders positions (S.erase a)).image (List.cons a)
  have hpre : (restrictedOrder positions S) ⁻¹' (C : Set (List I)) =
      firstEvent (restrictedOrder positions S) a := by
    apply Set.ext
    intro π
    change restrictedOrder positions S π ∈ C ↔
      (restrictedOrder positions S π).head? = some a
    constructor
    · intro hπ
      obtain ⟨xs, _hxs, hxsπ⟩ := Finset.mem_image.mp hπ
      rw [← hxsπ]
      rfl
    · intro hπ
      obtain ⟨xs, hxs⟩ := List.head?_eq_some_iff.mp hπ
      refine Finset.mem_image.mpr ⟨xs, ?_, hxs.symm⟩
      apply (cons_mem_orders positions hnd S a (hcomplete a) ha xs).mp
      rw [← hxs]
      exact restrictedOrder_mem_orders positions hnd hcomplete S π
  have hpartition := sum_measure_preimage_singleton
    (μ := uniformOn (Set.univ : Set (Equiv.Perm I)))
    (f := restrictedOrder positions S) C (fun _ys _ => (Set.toFinite _).measurableSet)
  rw [hpre] at hpartition
  change (∑ ys ∈ C, uniformOn Set.univ {π | restrictedOrder positions S π = ys}) =
    uniformOn Set.univ (firstEvent (restrictedOrder positions S) a) at hpartition
  have hsum :
      (∑ ys ∈ C, uniformOn Set.univ {π | restrictedOrder positions S π = ys}) =
        (C.card : ℝ≥0∞) * (Nat.factorial S.card : ℝ≥0∞)⁻¹ := by
    calc
      _ = ∑ _ys ∈ C, (Nat.factorial S.card : ℝ≥0∞)⁻¹ := by
        apply Finset.sum_congr rfl
        intro ys hys
        obtain ⟨xs, hxs, rfl⟩ := Finset.mem_image.mp hys
        rw [uniformOn_restrictedOrder_eq positions hnd hcomplete S (a :: xs),
          if_pos ((cons_mem_orders positions hnd S a (hcomplete a) ha xs).mpr hxs)]
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : C.card = (orders positions (S.erase a)).card :=
    Finset.card_image_of_injective _ (fun _xs _ys h => (List.cons.inj h).2)
  calc
    uniformOn Set.univ (firstEvent (restrictedOrder positions S) a) =
        ∑ ys ∈ C, uniformOn Set.univ {π | restrictedOrder positions S π = ys} :=
      hpartition.symm
    _ = (C.card : ℝ≥0∞) * (Nat.factorial S.card : ℝ≥0∞)⁻¹ := hsum
    _ = (Nat.factorial (S.erase a).card : ℝ≥0∞) *
        (Nat.factorial S.card : ℝ≥0∞)⁻¹ := by
      rw [hcard, orders_card positions hnd hcomplete (S.erase a)]
    _ = (S.card : ℝ≥0∞)⁻¹ := factorial_ratio_head S a ha

/-- Conditioning the original finite uniform environment gives its uniform
restriction. This also holds on null events and does not require Nodup. -/
theorem cond_uniformOn_firstEvent
    [MeasurableSpace (Equiv.Perm I)] [MeasurableSingletonClass (Equiv.Perm I)]
    (positions : List I) (hcomplete : ∀ b, b ∈ positions) (S : Finset I) (a : I) :
    (uniformOn (Set.univ : Set (Equiv.Perm I)))[|
        firstEvent (restrictedOrder positions S) a] =
      uniformOn (firstEvent (restrictedOrder positions S) a) := by
  classical
  letI := Fintype.ofList positions hcomplete
  have hE : MeasurableSet (firstEvent (restrictedOrder positions S) a) :=
    (Set.toFinite _).measurableSet
  unfold uniformOn
  simpa only [Set.univ_inter] using
    cond_cond_eq_cond_inter (s := Set.univ)
      (t := firstEvent (restrictedOrder positions S) a) MeasurableSet.univ hE
      (Measure.count : Measure (Equiv.Perm I))

/-- Universal source-event formula for the actual tail, including unsupported
lists. No measurable structure on the output lists is required. -/
theorem cond_tail_eq
    [MeasurableSpace (Equiv.Perm I)] [MeasurableSingletonClass (Equiv.Perm I)]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ b, b ∈ positions)
    (S : Finset I) (a : I) (ha : a ∈ S) (xs : List I) :
    (uniformOn (Set.univ : Set (Equiv.Perm I)))[|
        firstEvent (restrictedOrder positions S) a]
        {π | (restrictedOrder positions S π).tail = xs} =
      if xs ∈ orders positions (S.erase a)
      then (Nat.factorial (S.erase a).card : ℝ≥0∞)⁻¹
      else 0 := by
  classical
  letI := Fintype.ofList positions hcomplete
  have hE : MeasurableSet (firstEvent (restrictedOrder positions S) a) :=
    (Set.toFinite _).measurableSet
  rw [cond_apply hE, firstEvent_inter_tail (restrictedOrder positions S) a xs,
    uniformOn_firstEvent positions hnd hcomplete S a ha,
    uniformOn_restrictedOrder_eq positions hnd hcomplete S (a :: xs),
    inv_inv, cons_mem_orders positions hnd S a (hcomplete a) ha xs]
  by_cases hxs : xs ∈ orders positions (S.erase a)
  · simp only [if_pos hxs]
    exact factorial_ratio_tail S a ha
  · simp only [if_neg hxs, mul_zero]

/-- The actual tail's pushforward under the original law conditioned on its
first selected key is the existing uniform remaining-order measure. -/
theorem map_tail_cond_first
    [MeasurableSpace (Equiv.Perm I)] [MeasurableSingletonClass (Equiv.Perm I)]
    [MeasurableSpace (List I)] [MeasurableSingletonClass (List I)]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ b, b ∈ positions)
    (S : Finset I) (a : I) (ha : a ∈ S) :
    ((uniformOn (Set.univ : Set (Equiv.Perm I)))[|
        firstEvent (restrictedOrder positions S) a]).map
        (fun π => (restrictedOrder positions S π).tail) =
      uniformOn (orders positions (S.erase a) : Set (List I)) := by
  classical
  letI := Fintype.ofList positions hcomplete
  apply Measure.ext_of_singleton
  intro xs
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton xs)]
  change (uniformOn (Set.univ : Set (Equiv.Perm I)))[|
      firstEvent (restrictedOrder positions S) a]
      {π | (restrictedOrder positions S π).tail = xs} =
    uniformOn (orders positions (S.erase a) : Set (List I)) {xs}
  have htarget : uniformOn (orders positions (S.erase a) : Set (List I)) {xs} =
      (((orders positions (S.erase a)) ∩ {xs}).card : ℝ≥0∞) /
        ((orders positions (S.erase a)).card : ℝ≥0∞) := by
    simpa only [Finset.coe_singleton] using
      (uniformOn_apply_finset
        (s := orders positions (S.erase a)) (t := ({xs} : Finset (List I))))
  rw [cond_tail_eq positions hnd hcomplete S a ha xs, htarget]
  by_cases hxs : xs ∈ orders positions (S.erase a)
  · simp [hxs, orders_card positions hnd hcomplete (S.erase a), one_div]
  · simp [hxs]

private theorem restrictedOrder_hasLaw
    [MeasurableSpace (Equiv.Perm I)] [MeasurableSingletonClass (Equiv.Perm I)]
    [MeasurableSpace (List I)] [MeasurableSingletonClass (List I)]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ b, b ∈ positions)
    (S : Finset I) :
    HasLaw (restrictedOrder positions S)
      (uniformOn (orders positions S : Set (List I)))
      (uniformOn (Set.univ : Set (Equiv.Perm I))) := by
  classical
  letI := Fintype.ofList positions hcomplete
  exact {
    aemeasurable := (measurable_of_finite _).aemeasurable
    map_eq := map_restrictedOrder_uniformOn positions hnd hcomplete S
  }

private theorem hasLaw_cond {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {Y : A → B}
    (hY : HasLaw Y ν μ) (H : Set B) (hH : MeasurableSet H) :
    HasLaw Y (ν[|H]) (μ[|Y ⁻¹' H]) := by
  refine {
    aemeasurable := hY.aemeasurable.mono_ac cond_absolutelyContinuous
    map_eq := ?_
  }
  unfold ProbabilityTheory.cond
  rw [Measure.map_smul _ hY.aemeasurable.restrict,
    ← Measure.restrict_map_of_aemeasurable hY.aemeasurable hH,
    ← Measure.map_apply_of_aemeasurable hY.aemeasurable hH, hY.map_eq]

private theorem orders_head_mass
    [MeasurableSpace (List I)] [MeasurableSingletonClass (List I)]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ b, b ∈ positions)
    (S : Finset I) (a : I) (ha : a ∈ S) :
    uniformOn (orders positions S : Set (List I))
      (firstEvent (id : List I → List I) a) = (S.card : ℝ≥0∞)⁻¹ := by
  classical
  letI := Fintype.ofList positions hcomplete
  letI : MeasurableSpace (Equiv.Perm I) := ⊤
  letI : MeasurableSingletonClass (Equiv.Perm I) := ⟨fun _ => trivial⟩
  have hO := restrictedOrder_hasLaw positions hnd hcomplete S
  have hH : MeasurableSet {xs : List I | xs.head? = some a} :=
    (Set.to_countable _).measurableSet
  have hmass := hO.measure_eq (p := fun xs => xs.head? = some a) hH
  calc
    uniformOn (orders positions S : Set (List I))
        (firstEvent (id : List I → List I) a) =
        uniformOn (Set.univ : Set (Equiv.Perm I))
          (firstEvent (restrictedOrder positions S) a) := hmass.symm
    _ = (S.card : ℝ≥0∞)⁻¹ := uniformOn_firstEvent positions hnd hcomplete S a ha

/-- The observed whole-order law determines first-key mass even when the
underlying environment is not the original uniform permutation measure. -/
theorem head_mass_of_hasLaw
    [MeasurableSpace Ω] [MeasurableSpace (List I)] [MeasurableSingletonClass (List I)]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ b, b ∈ positions)
    (S : Finset I) (a : I) (ha : a ∈ S)
    {μ : Measure Ω} {Y : Ω → List I}
    (hY : HasLaw Y (uniformOn (orders positions S : Set (List I))) μ) :
    μ (firstEvent Y a) = (S.card : ℝ≥0∞)⁻¹ := by
  classical
  letI := Fintype.ofList positions hcomplete
  have hH : MeasurableSet {xs : List I | xs.head? = some a} :=
    (Set.to_countable _).measurableSet
  calc
    μ (firstEvent Y a) = uniformOn (orders positions S : Set (List I))
        (firstEvent (id : List I → List I) a) :=
      hY.measure_eq (p := fun xs => xs.head? = some a) hH
    _ = (S.card : ℝ≥0∞)⁻¹ := orders_head_mass positions hnd hcomplete S a ha

private theorem tail_hasLaw_orders_cond
    [MeasurableSpace (List I)] [MeasurableSingletonClass (List I)]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ b, b ∈ positions)
    (S : Finset I) (a : I) (ha : a ∈ S) :
    HasLaw (List.tail : List I → List I)
      (uniformOn (orders positions (S.erase a) : Set (List I)))
      ((uniformOn (orders positions S : Set (List I)))[|
        firstEvent (id : List I → List I) a]) := by
  classical
  letI := Fintype.ofList positions hcomplete
  letI : MeasurableSpace (Equiv.Perm I) := ⊤
  letI : MeasurableSingletonClass (Equiv.Perm I) := ⟨fun _ => trivial⟩
  have hH : MeasurableSet (firstEvent (id : List I → List I) a) :=
    (Set.to_countable _).measurableSet
  have hcond := hasLaw_cond (restrictedOrder_hasLaw positions hnd hcomplete S)
    (firstEvent (id : List I → List I) a) hH
  change HasLaw (restrictedOrder positions S)
    ((uniformOn (orders positions S : Set (List I)))[|
      firstEvent (id : List I → List I) a])
    ((uniformOn (Set.univ : Set (Equiv.Perm I)))[|
      firstEvent (restrictedOrder positions S) a]) at hcond
  refine {
    aemeasurable := (measurable_of_countable (List.tail : List I → List I)).aemeasurable
    map_eq := ?_
  }
  rw [← hcond.map_eq,
    Measure.map_map (measurable_of_countable _) (measurable_of_finite _)]
  exact map_tail_cond_first positions hnd hcomplete S a ha

/-- A uniform observed whole order yields a uniform actual remaining order
after revealing its first key. Only almost-everywhere measurability of the
observation, as recorded by `HasLaw`, is required. -/
theorem hasLaw_tail_cond_first
    [MeasurableSpace Ω] [MeasurableSpace (List I)] [MeasurableSingletonClass (List I)]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ b, b ∈ positions)
    (S : Finset I) (a : I) (ha : a ∈ S)
    {μ : Measure Ω} {Y : Ω → List I}
    (hY : HasLaw Y (uniformOn (orders positions S : Set (List I))) μ) :
    HasLaw (fun ω => (Y ω).tail)
      (uniformOn (orders positions (S.erase a) : Set (List I)))
      (μ[|firstEvent Y a]) := by
  classical
  letI := Fintype.ofList positions hcomplete
  have hH : MeasurableSet (firstEvent (id : List I → List I) a) :=
    (Set.to_countable _).measurableSet
  have hcond := hasLaw_cond hY (firstEvent (id : List I → List I) a) hH
  change HasLaw Y
    ((uniformOn (orders positions S : Set (List I)))[|
      firstEvent (id : List I → List I) a]) (μ[|firstEvent Y a]) at hcond
  exact (tail_hasLaw_orders_cond positions hnd hcomplete S a ha).fun_comp hcond

private theorem filter_hasLaw_orders
    [MeasurableSpace (List I)] [MeasurableSingletonClass (List I)]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ b, b ∈ positions)
    (S T : Finset I) (hT : T ⊆ S) :
    HasLaw (fun xs : List I => xs.filter (fun b => decide (b ∈ T)))
      (uniformOn (orders positions T : Set (List I)))
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
      (fun xs : List I => xs.filter (fun b => decide (b ∈ T))) ∘
          restrictedOrder positions S = restrictedOrder positions T := by
    funext π
    exact filter_restrictedOrder_of_subset positions S T π hT
  rw [hfun]
  exact map_restrictedOrder_uniformOn positions hnd hcomplete T

/-- Filtering a fixed subset of the actual remaining order preserves the
uniform observed-law invariant under the same conditioned environment. -/
theorem hasLaw_filter_tail_cond_first
    [MeasurableSpace Ω] [MeasurableSpace (List I)] [MeasurableSingletonClass (List I)]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ b, b ∈ positions)
    (S : Finset I) (a : I) (ha : a ∈ S)
    {μ : Measure Ω} {Y : Ω → List I}
    (hY : HasLaw Y (uniformOn (orders positions S : Set (List I))) μ)
    (T : Finset I) (hT : T ⊆ S.erase a) :
    HasLaw (fun ω => (Y ω).tail.filter (fun b => decide (b ∈ T)))
      (uniformOn (orders positions T : Set (List I)))
      (μ[|firstEvent Y a]) :=
  (filter_hasLaw_orders positions hnd hcomplete (S.erase a) T hT).fun_comp
    (hasLaw_tail_cond_first positions hnd hcomplete S a ha hY)

/-- The actual original T projection has the stated conditional law when T
is fixed inside the unexposed part of S. -/
theorem map_restrictedOrder_cond_first
    [MeasurableSpace (Equiv.Perm I)] [MeasurableSingletonClass (Equiv.Perm I)]
    [MeasurableSpace (List I)] [MeasurableSingletonClass (List I)]
    (positions : List I) (hnd : positions.Nodup) (hcomplete : ∀ b, b ∈ positions)
    (S : Finset I) (a : I) (ha : a ∈ S) (T : Finset I) (hT : T ⊆ S.erase a) :
    ((uniformOn (Set.univ : Set (Equiv.Perm I)))[|
        firstEvent (restrictedOrder positions S) a]).map (restrictedOrder positions T) =
      uniformOn (orders positions T : Set (List I)) := by
  classical
  letI := Fintype.ofList positions hcomplete
  have h := hasLaw_filter_tail_cond_first positions hnd hcomplete S a ha
    (restrictedOrder_hasLaw positions hnd hcomplete S) T hT
  have hE : MeasurableSet (firstEvent (restrictedOrder positions S) a) :=
    (Set.toFinite _).measurableSet
  have heq : restrictedOrder positions T =ᵐ[
      (uniformOn (Set.univ : Set (Equiv.Perm I)))[|
        firstEvent (restrictedOrder positions S) a]]
      (fun π => (restrictedOrder positions S π).tail.filter (fun b => decide (b ∈ T))) :=
    ae_cond_of_forall_mem hE fun π hπ =>
      (filter_tail_restrictedOrder_eq positions hnd S a π hπ T hT).symm
  exact (h.congr heq).map_eq

end Decidable

end Applications.Probability.PermutationTail

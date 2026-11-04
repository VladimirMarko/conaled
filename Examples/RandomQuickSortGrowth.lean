import Applications.Resources.RandomQuickSortGrowth

/-! Actual-execution clients of the harmonic and growth bounds.
Small means and the duplicate counterexamples were fixed independently before
the proofs. Arbitrary function-valued tags exercise the absence of payload
equality, enumeration and measurability assumptions. Family bounds use actual
length; neither the sampler nor pivot indexing/removal receives a new tariff.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RandomQuickSortGrowth
open Resources.RandomQuickSort
universe u v

noncomputable section

local notation "natLt" => (fun a b : Nat => decide (a < b))

/-- An uninhabited payload still has the positive empty-run mean. -/
theorem empty_payload_means :
    exerciseMean (fun _ _ : Empty => false) [] =
        8 * ((0 : ℝ) + 1) * (harmonic 0 : ℝ) - 12 * (0 : ℝ) + 1 ∧
      exerciseMean (fun _ _ : Empty => false) [] = 1 ∧
      literalMean (fun _ _ : Empty => false) [] = 1 := by
  constructor
  · exact exerciseMean_eq_harmonic (fun _ : Empty => (0 : Nat)) [] (by simp)
  · simp

theorem singleton_payload_means {α : Type u} {κ : Type v} [LinearOrder κ]
    (key : α → κ) (x : α) :
    exerciseMean (fun a b => decide (key a < key b)) [x] = 5 ∧
      literalMean (fun a b => decide (key a < key b)) [x] = 8 ∧
      5 ≤ literalMean (fun a b => decide (key a < key b)) [x] ∧
      literalMean (fun a b => decide (key a < key b)) [x] ≤ 10 := by
  norm_num

theorem empty_log_boundary (C : ℝ) :
    ¬ exerciseMean (fun _ _ : Empty => false) [] ≤
        C * ((0 : ℝ) * Real.logb 2 0) ∧
      ¬ literalMean (fun _ _ : Empty => false) [] ≤
        C * ((0 : ℝ) * Real.logb 2 0) := by
  simp

theorem singleton_log_boundary {α : Type u} {κ : Type v} [LinearOrder κ]
    (key : α → κ) (x : α) (C : ℝ) :
    ¬ exerciseMean (fun a b => decide (key a < key b)) [x] ≤
        C * ((1 : ℝ) * Real.logb 2 1) ∧
      ¬ literalMean (fun a b => decide (key a < key b)) [x] ≤
        C * ((1 : ℝ) * Real.logb 2 1) := by
  simp

/-- The loose scalar bounds at the first admissible size are not exact means. -/
theorem two_distinct_harmonic :
    exerciseMean natLt [1, 0] = 13 ∧
      13 ≤ literalMean natLt [1, 0] ∧
      literalMean natLt [1, 0] ≤ 26 ∧
      exerciseMean natLt [1, 0] ≤ 64 ∧
      literalMean natLt [1, 0] ≤ 128 := by
  have he := exerciseMean_eq_harmonic (id : Nat → Nat) [1, 0] (by decide)
  have hc := literalMean_harmonic_comparison (id : Nat → Nat) [1, 0] (by decide)
  norm_num [harmonic_succ] at he hc
  have hbE := exerciseMean_le_nlogb (id : Nat → Nat) [1, 0] (by decide) (by decide)
  have hbF := literalMean_le_nlogb (id : Nat → Nat) [1, 0] (by decide) (by decide)
  have hlog : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
  norm_num [hlog] at hbE hbF
  exact ⟨he, hc.1, hc.2, hbE, hbF⟩

/-- The independently calculated actual masses 1/3 at 21 and 2/3 at 25 agree. -/
theorem three_reordered_harmonic :
    exerciseMean natLt [2, 0, 1] = (71 : ℝ) / 3 ∧
      (71 : ℝ) / 3 ≤ literalMean natLt [2, 0, 1] ∧
      literalMean natLt [2, 0, 1] ≤ (142 : ℝ) / 3 := by
  have he := exerciseMean_eq_harmonic (id : Nat → Nat) [2, 0, 1] (by decide)
  have hc := literalMean_harmonic_comparison (id : Nat → Nat) [2, 0, 1] (by decide)
  norm_num [harmonic_succ] at he hc
  exact ⟨he, hc⟩

theorem four_tagged_harmonic {α : Type u} (a b c d : α) :
    exerciseMean (fun x y : Nat × α => decide (x.1 < y.1))
        [(3, a), (1, b), (0, c), (2, d)] = (109 : ℝ) / 3 ∧
      (109 : ℝ) / 3 ≤
        literalMean (fun x y : Nat × α => decide (x.1 < y.1))
          [(3, a), (1, b), (0, c), (2, d)] ∧
      literalMean (fun x y : Nat × α => decide (x.1 < y.1))
          [(3, a), (1, b), (0, c), (2, d)] ≤ (218 : ℝ) / 3 := by
  have hd :
      (([(3, a), (1, b), (0, c), (2, d)] : List (Nat × α)).map Prod.fst).Nodup := by
    change ([3, 1, 0, 2] : List Nat).Nodup
    decide
  have he := exerciseMean_eq_harmonic (Prod.fst : Nat × α → Nat)
    [(3, a), (1, b), (0, c), (2, d)] hd
  have hc := literalMean_harmonic_comparison (Prod.fst : Nat × α → Nat)
    [(3, a), (1, b), (0, c), (2, d)] hd
  norm_num [harmonic_succ] at he hc
  exact ⟨he, hc⟩

theorem five_sizeMean : sizeMean 5 = (253 : ℝ) / 5 := by
  rw [sizeMean_eq_harmonic]
  norm_num [harmonic_succ]

/-- Arbitrary distinct-key lists of each size, with no order law on payloads. -/
theorem arbitrary_length_indexed_growth {α : Type u} {κ : Type v} [LinearOrder κ]
    (key : α → κ) (xs : Nat → List α)
    (hd : ∀ n, ((xs n).map key).Nodup) (hlen : ∀ n, (xs n).length = n) :
    Asymptotics.IsBigO Filter.atTop
        (fun n => exerciseMean (fun a b => decide (key a < key b)) (xs n))
        (fun n : Nat => (n : ℝ) * Real.logb 2 (n : ℝ)) ∧
      Asymptotics.IsBigO Filter.atTop
        (fun n => literalMean (fun a b => decide (key a < key b)) (xs n))
        (fun n : Nat => (n : ℝ) * Real.logb 2 (n : ℝ)) := by
  have ht : Filter.Tendsto (fun n => (xs n).length) Filter.atTop Filter.atTop := by
    have heq : (fun n => (xs n).length) = id := funext hlen
    rw [heq]
    exact Filter.tendsto_id
  have he := exerciseMean_family_isBigO_logb key Filter.atTop xs
    (Filter.Eventually.of_forall hd) ht
  have hf := literalMean_family_isBigO_logb key Filter.atTop xs
    (Filter.Eventually.of_forall hd) ht
  simpa only [hlen] using And.intro he hf

/-- Full payloads contain arbitrary functions; only their Nat keys are ordered. -/
theorem function_tagged_family_growth (tags : Nat → Nat → (Nat → Nat)) :
    Asymptotics.IsBigO Filter.atTop
        (fun n => exerciseMean (fun a b : Nat × (Nat → Nat) => decide (a.1 < b.1))
          ((List.range n).map (fun k => (k, tags n k))))
        (fun n : Nat => (n : ℝ) * Real.logb 2 (n : ℝ)) ∧
      Asymptotics.IsBigO Filter.atTop
        (fun n => literalMean (fun a b : Nat × (Nat → Nat) => decide (a.1 < b.1))
          ((List.range n).map (fun k => (k, tags n k))))
        (fun n : Nat => (n : ℝ) * Real.logb 2 (n : ℝ)) := by
  apply arbitrary_length_indexed_growth (Prod.fst : Nat × (Nat → Nat) → Nat)
    (fun n => (List.range n).map (fun k => (k, tags n k)))
  · intro n
    rw [List.map_map]
    change ((List.range n).map id).Nodup
    rw [List.map_id]
    exact List.nodup_range
  · intro n
    simp only [List.length_map, List.length_range]

/-- The family's index differs from the size used in its growth function. -/
theorem shifted_range_family_growth :
    Asymptotics.IsBigO Filter.atTop
        (fun n : Nat => exerciseMean natLt (List.range (n + 2)))
        (fun n : Nat => ((n + 2 : Nat) : ℝ) * Real.logb 2 ((n + 2 : Nat) : ℝ)) ∧
      Asymptotics.IsBigO Filter.atTop
        (fun n : Nat => literalMean natLt (List.range (n + 2)))
        (fun n : Nat => ((n + 2 : Nat) : ℝ) * Real.logb 2 ((n + 2 : Nat) : ℝ)) := by
  have hd : ∀ᶠ n : Nat in Filter.atTop,
      ((List.range (n + 2)).map (id : Nat → Nat)).Nodup :=
    Filter.Eventually.of_forall (fun n => by
      simpa only [List.map_id] using (List.nodup_range (n := n + 2)))
  have ht : Filter.Tendsto (fun n : Nat => (List.range (n + 2)).length)
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with n hn
    simp only [List.length_range]
    omega
  have he := exerciseMean_family_isBigO_logb (id : Nat → Nat) Filter.atTop
    (fun n => List.range (n + 2)) hd ht
  have hf := literalMean_family_isBigO_logb (id : Nat → Nat) Filter.atTop
    (fun n => List.range (n + 2)) hd ht
  simpa only [List.length_range] using And.intro he hf

/-- Constant key 7 gives the all-false comparator despite distinct payloads. -/
theorem equal_key_three_not_harmonic :
    ([0, 1, 2] : List Nat).Nodup ∧
      ¬ (([0, 1, 2] : List Nat).map (fun _ => (7 : Nat))).Nodup ∧
      exerciseMean (fun _ _ : Nat => false) [0, 1, 2] = 25 ∧
      exerciseMean (fun _ _ : Nat => false) [0, 1, 2] ≠
        8 * ((3 : ℝ) + 1) * (harmonic 3 : ℝ) - 12 * (3 : ℝ) + 1 := by
  have he := exerciseMean_of_all_false (fun _ _ : Nat => false) [0, 1, 2]
    (by intro _ _ _ _; rfl)
  norm_num at he
  refine ⟨by decide, by decide, he, ?_⟩
  rw [he]
  norm_num [harmonic_succ]

/-- The exact infinite-family boundary retains both actual quadratic tariffs. -/
theorem equal_key_family_means {α : Type u} (tags : List α) :
    exerciseMean (fun _ _ : α => false) tags =
        ((2 * tags.length ^ 2 + 2 * tags.length + 1 : Nat) : ℝ) ∧
      literalMean (fun _ _ : α => false) tags =
        ((2 * tags.length ^ 2 + 5 * tags.length + 1 : Nat) : ℝ) :=
  ⟨exerciseMean_of_all_false _ tags (by intro _ _ _ _; rfl),
    literalMean_of_all_false _ tags (by intro _ _ _ _; rfl)⟩

/-- Both fixed constants fail without key distinctness. This finite example is
not itself a claim that no Big-O constant exists for an entire family. -/
theorem equal_key_binary_bounds_fail :
    (List.range 256).Nodup ∧
      exerciseMean (fun _ _ : Nat => false) (List.range 256) = 131585 ∧
      literalMean (fun _ _ : Nat => false) (List.range 256) = 132353 ∧
      ¬ exerciseMean (fun _ _ : Nat => false) (List.range 256) ≤
        32 * ((256 : ℝ) * Real.logb 2 (256 : ℝ)) ∧
      ¬ literalMean (fun _ _ : Nat => false) (List.range 256) ≤
        64 * ((256 : ℝ) * Real.logb 2 (256 : ℝ)) := by
  have h := equal_key_family_means (List.range 256)
  norm_num at h
  have hlog : Real.logb 2 (256 : ℝ) = 8 := by
    have hp := Real.logb_pow (2 : ℝ) (2 : ℝ) 8
    have hs : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
    rw [hs] at hp
    norm_num at hp
    exact hp
  refine ⟨List.nodup_range, h.1, h.2, ?_, ?_⟩
  · rw [h.1, hlog]
    norm_num
  · rw [h.2, hlog]
    norm_num

end
end Examples.RandomQuickSortGrowth

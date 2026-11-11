import Applications.Resources.DigitSearch
import Examples.DigitSearchContract

/-! First-hit clients and finite populations distinguish execution from a limiting mean. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources.DigitSearchExamples
open DigitSearch

theorem hit : search large [0,4,8,9] = (some 2,3) :=
  first_hit_suffix large [0,4] 8 [9] (by decide) (by decide)

theorem miss : search large [0,4,3] = (none,3) :=
  no_hit large [0,4,3] (by decide)

/-- Duplicate hits after the first are never inspected. -/
theorem duplicate_suffix (xs : List Digit) : search large (8::8::xs) = (some 0,1) :=
  first_hit_suffix large [] 8 (8::xs) (by simp) (by decide)

example : ∃ h : 2 < ([0,4,8,9] : List Digit).length,
    large ([0,4,8,9] : List Digit)[2] = true ∧
      ∀ j (hj : j<2), large (([0,4,8,9] : List Digit)[j]'(Nat.lt_trans hj h)) = false :=
  (first_spec large [0,4,8,9] 2).mp (congrArg Prod.fst hit)

example : (ListFusion.takeWhile 0 0 1 (fun d => !large d) [0,4,8,9]).2 = 3 := by
  rw [← work_eq_takeWhile,hit]

example : signedPosition (search large [0,4,3]).1 = -1 :=
  (signed_failure _ _).mpr (by decide)

theorem worst (n : Nat) : search large (List.replicate n (0:Digit)) = (none,n) := by
  simpa using no_hit large (List.replicate n (0:Digit)) (by simp [large])
theorem best (n : Nat) : search large (List.replicate (n+1) (9:Digit)) = (some 0,1) := by
  rw [List.replicate_succ]
  exact first_hit_suffix large [] 9 _ (by simp) (by decide)

/-- The native product's complete successor equation yields the frozen ordered pairs. -/
theorem words_two : words 2 = DigitSearchContract.pairs := by
  rw [words_succ,words_succ,words_zero]
  simp [DigitSearchContract.pairs,DigitSearchContract.digits,DigitSearch.digits,← List.map_eq_flatMap,List.map_map,Function.comp_def]

example : (words 2).take 2 = [[0,0],[0,1]] := by rw [words_two]; decide
example : ((words 2).drop 9).take 2 = [[0,9],[1,0]] := by rw [words_two]; decide

theorem sections_wrong_order : words 2 ≠ [digits,digits].sections := by
  intro h
  have hp := congrArg (List.take 2) h
  rw [words_two] at hp
  have hn : DigitSearchContract.pairs.take 2 ≠ [digits,digits].sections.take 2 := by decide
  exact hn hp

theorem two_population_partition :
    ((words 2).filter (fun xs => (search large xs).1 == some 0)).length = 50 ∧
    ((words 2).filter (fun xs => (search large xs).1 == some 1)).length = 25 ∧
    ((words 2).filter (fun xs => (search large xs).1 == none)).length = 25 := by
  simp only [words_two,search_value]
  decide

theorem total_two : totalCost 2 = 150 := by
  have h := totalCost_exact 2
  norm_num at h
  omega

theorem function_population_total :
    (∑ f : Fin 2 → Digit, (search large (List.ofFn f)).2) = 150 := by
  rw [← totalCost_functions,total_two]

theorem mean_two : expected 2 = 3/2 := by rw [expected_closed]; norm_num

theorem finite_function_mean :
    (∑ f : Fin 2 → Digit, ((search large (List.ofFn f)).2 : ℚ)) /
      (Fintype.card (Fin 2 → Digit) : ℚ) = 3/2 := by
  rw [← expected_functions]
  exact mean_two

theorem empty_population : words 0 = [[]] ∧ (words 0).length = 1 ∧
    totalCost 0 = 0 ∧ expected 0 = 0 := by
  refine ⟨words_zero,rfl,rfl,?_⟩
  rw [expected_closed]; norm_num

theorem finite_mean_correction : expected 1 = 1 ∧
    expected 1 ≠ (∑ k ∈ Finset.Ico 1 (2:Nat), (k:ℚ)/(2:ℚ)^k) ∧ expected 1 ≠ 2 := by
  rw [expected_closed]
  norm_num

/-- Every finite population remains strictly below its limiting mean. -/
example (n : Nat) : expected n < 2 ∧ 2-expected n = 2/(2:ℚ)^n :=
  ⟨expected_lt_two n,expected_error n⟩

example (ε : ℚ) (he : 0<ε) (n : Nat)
    (hn : 2*((⌈(2/ε:ℚ)⌉:ℤ).natAbs+1) ≤ n) :
    0 < 2-expected n ∧ 2-expected n < ε := expected_modulus ε he n hn

example : Filter.Tendsto expected Filter.atTop (nhds (2:ℚ)) := expected_tendsto
end Resources.DigitSearchExamples

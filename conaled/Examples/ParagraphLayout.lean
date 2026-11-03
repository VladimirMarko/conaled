import Applications.Paragraphs.Observation

/-! Exact character-list examples and independent global layout contracts. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.ParagraphLayout
open Paragraphs OrderedPartitions

/-- Representative words for the printed example widths; not a change to Text's representation. -/
def wordOfLength (n : Nat) : Word := List.replicate n 'a'

def bookWords : Text :=
  [wordOfLength 6, wordOfLength 1, wordOfLength 5, wordOfLength 3, wordOfLength 4, wordOfLength 7]

def bookGreedy : Para :=
  [[wordOfLength 6, wordOfLength 1], [wordOfLength 5, wordOfLength 3],
    [wordOfLength 4], [wordOfLength 7]]

def bookAlternative : Para :=
  [[wordOfLength 6], [wordOfLength 1, wordOfLength 5],
    [wordOfLength 3, wordOfLength 4], [wordOfLength 7]]

def exerciseWords : Text :=
  [wordOfLength 6, wordOfLength 1, wordOfLength 5, wordOfLength 3, wordOfLength 4]

def exerciseFirst : Para :=
  [[wordOfLength 6, wordOfLength 1], [wordOfLength 5, wordOfLength 3], [wordOfLength 4]]

def exerciseSecond : Para :=
  [[wordOfLength 6], [wordOfLength 1, wordOfLength 5], [wordOfLength 3, wordOfLength 4]]

def equalityFirst : Para :=
  [[wordOfLength 1, wordOfLength 1], [wordOfLength 1]]

def equalitySecond : Para :=
  [[wordOfLength 1], [wordOfLength 1, wordOfLength 1]]

theorem book_greedy_eq : greedy 10 bookWords = bookGreedy := by decide

theorem book_minimumLex : MinimumLex 10 bookWords bookGreedy := by
  rw [← book_greedy_eq]
  exact greedy_minimumLex 10 bookWords (by decide)

/-- The reversed old comparison refutes the count-only local sufficient condition. -/
theorem exercise12_14_condition_failure :
    SourceInput 10 exerciseWords ∧
    FitPartition 10 exerciseWords exerciseFirst ∧ FitPartition 10 exerciseWords exerciseSecond ∧
    (wordOfLength 4).length ≤ 10 ∧ cost1 exerciseSecond ≤ cost1 exerciseFirst ∧
    ¬ cost1 (add 10 exerciseSecond (wordOfLength 4)) ≤
      cost1 (add 10 exerciseFirst (wordOfLength 4)) := by decide

/-- Full relevant premises hold, but printed297's both-bind width equality is too strong. -/
theorem printed297_both_bind_equality_counterexample :
    SourceInput 5 [wordOfLength 1, wordOfLength 1, wordOfLength 1, wordOfLength 1] ∧
    FitPartition 5 [wordOfLength 1, wordOfLength 1, wordOfLength 1] equalityFirst ∧
    FitPartition 5 [wordOfLength 1, wordOfLength 1, wordOfLength 1] equalitySecond ∧
    cost1 equalityFirst = cost1 equalitySecond ∧ lastWidth equalityFirst ≤ lastWidth equalitySecond ∧
    fits 5 (equalityFirst.getLastD [] ++ [wordOfLength 1]) = true ∧
    fits 5 (equalitySecond.getLastD [] ++ [wordOfLength 1]) = true ∧
    add 5 equalityFirst (wordOfLength 1) = bindRight (wordOfLength 1) equalityFirst ∧
    add 5 equalitySecond (wordOfLength 1) = bindRight (wordOfLength 1) equalitySecond ∧
    lastWidth (add 5 equalityFirst (wordOfLength 1)) ≠
      lastWidth (add 5 equalitySecond (wordOfLength 1)) := by decide


/-- The empty extension has an optimum although the printed input domain is nonempty. -/
theorem empty : greedy 0 [] = [] ∧ greedy2 0 [] = [] ∧ MinimumLines 0 [] [] ∧
    ¬ SourceInput 0 [] := by
  exact ⟨rfl, rfl, greedy_minimumLines 0 [] (by simp [AllWordsFit]), by simp [SourceInput]⟩

theorem singleton : MinimumLex 3 [wordOfLength 3] [[wordOfLength 3]] :=
  greedy_minimumLex 3 [wordOfLength 3] (by decide)

/-- The inclusive width guard counts the separator and accepts equality. -/
theorem exact_width : greedy 5 [wordOfLength 2, wordOfLength 2] =
    [[wordOfLength 2, wordOfLength 2]] ∧
    greedy2 5 [wordOfLength 2, wordOfLength 2] = [[wordOfLength 2, wordOfLength 2]] ∧
    MinimumLex 5 [wordOfLength 2, wordOfLength 2] [[wordOfLength 2, wordOfLength 2]] := by
  have he : greedy 5 [wordOfLength 2, wordOfLength 2] = [[wordOfLength 2, wordOfLength 2]] := by decide
  refine ⟨he, ?_, ?_⟩
  · rw [greedy2_eq_greedy _ _ (by decide), he]
  · simpa only [he] using greedy_minimumLex 5 [wordOfLength 2, wordOfLength 2] (by decide)

/-- Fewer lines win even when the selected final line is wider. -/
theorem lex_count_priority : lexCost [[wordOfLength 2, wordOfLength 2]] ≤
    lexCost [[wordOfLength 2], [wordOfLength 2]] ∧
    lastWidth [[wordOfLength 2], [wordOfLength 2]] <
      lastWidth [[wordOfLength 2, wordOfLength 2]] := by
  exact ⟨(costLE_iff_lex _ _).mp (exact_width.2.2.2 _ (by decide)), by decide⟩

theorem source_domains : FoldDomain 5 [] [wordOfLength 2, wordOfLength 2] ∧
    Greedy2Domain 5 [wordOfLength 2, wordOfLength 2] :=
  ⟨greedy_source_domain _ _ (by decide), greedy2_source_domain _ _ (by decide)⟩

/-- Both candidates fit, but exhaustive generation and greedy selection order differ. -/
theorem candidate_order :
    fitExtend 5 (wordOfLength 2) [[wordOfLength 2]] =
      [[[wordOfLength 2], [wordOfLength 2]], [[wordOfLength 2, wordOfLength 2]]] ∧
    addCandidates 5 [[wordOfLength 2]] (wordOfLength 2) =
      [[[wordOfLength 2, wordOfLength 2]], [[wordOfLength 2], [wordOfLength 2]]] := by decide

def repeatedProblem : Problem := ⟨(3, [wordOfLength 1, wordOfLength 1, wordOfLength 1]), by decide⟩

theorem repeated_layout :
    greedy repeatedProblem.val.1 repeatedProblem.val.2 =
      [[wordOfLength 1, wordOfLength 1], [wordOfLength 1]] ∧
    MinimumLex 3 repeatedProblem.val.2 [[wordOfLength 1, wordOfLength 1], [wordOfLength 1]] := by
  have he : greedy repeatedProblem.val.1 repeatedProblem.val.2 =
      [[wordOfLength 1, wordOfLength 1], [wordOfLength 1]] := by decide
  have h := selected_layout_optimal repeatedProblem
  rw [he] at h
  exact ⟨he, h⟩

theorem repeated_count : (lineCountSquare.impl repeatedProblem).2 = 2 := by
  apply selected_lineCount_eq repeatedProblem [[wordOfLength 1, wordOfLength 1], [wordOfLength 1]]
  exact ⟨repeated_layout.2.1, fun q hq => costLE_count _ q (repeated_layout.2.2 q hq)⟩

def bookProblem : Problem := ⟨(10, bookWords), by decide⟩

theorem book_layout_consumer : MinimumLex 10 bookWords bookGreedy := by
  have h := selected_layout_optimal bookProblem
  simpa only [bookProblem, book_greedy_eq] using h

theorem alternative_optimum : MinimumLex 10 bookWords bookAlternative := by
  refine ⟨by decide, ?_⟩
  intro q hq
  apply (costLE_iff_lex _ q).mpr
  have he : lexCost bookAlternative = lexCost bookGreedy := by decide
  rw [he]
  exact (costLE_iff_lex _ q).mp (book_layout_consumer.2 q hq)

/-- Equal global scores permit distinct ordered layout witnesses. -/
theorem tied_layouts : bookGreedy ≠ bookAlternative ∧
    cost1Prime bookGreedy = (4, 7) ∧ cost1Prime bookAlternative = (4, 7) ∧
    (lineCountSquare.impl bookProblem).2 = 4 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  apply selected_lineCount_eq bookProblem bookAlternative
  exact ⟨alternative_optimum.1, fun q hq => costLE_count _ q (alternative_optimum.2 q hq)⟩

/-- Mathematical correctness permits an empty word; the source-word domain does not. -/
theorem empty_word_extension : MinimumLex 0 [[]] [[[]]] ∧ ¬ SourceInput 0 [[]] := by
  exact ⟨greedy_minimumLex 0 [[]] (by decide), by decide⟩

/-- Removing AllWordsFit makes the two actual totalized algorithms disagree. -/
theorem oversized_divergence : ¬ AllWordsFit 1 [wordOfLength 2, wordOfLength 2] ∧
    greedy 1 [wordOfLength 2, wordOfLength 2] = [] ∧
    greedy2 1 [wordOfLength 2, wordOfLength 2] = [[wordOfLength 2], [wordOfLength 2]] := by decide

/-- The valid nonstrict conclusion survives the printed both-bind equality failure. -/
theorem both_bind_inequality : CostLE
    (add 5 equalityFirst (wordOfLength 1)) (add 5 equalitySecond (wordOfLength 1)) :=
  add_cost_mono 5 [wordOfLength 1, wordOfLength 1, wordOfLength 1]
    equalityFirst equalitySecond (wordOfLength 1)
    (by simp [IsPartition, NonemptyBlocks, equalityFirst])
    (by simp [IsPartition, NonemptyBlocks, equalitySecond]) (by decide) (by decide)

theorem exercise_append_outputs : add 10 exerciseFirst (wordOfLength 4) =
      [[wordOfLength 6, wordOfLength 1], [wordOfLength 5, wordOfLength 3],
        [wordOfLength 4, wordOfLength 4]] ∧
    add 10 exerciseSecond (wordOfLength 4) =
      [[wordOfLength 6], [wordOfLength 1, wordOfLength 5],
        [wordOfLength 3, wordOfLength 4], [wordOfLength 4]] := by decide

end Examples.ParagraphLayout

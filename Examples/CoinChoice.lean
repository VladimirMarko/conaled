import Applications.CoinChoice.Descending

/-! Lexical greatestness and coin-count minimality are separate checked consumers. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CoinChoice
open Applications.CoinChoice Optimization Optimization.Thinning

private theorem currency431 : Currency [4, 3, 1] := .cons (by decide) (.cons (by decide) .unit)
private theorem currency731 : Currency [7, 3, 1] := .cons (by decide) (.cons (by decide) .unit)

theorem zero_amount {ds : List Nat} (h : Currency ds) :
    LexMaximumTuple ds 0 (List.replicate ds.length 0) ∧
      MinCoins ds 0 (List.replicate ds.length 0) := by
  constructor
  · simpa only [mkchange3_zero h] using mkchange3_lexMaximum h 0
  · apply mkchange_spec h
    rw [mkchange, mktuples_zero h]
    rfl

theorem unit_currency (n : Nat) : LexMaximumTuple [1] n [n] ∧ MinCoins [1] n [n] := by
  constructor
  · simpa only [mkchange3_unit] using mkchange3_lexMaximum Currency.unit n
  · apply mkchange_spec Currency.unit
    rw [mkchange, mktuples_unit]
    rfl

theorem ascending_order : mktuples2 [2, 1] 4 = [[0, 4], [1, 2], [2, 0]] := by
  rw [mktuples2_eq_mktuples]
  decide

theorem descending_order : mktuples3 [4, 3, 1] 6 =
    [[1, 0, 2], [0, 2, 0], [0, 1, 3], [0, 0, 6]] := by
  rw [mktuples3_eq_reverse]
  decide

theorem enumeration_complete (cs : List Nat) :
    cs ∈ mktuples [4, 3, 1] 6 ↔ cs.length = 3 ∧ amount [4, 3, 1] cs = 6 := by
  rw [mem_mktuples_iff currency431, represents_iff_amount]
  rfl

theorem repeated_positions :
    LexMaximumTuple [2, 2, 1] 4 [2, 0, 0] ∧ MinCoins [2, 2, 1] 4 [0, 2, 0] := by
  have h : Currency [2, 2, 1] := .cons (by decide) (.cons (by decide) .unit)
  constructor
  · have he : mkchange3 [2, 2, 1] 4 = [2, 0, 0] := by decide
    exact he ▸ mkchange3_lexMaximum h 4
  · exact mkchange_spec h 4 _ (by decide)

theorem nonmonotone_positions :
    LexMaximumTuple [1, 5, 1] 6 [6, 0, 0] ∧ MinCoins [1, 5, 1] 6 [1, 1, 0] := by
  have h : Currency [1, 5, 1] := .cons (by decide) (.cons (by decide) .unit)
  constructor
  · have he : mkchange3 [1, 5, 1] 6 = [6, 0, 0] := by decide
    exact he ▸ mkchange3_lexMaximum h 6
  · exact mkchangeStrict_spec h 6 _ (by decide)

theorem ordinary_change : LexMaximumTuple [5, 2, 1] 11 [2, 0, 1] ∧
    MinCoins [5, 2, 1] 11 [2, 0, 1] := by
  have h : Currency [5, 2, 1] := .cons (by decide) (.cons (by decide) .unit)
  constructor
  · have he : mkchange3 [5, 2, 1] 11 = [2, 0, 1] := by decide
    exact he ▸ mkchange3_lexMaximum h 11
  · exact mkchange_spec h 11 _ (by decide)

theorem different_objectives : LexMaximumTuple [4, 3, 1] 6 [1, 0, 2] ∧
    MinCoins [4, 3, 1] 6 [0, 2, 0] ∧ ¬ MinCoins [4, 3, 1] 6 [1, 0, 2] := by
  have greedy : mkchange3 [4, 3, 1] 6 = [1, 0, 2] := by decide
  have best := mkchange_spec currency431 6 [0, 2, 0] (by decide)
  refine ⟨greedy ▸ mkchange3_lexMaximum currency431 6, best, ?_⟩
  intro h
  have wrong := h.2 [0, 2, 0] best.1
  contradiction

theorem lexical_reference : lexicalChoice [4, 3, 1] 6 = some [1, 0, 2] := by
  rw [lexicalChoice_eq_greedy currency431]
  rfl

-- Finite checked enumeration at54 requires deeper proof elaboration, not native evaluation.
set_option maxRecDepth 4096 in
theorem first_and_last_ties :
    mkchange [7, 3, 1] 54 = some [6, 4, 0] ∧
      mkchangeStrict [7, 3, 1] 54 = some [7, 1, 2] := by decide

theorem distinct_minimizers : MinCoins [7, 3, 1] 54 [6, 4, 0] ∧
    MinCoins [7, 3, 1] 54 [7, 1, 2] ∧
    count [6, 4, 0] = count [7, 1, 2] ∧ ([6, 4, 0] : List Nat) ≠ [7, 1, 2] := by
  exact ⟨mkchange_spec currency731 54 _ first_and_last_ties.1,
    mkchangeStrict_spec currency731 54 _ first_and_last_ties.2,
    mkchange_variant_count_eq currency731 54 _ _ first_and_last_ties.1 first_and_last_ties.2,
    by decide⟩

theorem tie_positions : FirstMinimum count (mktuples [7, 3, 1] 54) [6, 4, 0] ∧
    LastMinimum count (mktuples [7, 3, 1] 54) [7, 1, 2] :=
  ⟨(mkchange_firstMinimum _ _ _).mp first_and_last_ties.1,
    (mkchangeStrict_lastMinimum _ _ _).mp first_and_last_ties.2⟩

theorem descending_tie : mkchangeDescending [7, 3, 1] 54 = some [7, 1, 2] := by
  rw [mkchangeDescending_eq_strict]
  exact first_and_last_ties.2

theorem only_greatest_tie_is_lexical : LexMaximumTuple [7, 3, 1] 54 [7, 1, 2] ∧
    ¬ LexMaximumTuple [7, 3, 1] 54 [6, 4, 0] := by
  have he : mkchange3 [7, 3, 1] 54 = [7, 1, 2] := by decide
  have hg := he ▸ mkchange3_lexMaximum currency731 54
  refine ⟨hg, ?_⟩
  intro h
  have wrong := lexMaximum_unique h hg
  contradiction

theorem decreasing_bridge : IsTuple [4, 3, 1] 6 [1, 0, 2] := by
  have h : ValidDenominations [4, 3, 1] := by decide
  have he : mkchange3 [4, 3, 1] 6 = [1, 0, 2] := by decide
  exact he ▸ greedy_feasible_decreasing h 6

theorem alignment_matters : amount [2, 1] [3] = 6 ∧ ¬ Represents [2, 1] [3] 6 := by
  refine ⟨rfl, ?_⟩
  rw [represents_iff_amount]
  decide

/-- These total evaluations lie outside both positive-unit source domains. -/
theorem outside_domain :
    mkchange3 [] 3 = [] ∧ mkchange3 [0, 1] 6 = [0, 6] ∧ mkchange3 [2] 3 = [1] ∧
    ¬ Currency [] ∧ ¬ Currency [0, 1] ∧ ¬ Currency [2] := by
  simp only [currency_iff_positive_last]
  decide

theorem empty_selections : mkchange [] 6 = none ∧ mkchangeStrict [] 6 = none ∧
    mkchangeDescending [] 6 = none := by
  exact ⟨rfl, rfl, rfl⟩

end Examples.CoinChoice

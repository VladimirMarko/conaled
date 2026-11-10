import Applications.Floating.Observation

/-!
# Limits of transporting exact algebra to rounded arithmetic

These finite witnesses execute the pinned logical binary64/binary32 models.
They retain the source's exact finite inputs and distinguish decoded results.
They do not contradict associative-fold theorems under their stated hypotheses,
nor assert native hardware adequacy or unrestricted comparison nontransitivity.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.FloatingAlgebraLimits

open Floating.Observation

def reassociation64 : List Float := [9007199254740992, 1, -9007199254740992]
def reassociation32 : List Float32 := [16777216, 1, -16777216]

theorem reassociation64_inputs :
    reassociation64.map decode64 =
      [some 9007199254740992, some 1, some (-9007199254740992)] := by
  decide +kernel

theorem reassociation32_inputs :
    reassociation32.map decode32 = [some 16777216, some 1, some (-16777216)] := by
  decide +kernel

theorem association64_values :
    decode64 (((9007199254740992 : Float) + 1) + (-9007199254740992)) = some 0 ∧
    decode64 ((9007199254740992 : Float) + (1 + (-9007199254740992))) = some 1 := by
  decide +kernel

theorem association32_values :
    decode32 (((16777216 : Float32) + 1) + (-16777216)) = some 0 ∧
    decode32 ((16777216 : Float32) + (1 + (-16777216))) = some 1 := by
  decide +kernel

theorem folds64_values :
    decode64 (List.foldl (fun a b : Float => a + b) 0 reassociation64) = some 0 ∧
    decode64 (List.foldr (fun a b : Float => a + b) 0 reassociation64) = some 1 := by
  decide +kernel

theorem folds32_values :
    decode32 (List.foldl (fun a b : Float32 => a + b) 0 reassociation32) = some 0 ∧
    decode32 (List.foldr (fun a b : Float32 => a + b) 0 reassociation32) = some 1 := by
  decide +kernel

theorem addition64_not_associative :
    ¬ (∀ a b c : Float, (a + b) + c = a + (b + c)) := by
  intro h
  have he := congrArg decode64 (h 9007199254740992 1 (-9007199254740992))
  rw [association64_values.1, association64_values.2] at he
  cases he

theorem addition32_not_associative :
    ¬ (∀ a b c : Float32, (a + b) + c = a + (b + c)) := by
  intro h
  have he := congrArg decode32 (h 16777216 1 (-16777216))
  rw [association32_values.1, association32_values.2] at he
  cases he

theorem folds64_not_equal :
    List.foldl (fun a b : Float => a + b) 0 reassociation64 ≠
      List.foldr (fun a b : Float => a + b) 0 reassociation64 := by
  intro h
  have he := congrArg decode64 h
  rw [folds64_values.1, folds64_values.2] at he
  cases he

theorem folds32_not_equal :
    List.foldl (fun a b : Float32 => a + b) 0 reassociation32 ≠
      List.foldr (fun a b : Float32 => a + b) 0 reassociation32 := by
  intro h
  have he := congrArg decode32 h
  rw [folds32_values.1, folds32_values.2] at he
  cases he

theorem difference64_inputs :
    ([9007199254740994, 1, 9007199254740992, 0] : List Float).map decode64 =
      [some 9007199254740994, some 1, some 9007199254740992, some 0] := by
  decide +kernel

theorem difference32_inputs :
    ([16777218, 1, 16777216, 0] : List Float32).map decode32 =
      [some 16777218, some 1, some 16777216, some 0] := by
  decide +kernel

theorem difference64_values :
    decode64 ((9007199254740994 : Float) - 1) = some 9007199254740992 ∧
    decode64 ((9007199254740992 : Float) - 0) = some 9007199254740992 ∧
    decode64 ((9007199254740994 : Float) - 9007199254740992) = some 2 ∧
    decode64 ((1 : Float) - 0) = some 1 := by
  decide +kernel

theorem difference32_values :
    decode32 ((16777218 : Float32) - 1) = some 16777216 ∧
    decode32 ((16777216 : Float32) - 0) = some 16777216 ∧
    decode32 ((16777218 : Float32) - 16777216) = some 2 ∧
    decode32 ((1 : Float32) - 0) = some 1 := by
  decide +kernel

theorem difference64_comparisons :
    (9007199254740994 : Float) - 1 ≤ (9007199254740992 : Float) - 0 ∧
    ¬ ((9007199254740994 : Float) - 9007199254740992 ≤ (1 : Float) - 0) := by
  decide +kernel

theorem difference32_comparisons :
    (16777218 : Float32) - 1 ≤ (16777216 : Float32) - 0 ∧
    ¬ ((16777218 : Float32) - 16777216 ≤ (1 : Float32) - 0) := by
  decide +kernel

theorem difference64_rearrangement_fails :
    ¬ (∀ x y x' y' : Float, x - y ≤ x' - y' ↔ x - x' ≤ y - y') := by
  intro h
  exact difference64_comparisons.2
    ((h 9007199254740994 1 9007199254740992 0).mp difference64_comparisons.1)

theorem difference32_rearrangement_fails :
    ¬ (∀ x y x' y' : Float32, x - y ≤ x' - y' ↔ x - x' ≤ y - y') := by
  intro h
  exact difference32_comparisons.2
    ((h 16777218 1 16777216 0).mp difference32_comparisons.1)

theorem rational_fold_values (b : Rat) :
    List.foldl (fun a c : Rat => a + c) 0 [b, 1, -b] = 1 ∧
    List.foldr (fun a c : Rat => a + c) 0 [b, 1, -b] = 1 := by
  simp only [List.foldl, List.foldr]
  constructor <;> grind

theorem rational_difference_comparisons (b : Rat) :
    ¬ (b + 2 - 1 ≤ b - 0) ∧ ¬ (b + 2 - b ≤ (1 : Rat) - 0) := by
  constructor <;> grind

theorem nan64_not_reflexive :
    decode64 ((0 : Float) / 0) = none ∧ ¬ ((0 : Float) / 0 ≤ (0 : Float) / 0) := by
  decide +kernel

theorem nan32_not_reflexive :
    decode32 ((0 : Float32) / 0) = none ∧ ¬ ((0 : Float32) / 0 ≤ (0 : Float32) / 0) := by
  decide +kernel

theorem signed_zero64_not_antisymmetric :
    decode64 (0 : Float) = some 0 ∧ decode64 (-(0 : Float)) = some 0 ∧
    (0 : Float) ≤ -(0 : Float) ∧ -(0 : Float) ≤ (0 : Float) ∧
    (0 : Float) ≠ -(0 : Float) := by
  decide +kernel

theorem signed_zero32_not_antisymmetric :
    decode32 (0 : Float32) = some 0 ∧ decode32 (-(0 : Float32)) = some 0 ∧
    (0 : Float32) ≤ -(0 : Float32) ∧ -(0 : Float32) ≤ (0 : Float32) ∧
    (0 : Float32) ≠ -(0 : Float32) := by
  decide +kernel

end Examples.FloatingAlgebraLimits

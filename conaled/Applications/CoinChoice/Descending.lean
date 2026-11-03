import Applications.CoinChoice.Selection

/-! The descending source generator is recursive; reversal is a proved property. -/
set_option autoImplicit false
set_option warningAsError true
namespace Applications.CoinChoice
open Optimization Optimization.Thinning

def downFrom : Nat → List Nat
  | 0 => [0]
  | m + 1 => (m + 1) :: downFrom m

theorem downFrom_eq_reverse_range (m : Nat) : downFrom m = (List.range (m + 1)).reverse := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [downFrom, ih, List.range_succ (n := m + 1), List.reverse_append]
    rfl

def mktuples3 : List Nat → Nat → List (List Nat)
  | [], _ => []
  | d :: ds, n =>
    if d = 1 ∧ ds = [] then [[n]]
    else (downFrom (n / d)).flatMap fun c =>
      (mktuples3 ds (n - c * d)).flatMap fun cs => [c :: cs]

theorem mktuples3_unit (n : Nat) : mktuples3 [1] n = [[n]] := by simp [mktuples3]

theorem mktuples3_cons (d n : Nat) (ds : List Nat) (hne : ds ≠ []) :
    mktuples3 (d :: ds) n = (downFrom (n / d)).flatMap
      (fun c => (mktuples3 ds (n - c * d)).map (c :: ·)) := by
  simp only [mktuples3, hne, and_false, ↓reduceIte, ← List.map_eq_flatMap]

theorem mktuples3_eq_reverse (ds : List Nat) (n : Nat) :
    mktuples3 ds n = (mktuples ds n).reverse := by
  induction ds generalizing n with
  | nil => rfl
  | cons d ds ih =>
    simp only [mktuples3, mktuples]
    split
    · rfl
    · simp only [ih, downFrom_eq_reverse_range, ← List.map_eq_flatMap, List.reverse_flatMap,
        List.map_reverse, Function.comp_def]

theorem mktuples3_perm (ds : List Nat) (n : Nat) :
    (mktuples3 ds n).Perm (mktuples ds n) := by
  rw [mktuples3_eq_reverse]
  exact List.reverse_perm _

theorem mktuples3_length (ds : List Nat) (n : Nat) :
    (mktuples3 ds n).length = (mktuples ds n).length := by
  rw [mktuples3_eq_reverse, List.length_reverse]

theorem mem_mktuples3 {ds : List Nat} (hds : Currency ds) (n : Nat) (cs : List Nat) :
    cs ∈ mktuples3 ds n ↔ Represents ds cs n := by
  rw [mktuples3_eq_reverse, List.mem_reverse, mem_mktuples_iff hds]

def mkchangeDescending (ds : List Nat) (n : Nat) : Option (List Nat) :=
  argmin count (mktuples3 ds n)

theorem mkchangeDescending_eq_strict (ds : List Nat) (n : Nat) :
    mkchangeDescending ds n = mkchangeStrict ds n := by
  rw [mkchangeDescending, mkchangeStrict, argminLast, mktuples3_eq_reverse]

theorem mkchangeDescending_spec {ds : List Nat} (hds : Currency ds) (n : Nat)
    (cs : List Nat) (he : mkchangeDescending ds n = some cs) : MinCoins ds n cs := by
  rw [mkchangeDescending_eq_strict] at he
  exact mkchangeStrict_spec hds n cs he

theorem mkchangeDescending_firstMinimum (ds : List Nat) (n : Nat) (cs : List Nat) :
    mkchangeDescending ds n = some cs ↔ FirstMinimum count (mktuples3 ds n) cs :=
  argmin_eq_some_iff_firstMinimum _ _ _

theorem mkchangeDescending_exists {ds : List Nat} (hds : Currency ds) (n : Nat) :
    ∃ cs, mkchangeDescending ds n = some cs ∧ MinCoins ds n cs := by
  rw [mkchangeDescending_eq_strict]
  exact mkchangeStrict_exists hds n

end Applications.CoinChoice

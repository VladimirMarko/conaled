import Applications.Optimization.Thinning
import Mathlib.Data.List.Lex

/-! Aligned coin positions, ascending enumerators, and direct lexicographic greedy change. -/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.CoinChoice

/-- Independent sufficient domain: positive positions, ending in the unit coin. -/
inductive Currency : List Nat → Prop where
  | unit : Currency [1]
  | cons {d : Nat} {ds : List Nat} : 0 < d → Currency ds → Currency (d :: ds)

/-- Independent aligned weighted-value relation; no algorithm appears here. -/
inductive Represents : List Nat → List Nat → Nat → Prop where
  | nil : Represents [] [] 0
  | cons {d c r : Nat} {ds cs : List Nat} :
      Represents ds cs r → Represents (d :: ds) (c :: cs) (d * c + r)

/-- Actual source amount retains zipWith truncation; alignment is separate. -/
def amount (ds cs : List Nat) : Nat := (List.zipWith Nat.mul ds cs).sum

/-- Source coin-count objective, not an execution counter. -/
def count (cs : List Nat) : Nat := cs.sum

abbrev LexLE (xs ys : List Nat) : Prop := xs ≤ ys

theorem lexLE_iff (xs ys : List Nat) : LexLE xs ys ↔ xs = ys ∨ List.Lex Nat.lt xs ys :=
  le_iff_eq_or_lt

def LexMaximumTuple (ds : List Nat) (n : Nat) (cs : List Nat) : Prop :=
  Represents ds cs n ∧ ∀ ys, Represents ds ys n → LexLE ys cs

def MinCoins (ds : List Nat) (n : Nat) (cs : List Nat) : Prop :=
  Represents ds cs n ∧ ∀ ys, Represents ds ys n → cs.sum ≤ ys.sum

theorem currency_nonempty {ds : List Nat} (h : Currency ds) : ds ≠ [] := by
  cases h <;> simp

theorem currency_iff_positive_prefix_unit (ds : List Nat) :
    Currency ds ↔ ∃ pre, ds = pre ++ [1] ∧ ∀ d ∈ pre, 0 < d := by
  constructor
  · intro h
    induction h with
    | unit => exact ⟨[], rfl, by simp⟩
    | @cons d ds hd _ ih =>
      obtain ⟨pre, he, hp⟩ := ih
      refine ⟨d :: pre, by simp [he], ?_⟩
      intro e hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hd
      · exact hp e hm
  · rintro ⟨pre, rfl, hp⟩
    induction pre with
    | nil => exact .unit
    | cons d pre ih =>
      exact .cons (hp d (by simp)) (ih (fun e he => hp e (by simp [he])))

theorem currency_positive {ds : List Nat} (h : Currency ds) {d : Nat}
    (hd : d ∈ ds) : 0 < d := by
  induction h with
  | unit =>
    have he : d = 1 := by simpa using hd
    subst d
    decide
  | cons he _ ih =>
    rcases List.mem_cons.mp hd with rfl | hd
    · exact he
    · exact ih hd

theorem represents_length {ds cs : List Nat} {n : Nat} (h : Represents ds cs n) :
    cs.length = ds.length := by
  induction h <;> simp_all

theorem represents_amount {ds cs : List Nat} {n : Nat}
    (h : Represents ds cs n) : amount ds cs = n := by
  induction h <;> simp_all [amount]

theorem represents_iff_amount (ds cs : List Nat) (n : Nat) :
    Represents ds cs n ↔ cs.length = ds.length ∧ amount ds cs = n := by
  constructor
  · intro h
    exact ⟨represents_length h, represents_amount h⟩
  · induction ds generalizing cs n with
    | nil =>
      intro h
      have hc : cs = [] := List.length_eq_zero_iff.mp (by simpa using h.1)
      subst cs
      have hn : n = 0 := by simpa [amount] using h.2.symm
      subst n
      exact .nil
    | cons d ds ih =>
      rintro ⟨hl, ha⟩
      cases cs with
      | nil => simp at hl
      | cons c cs =>
        have ht : Represents ds cs (amount ds cs) :=
          ih cs (amount ds cs) ⟨by simpa using hl, rfl⟩
        have hn : d * c + amount ds cs = n := by simpa [amount] using ha
        exact hn ▸ Represents.cons ht

theorem represents_unit (cs : List Nat) (n : Nat) :
    Represents [1] cs n ↔ cs = [n] := by
  rw [represents_iff_amount]
  cases cs with
  | nil => simp
  | cons c cs =>
    cases cs with
    | nil => simp [amount]
    | cons e es => simp

theorem lexLE_refl (cs : List Nat) : LexLE cs cs := le_rfl

theorem lexLE_antisymm {cs xs : List Nat} (h : LexLE cs xs) (h' : LexLE xs cs) :
    cs = xs := le_antisymm h h'

theorem lexMaximum_unique {ds cs xs : List Nat} {n : Nat}
    (hc : LexMaximumTuple ds n cs) (hx : LexMaximumTuple ds n xs) : cs = xs :=
  lexLE_antisymm (hx.2 cs hc.1) (hc.2 xs hx.1)

/-! ## Both actual ascending source generators -/

def mktuples : List Nat → Nat → List (List Nat)
  | [], _ => []
  | d :: ds, n =>
    if d = 1 ∧ ds = [] then [[n]]
    else (List.range (n / d + 1)).flatMap (fun c =>
      (mktuples ds (n - c * d)).flatMap (fun cs => [c :: cs]))

def mktuples2 : List Nat → Nat → List (List Nat)
  | [], _ => []
  | d :: ds, n =>
    if d = 1 ∧ ds = [] then [[n]]
    else (List.range (n / d + 1)).flatMap (fun c =>
      (mktuples2 ds (n - c * d)).map (fun cs => c :: cs))

theorem mktuples_nil (n : Nat) : mktuples [] n = [] := rfl

theorem mktuples_unit (n : Nat) : mktuples [1] n = [[n]] := by simp [mktuples]

theorem mktuples_cons (d n : Nat) (ds : List Nat) (h : ¬ (d = 1 ∧ ds = [])) :
    mktuples (d :: ds) n = (List.range (n / d + 1)).flatMap (fun c =>
      (mktuples ds (n - c * d)).flatMap (fun cs => [c :: cs])) := by
  rw [mktuples, ite_eq_right h]

/-- Exact ordered equality on all totalized inputs, retaining every occurrence. -/
theorem mktuples2_eq_mktuples (ds : List Nat) (n : Nat) :
    mktuples2 ds n = mktuples ds n := by
  induction ds generalizing n with
  | nil => rfl
  | cons d ds ih =>
    rw [mktuples2, mktuples]
    split
    · rfl
    · congr 1
      funext c
      rw [ih]
      exact List.map_eq_flatMap

theorem feasible_leading_count_bound {d c n : Nat} {ds cs : List Nat}
    (hd : 0 < d) (h : Represents (d :: ds) (c :: cs) n) : c ≤ n / d := by
  cases h with
  | cons _ =>
    apply (Nat.le_div_iff_mul_le hd).2
    rw [Nat.mul_comm]
    omega

theorem feasible_residual {d c n : Nat} {ds cs : List Nat}
    (h : Represents (d :: ds) (c :: cs) n) : Represents ds cs (n - c * d) := by
  cases h with
  | cons h => simpa [Nat.mul_comm] using h

theorem quotient_residual (d n : Nat) (hd : 0 < d) :
    n / d * d + (n - n / d * d) = n ∧ n - n / d * d < d := by
  constructor
  · have h := Nat.div_mul_le_self n d
    omega
  · rw [← Nat.mod_eq_sub_div_mul]
    exact Nat.mod_lt n hd

/-- Every independently feasible aligned tuple occurs, and every output is feasible. -/
theorem mem_mktuples_iff {ds : List Nat} (hds : Currency ds) (n : Nat)
    (cs : List Nat) : cs ∈ mktuples ds n ↔ Represents ds cs n := by
  induction hds generalizing n cs with
  | unit => simp [mktuples_unit, represents_unit]
  | @cons d ds hd hds ih =>
    rw [mktuples_cons d n ds (by simp [currency_nonempty hds])]
    constructor
    · intro hm
      obtain ⟨c, hc, hm⟩ := List.mem_flatMap.mp hm
      obtain ⟨tail, ht, he⟩ := List.mem_flatMap.mp hm
      have he' : cs = c :: tail := by simpa using he
      subst cs
      have hc' : c ≤ n / d := by
        have hh := List.mem_range.mp hc
        omega
      have hmul := (Nat.le_div_iff_mul_le hd).1 hc'
      have ht' := (ih (n - c * d) tail).mp ht
      have hn : d * c + (n - c * d) = n := by rw [Nat.mul_comm]; omega
      exact hn ▸ Represents.cons ht'
    · intro hr
      cases cs with
      | nil => cases hr
      | cons c cs =>
        have hc := feasible_leading_count_bound hd hr
        have ht := feasible_residual hr
        apply List.mem_flatMap.mpr
        refine ⟨c, List.mem_range.mpr (by omega), ?_⟩
        apply List.mem_flatMap.mpr
        exact ⟨cs, (ih (n - c * d) cs).mpr ht, by simp⟩

theorem mem_mktuples2_iff {ds : List Nat} (hds : Currency ds) (n : Nat)
    (cs : List Nat) : cs ∈ mktuples2 ds n ↔ Represents ds cs n := by
  rw [mktuples2_eq_mktuples]
  exact mem_mktuples_iff hds n cs

theorem mem_mktuples_length {ds cs : List Nat} {n : Nat} (hds : Currency ds)
    (hm : cs ∈ mktuples ds n) : cs.length = ds.length :=
  represents_length ((mem_mktuples_iff hds n cs).mp hm)

/-! ## Actual direct quotient/residual algorithm and independent global optimum -/

def mkchange3 : List Nat → Nat → List Nat
  | [], _ => []
  | d :: ds, n =>
    if d = 1 ∧ ds = [] then [n]
    else
      let c := n / d
      c :: mkchange3 ds (n - c * d)

theorem mkchange3_nil (n : Nat) : mkchange3 [] n = [] := rfl

theorem mkchange3_unit (n : Nat) : mkchange3 [1] n = [n] := by simp [mkchange3]

theorem mkchange3_cons (d n : Nat) (ds : List Nat) (h : ¬ (d = 1 ∧ ds = [])) :
    mkchange3 (d :: ds) n =
      let c := n / d
      c :: mkchange3 ds (n - c * d) := by
  rw [mkchange3, ite_eq_right h]

/-- Cardinality on all totalized inputs; this is not a runtime bound. -/
theorem mkchange3_length (ds : List Nat) (n : Nat) :
    (mkchange3 ds n).length = ds.length := by
  induction ds generalizing n with
  | nil => rfl
  | cons d ds ih =>
    rw [mkchange3]
    split
    · rename_i h
      rcases h with ⟨rfl, rfl⟩
      rfl
    · simp [ih]

theorem mkchange3_represents {ds : List Nat} (hds : Currency ds) (n : Nat) :
    Represents ds (mkchange3 ds n) n := by
  induction hds generalizing n with
  | unit => exact (represents_unit _ _).mpr (mkchange3_unit n)
  | @cons d ds hd hds ih =>
    rw [mkchange3_cons d n ds (by simp [currency_nonempty hds])]
    have ht := Represents.cons (d := d) (c := n / d) (ih (n - n / d * d))
    have hn : d * (n / d) + (n - n / d * d) = n := by
      simpa [Nat.mul_comm] using (quotient_residual d n hd).1
    simpa only [hn] using ht

/-- Direct proof over all independent feasible tuples; no enumeration in the proof goal. -/
theorem mkchange3_lex_upper {ds : List Nat} (hds : Currency ds) (n : Nat)
    (cs : List Nat) (hr : Represents ds cs n) : LexLE cs (mkchange3 ds n) := by
  induction hds generalizing n cs with
  | unit =>
    have hc := (represents_unit cs n).mp hr
    rw [hc, mkchange3_unit]
  | @cons d ds hd hds ih =>
    rw [mkchange3_cons d n ds (by simp [currency_nonempty hds])]
    change LexLE cs (n / d :: mkchange3 ds (n - n / d * d))
    rw [lexLE_iff]
    cases cs with
    | nil => cases hr
    | cons c cs =>
      have hc := feasible_leading_count_bound hd hr
      have ht := feasible_residual hr
      by_cases he : c = n / d
      · have hi := ih (n - c * d) cs ht
        rcases (lexLE_iff _ _).mp hi with hi | hi
        · exact Or.inl (by simp [he] at hi ⊢; exact hi)
        · exact Or.inr (he ▸ List.Lex.cons hi)
      · have hlt : c < n / d := by omega
        exact Or.inr (List.Lex.rel hlt)

theorem mkchange3_lexMaximum {ds : List Nat} (hds : Currency ds) (n : Nat) :
    LexMaximumTuple ds n (mkchange3 ds n) :=
  ⟨mkchange3_represents hds n, fun cs hr => mkchange3_lex_upper hds n cs hr⟩

theorem eq_mkchange3_of_lexMaximum {ds cs : List Nat} {n : Nat} (hds : Currency ds)
    (h : LexMaximumTuple ds n cs) : cs = mkchange3 ds n :=
  lexMaximum_unique h (mkchange3_lexMaximum hds n)

theorem lexMaximum_iff_eq_mkchange3 {ds : List Nat} (hds : Currency ds) (n : Nat)
    (cs : List Nat) : LexMaximumTuple ds n cs ↔ cs = mkchange3 ds n := by
  constructor
  · exact eq_mkchange3_of_lexMaximum hds
  · rintro rfl
    exact mkchange3_lexMaximum hds n

theorem mkchange3_mem_mktuples {ds : List Nat} (hds : Currency ds) (n : Nat) :
    mkchange3 ds n ∈ mktuples ds n :=
  (mem_mktuples_iff hds n _).mpr (mkchange3_represents hds n)

theorem mktuples_nonempty {ds : List Nat} (hds : Currency ds) (n : Nat) :
    mktuples ds n ≠ [] := by
  have hm := mkchange3_mem_mktuples hds n
  intro he
  simp [he] at hm

theorem mktuples_zero {ds : List Nat} (hds : Currency ds) :
    mktuples ds 0 = [List.replicate ds.length 0] := by
  induction hds with
  | unit => simp [mktuples_unit]
  | @cons d ds _ hds ih =>
    rw [mktuples_cons d 0 ds (by simp [currency_nonempty hds])]
    simp [ih, List.replicate_succ]

theorem mkchange3_zero {ds : List Nat} (hds : Currency ds) :
    mkchange3 ds 0 = List.replicate ds.length 0 := by
  induction hds with
  | unit => simp [mkchange3_unit]
  | @cons d ds _ hds ih =>
    rw [mkchange3_cons d 0 ds (by simp [currency_nonempty hds])]
    simp [ih, List.replicate_succ]

def usds : List Nat := [100, 50, 25, 10, 5, 1]
def ukds : List Nat := [200, 100, 50, 20, 10, 5, 2, 1]

theorem usds_currency : Currency usds :=
  (currency_iff_positive_prefix_unit usds).mpr ⟨[100,50,25,10,5], rfl, by decide⟩

theorem ukds_currency : Currency ukds :=
  (currency_iff_positive_prefix_unit ukds).mpr ⟨[200,100,50,20,10,5,2], rfl, by decide⟩


end Applications.CoinChoice

import Applications.CoinChoice.Basic

/-! Bridges from the decreasing-currency source presentation to the shared semantics. -/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.CoinChoice

/-- Source dot product, including its unmatched-list truncation extension. -/
def weightedSum : List Nat → List Nat → Nat
  | d :: ds, c :: cs => d * c + weightedSum ds cs
  | _, _ => 0

/-- The source's second semantic presentation retains an explicit alignment condition. -/
def IsTuple (ds : List Nat) (n : Nat) (cs : List Nat) : Prop :=
  cs.length = ds.length ∧ weightedSum ds cs = n

instance (ds cs : List Nat) (n : Nat) : Decidable (IsTuple ds n cs) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Strictly decreasing source currencies form a subdomain of `Currency`. -/
def ValidDenominations (ds : List Nat) : Prop :=
  ds.Pairwise (fun d e => e < d) ∧ (∀ d ∈ ds, 0 < d) ∧ ds.getLast? = some 1

instance (ds : List Nat) : Decidable (ValidDenominations ds) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem amount_eq_weightedSum (ds cs : List Nat) : amount ds cs = weightedSum ds cs := by
  induction ds generalizing cs with
  | nil => simp [amount, weightedSum]
  | cons d ds ih =>
    cases cs with
    | nil => simp [amount, weightedSum]
    | cons c cs => simpa [amount, weightedSum] using congrArg (d * c + ·) (ih cs)

theorem isTuple_iff_represents (ds cs : List Nat) (n : Nat) :
    IsTuple ds n cs ↔ Represents ds cs n := by
  rw [represents_iff_amount, amount_eq_weightedSum]
  rfl

theorem currency_iff_positive_last (ds : List Nat) :
    Currency ds ↔ (∀ d ∈ ds, 0 < d) ∧ ds.getLast? = some 1 := by
  constructor
  · intro h
    refine ⟨fun d hd => currency_positive h hd, ?_⟩
    induction h with
    | unit => rfl
    | cons _ _ ih => simp [List.getLast?_cons, ih]
  · intro h
    induction ds with
    | nil => simp at h
    | cons d ds ih =>
      cases ds with
      | nil =>
        have hd : d = 1 := by simpa using h.2
        subst d
        exact .unit
      | cons e es =>
        exact .cons (h.1 d (by simp))
          (ih ⟨fun x hx => h.1 x (List.mem_cons_of_mem d hx), by simpa using h.2⟩)

theorem valid_iff (ds : List Nat) :
    ValidDenominations ds ↔ ds.Pairwise (fun d e => e < d) ∧ Currency ds := by
  rw [currency_iff_positive_last]
  rfl

theorem ValidDenominations.currency {ds : List Nat} (h : ValidDenominations ds) :
    Currency ds := (valid_iff ds).mp h |>.2

/-- Exact equivalence of the two independently written lexical objectives. -/
theorem lexical_presentation_iff (ds cs : List Nat) (n : Nat) :
    (IsTuple ds n cs ∧ ∀ ys, IsTuple ds n ys → cs = ys ∨ List.Lex Nat.lt ys cs) ↔
      LexMaximumTuple ds n cs := by
  simp only [isTuple_iff_represents, LexMaximumTuple, lexLE_iff, eq_comm]

/-- Exact equivalence of the two independently written coin-count objectives. -/
theorem minimum_presentation_iff (ds cs : List Nat) (n : Nat) :
    (IsTuple ds n cs ∧ ∀ ys, IsTuple ds n ys → count cs ≤ count ys) ↔ MinCoins ds n cs := by
  simp only [isTuple_iff_represents, MinCoins, count]

/-- The second source reverses the conjunction in the unit test, leaving the recurrence exact. -/
theorem mktuples_decreasing_equation (d n : Nat) (ds : List Nat) :
    mktuples (d :: ds) n =
      if ds = [] ∧ d = 1 then [[n]] else
        (List.range (n / d + 1)).flatMap (fun c =>
          (mktuples ds (n - c * d)).flatMap (fun cs => [c :: cs])) := by
  rw [mktuples]
  simp only [and_comm]

theorem mktuples2_decreasing_equation (d n : Nat) (ds : List Nat) :
    mktuples2 (d :: ds) n =
      if ds = [] ∧ d = 1 then [[n]] else
        (List.range (n / d + 1)).flatMap (fun c =>
          (mktuples2 ds (n - c * d)).map (fun cs => c :: cs)) := by
  rw [mktuples2]
  simp only [and_comm]

theorem greedy_decreasing_equation (d n : Nat) (ds : List Nat) :
    mkchange3 (d :: ds) n =
      if ds = [] ∧ d = 1 then [n] else n / d :: mkchange3 ds (n - n / d * d) := by
  rw [mkchange3]
  simp only [and_comm]

theorem mem_mktuples_decreasing {ds : List Nat} (h : ValidDenominations ds)
    (n : Nat) (cs : List Nat) : cs ∈ mktuples ds n ↔ IsTuple ds n cs := by
  rw [isTuple_iff_represents, mem_mktuples_iff h.currency]

theorem greedy_feasible_decreasing {ds : List Nat} (h : ValidDenominations ds) (n : Nat) :
    IsTuple ds n (mkchange3 ds n) :=
  (isTuple_iff_represents _ _ _).mpr (mkchange3_represents h.currency n)

end Applications.CoinChoice

import Applications.Resources.RandomAccess.Lookup
import Applications.Resources.BinaryCounter.Decrement

/-! Finite end-operation accounting from checkpoint 233.
Provenance, source domains and statement review:
`docs/research/adwh-random-access-end-costs.md`. -/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RandomAccessCosts
open RandomAccess
universe u
variable {α : Type u}

def ones : RAList α → Nat
  | [] => 0
  | .zero :: ds => ones ds
  | .one _ :: ds => ones ds + 1

def zeros : RAList α → Nat
  | [] => 0
  | .zero :: ds => zeros ds + 1
  | .one _ :: ds => zeros ds

theorem ones_add_zeros (ds : RAList α) : ones ds + zeros ds = ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih => cases d <;> simp only [ones, zeros, List.length_cons] <;> omega

/-- The printed binary increment is exactly the digit skeleton of consT. -/
def bits : RAList α → BinaryCounter.Bits
  | [] => []
  | .zero :: ds => false :: bits ds
  | .one _ :: ds => true :: bits ds

theorem bits_consT (t : Tree α) (ds : RAList α) :
    bits (consT t ds) = BinaryCounter.inc (bits ds) := by
  induction ds generalizing t with
  | nil => rfl
  | cons d ds ih => cases d <;> simp [consT, bits, BinaryCounter.inc, ih]

theorem bits_length (ds : RAList α) : (bits ds).length = ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih => cases d <;> simp [bits, ih]

theorem bits_canonical {r : Nat} {ds : RAList α} (h : Valid r ds) :
    BinaryCounter.Canonical (bits ds) := by
  induction h with
  | nil r => trivial
  | @zero r ds hne h ih =>
    have hn : bits ds ≠ [] := by
      intro he
      have hh := bits_length ds
      rw [he] at hh
      exact hne (List.length_eq_zero_iff.mp hh.symm)
    simpa [bits, BinaryCounter.Canonical, hn] using ih
  | @one r t ds ht h ih =>
    by_cases he : ds = []
    · subst ds; simp [bits, BinaryCounter.Canonical]
    · have hn : bits ds ≠ [] := by
        intro hz
        have hh := bits_length ds
        rw [hz] at hh
        exact he (List.length_eq_zero_iff.mp hh.symm)
      simpa [bits, BinaryCounter.Canonical, hn] using ih

theorem bits_value {r : Nat} {ds : RAList α} (h : Valid r ds) :
    (fromRA ds).length = 2 ^ r * BinaryCounter.value (bits ds) := by
  induction h with
  | nil r => simp [fromRA, bits, BinaryCounter.value]
  | @zero r ds hne h ih =>
    simp only [fromRA, bits, BinaryCounter.value, Nat.pow_succ] at *
    grind
  | @one r t ds ht h ih =>
    simp only [fromRA, List.length_append, fromT_length ht, bits, BinaryCounter.value,
      Nat.pow_succ] at *
    grind

def consTRun (t : Tree α) : RAList α → RAList α × Nat
  | [] => ([.one t], 1)
  | .zero :: ds => (.one t :: ds, 1)
  | .one v :: ds =>
      let next := consTRun (node t v) ds
      (.zero :: next.1, next.2 + 1)

def consRARun (x : α) (ds : RAList α) : RAList α × Nat := consTRun (.leaf x) ds

theorem consTRun_value (t : Tree α) (ds : RAList α) :
    (consTRun t ds).1 = consT t ds := by
  induction ds generalizing t with
  | nil => rfl
  | cons d ds ih => cases d <;> simp [consTRun, consT, ih]

theorem consRARun_value (x : α) (ds : RAList α) :
    (consRARun x ds).1 = consRA x ds := consTRun_value _ _

theorem consRARun_refinement (x : α) (ds : RAList α) :
    fromRA (consRARun x ds).1 = x :: fromRA ds := by
  rw [consRARun_value, fromRA_consRA]

theorem bits_ones (ds : RAList α) : BinaryCounter.ones (bits ds) = ones ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => cases d <;> simp [bits, ones, BinaryCounter.ones, ih, Nat.add_comm]

/-- Equal counts, with digit visits and counter writes retaining their distinct meanings. -/
theorem consTRun_count_bits (t : Tree α) (ds : RAList α) :
    (consTRun t ds).2 = BinaryCounter.flipCost (bits ds) := by
  induction ds generalizing t with
  | nil => rfl
  | cons d ds ih => cases d <;> simp [consTRun, bits, BinaryCounter.flipCost, ih, Nat.add_comm]

theorem consTRun_potential (t : Tree α) (ds : RAList α) :
    (consTRun t ds).2 + ones (consTRun t ds).1 = ones ds + 2 := by
  have hp := BinaryCounter.flipCost_potential (bits ds)
  rw [← bits_consT t ds, bits_ones, bits_ones, ← consTRun_count_bits t ds] at hp
  rw [consTRun_value]
  omega

theorem consTRun_count_bounds (t : Tree α) (ds : RAList α) :
    1 ≤ (consTRun t ds).2 ∧ (consTRun t ds).2 ≤ ds.length + 1 := by
  rw [consTRun_count_bits]
  constructor
  · rw [BinaryCounter.flipCost_eq_leadingOnes_add_one]; omega
  · simpa [bits_length] using BinaryCounter.flipCost_le_length_add_one (bits ds)

theorem consRARun_log_bound (x : α) {ds : RAList α} (h : Inv ds) :
    (consRARun x ds).2 ≤ (fromRA ds).length.log2 + 2 := by
  have hc := (consTRun_count_bounds (.leaf x) ds).2
  have hd := digits_log_bound h
  exact Nat.le_trans hc (by omega)

def pushManyRun (xs : List α) (ds : RAList α) : RAList α × Nat :=
  Resources.run consRARun xs ds

theorem pushManyRun_value (xs : List α) (ds : RAList α) :
    (pushManyRun xs ds).1 = xs.foldl (fun ys x => consRA x ys) ds := by
  rw [pushManyRun, Resources.run_state]
  simp only [consRARun_value]

theorem pushManyRun_potential (xs : List α) (ds : RAList α) :
    (pushManyRun xs ds).2 + ones (pushManyRun xs ds).1 = ones ds + 2 * xs.length := by
  have hs : ∀ (x : α) ds, (consRARun x ds).2 + ones (consRARun x ds).1 = ones ds + 2 :=
    fun x ds => consTRun_potential (.leaf x) ds
  simpa [pushManyRun, Resources.budget_constant] using
    Resources.run_potential_exact consRARun (fun _ _ => 2) ones hs xs ds

theorem pushManyRun_cost_lower (xs : List α) (ds : RAList α) :
    xs.length ≤ (pushManyRun xs ds).2 := by
  induction xs generalizing ds with
  | nil => simp [pushManyRun, Resources.run, pure]
  | cons x xs ih =>
    have hr := ih (consRARun x ds).1
    have hc := (consTRun_count_bounds (.leaf x) ds).1
    change xs.length + 1 ≤ (consRARun x ds).2 + (pushManyRun xs (consRARun x ds).1).2
    change 1 ≤ (consRARun x ds).2 at hc
    omega

theorem pushManyRun_empty_bounds (xs : List α) :
    xs.length ≤ (pushManyRun xs []).2 ∧ (pushManyRun xs []).2 ≤ 2 * xs.length := by
  have hp := pushManyRun_potential xs []
  simp only [ones] at hp
  exact ⟨pushManyRun_cost_lower xs [], by omega⟩

/-- Source foldr construction, evaluated in its actual tail-before-head order. -/
def toRARun (xs : List α) : Measured (RAList α) Nat := pushManyRun xs.reverse []

@[simp] theorem toRARun_nil : toRARun ([] : List α) = ([],0) := rfl

/-- Exact tail-before-head source recurrence, including the accumulated cost. -/
theorem toRARun_cons (x : α) (xs : List α) :
    toRARun (x :: xs) = bind (toRARun xs) (consRARun x) := by
  simp [toRARun, pushManyRun, List.reverse_cons, run_append, run, bind, pure]

theorem toRARun_value (xs : List α) : (toRARun xs).1 = toRA xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [toRARun_cons, bind, consRARun_value, toRA, ih]

theorem toRARun_potential (xs : List α) :
    (toRARun xs).2 + ones (toRARun xs).1 = 2 * xs.length := by
  simpa [toRARun, ones] using pushManyRun_potential xs.reverse ([] : RAList α)

theorem toRARun_linear_bound (xs : List α) : (toRARun xs).2 ≤ 2 * xs.length := by
  have hh := toRARun_potential xs
  omega

def borrowCost : RAList α → Nat
  | [] => 1
  | .one _ :: _ => 1
  | .zero :: ds => borrowCost ds + 1

def unconsTRun : RAList α → Option (Tree α × RAList α) × Nat
  | [] => (none, 1)
  | .one t :: ds => (some (t, if ds.isEmpty then [] else .zero :: ds), 1)
  | .zero :: ds =>
      let rest := unconsTRun ds
      let result := match rest.1 with
        | some (.node _ l r, ys) => some (l, .one r :: ys)
        | _ => none
      (result, rest.2 + 1)

theorem unconsTRun_exact (ds : RAList α) :
    unconsTRun ds = (unconsT ds, borrowCost ds) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    cases d with
    | one t => rfl
    | zero => simp only [unconsTRun, ih, unconsT, borrowCost]; rfl

def unconsRARun (ds : RAList α) : Option (α × RAList α) × Nat :=
  let next := unconsTRun ds
  let result := match next.1 with
    | some (.leaf x, ys) => some (x, ys)
    | _ => none
  (result, next.2)

theorem unconsRARun_exact (ds : RAList α) :
    unconsRARun ds = (unconsRA ds, borrowCost ds) := by
  simp only [unconsRARun, unconsTRun_exact, unconsRA]
  rfl

theorem borrowCost_bounds (ds : RAList α) :
    1 ≤ borrowCost ds ∧ borrowCost ds ≤ ds.length + 1 := by
  induction ds with
  | nil => simp [borrowCost]
  | cons d ds ih => cases d <;> simp only [borrowCost, List.length_cons] <;> omega

theorem unconsRARun_log_bound {ds : RAList α} (h : Inv ds) :
    (unconsRARun ds).2 ≤ (fromRA ds).length.log2 + 2 := by
  rw [unconsRARun_exact]
  have hc := (borrowCost_bounds ds).2
  have hd := digits_log_bound h
  omega

theorem unconsT_potential {r : Nat} {ds : RAList α} (h : Valid r ds)
    {t : Tree α} {ys : RAList α} (he : unconsT ds = some (t, ys)) :
    borrowCost ds + zeros ys ≤ zeros ds + 2 := by
  induction h generalizing t ys with
  | nil r => simp [unconsT] at he
  | @one r v ds hv h ih =>
    cases ds with
    | nil =>
      simp only [unconsT, List.isEmpty_nil, ↓reduceIte] at he
      have hp := Prod.mk.inj (Option.some.inj he)
      rcases hp with ⟨rfl, rfl⟩
      simp [borrowCost, zeros]
    | cons d ds =>
      simp only [unconsT, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at he
      have hp := Prod.mk.inj (Option.some.inj he)
      rcases hp with ⟨rfl, rfl⟩
      simp [borrowCost, zeros]
      omega
  | @zero r ds hne h ih =>
    obtain ⟨v, zs, hv, hp, hz, ha, hc⟩ := unconsT_spec h hne
    have hi := ih hv
    cases hp with
    | node r l s hl hs =>
      simp only [unconsT, hv] at he
      have hh := Prod.mk.inj (Option.some.inj he)
      rcases hh with ⟨rfl, rfl⟩
      simp only [borrowCost, zeros]
      omega

theorem unconsRA_potential {ds : RAList α} (h : Inv ds)
    {x : α} {ys : RAList α} (he : unconsRA ds = some (x, ys)) :
    (unconsRARun ds).2 + zeros ys ≤ zeros ds + 2 := by
  have hne : ds ≠ [] := by intro hz; subst ds; simp [unconsRA, unconsT] at he
  obtain ⟨t, zs, ht, hp, hz, ha, hc⟩ := unconsT_spec h hne
  have hh := unconsT_potential h ht
  cases hp with
  | leaf y =>
    simp only [unconsRA, ht] at he
    have hi := Prod.mk.inj (Option.some.inj he)
    rcases hi with ⟨rfl, rfl⟩
    simpa only [unconsRARun_exact] using hh

theorem bits_unconsT {r : Nat} {ds : RAList α} (h : Valid r ds)
    {t : Tree α} {ys : RAList α} (he : unconsT ds = some (t, ys)) :
    BinaryCounter.decBits (bits ds) = some (bits ys) := by
  induction h generalizing t ys with
  | nil r => simp [unconsT] at he
  | @one r v ds hv h ih =>
    cases ds with
    | nil =>
      simp only [unconsT, List.isEmpty_nil, ↓reduceIte] at he
      have hp := Prod.mk.inj (Option.some.inj he)
      rcases hp with ⟨rfl, rfl⟩
      rfl
    | cons d ds =>
      simp only [unconsT, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at he
      have hp := Prod.mk.inj (Option.some.inj he)
      rcases hp with ⟨rfl, rfl⟩
      cases d <;> rfl
  | @zero r ds hne h ih =>
    obtain ⟨v, zs, hv, hp, hz, ha, hc⟩ := unconsT_spec h hne
    have hi := ih hv
    cases hp with
    | node r l s hl hs =>
      simp only [unconsT, hv] at he
      have hh := Prod.mk.inj (Option.some.inj he)
      rcases hh with ⟨rfl, rfl⟩
      simp [bits, BinaryCounter.decBits, hi]

end Resources.RandomAccessCosts

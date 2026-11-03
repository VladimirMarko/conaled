import Applications.Search.Ordered.Threshold

set_option autoImplicit false
set_option warningAsError true
namespace OrderedSearch

/-- Actual doubling, returning a valid upper bracket and its predecessor fact. -/
def doublingUpper (f : Nat → Nat) (hf : Increasing f) (target b : Nat) (hb : 0 < b) :
    {u : Nat // b ≤ u ∧ target ≤ f u ∧ (u = b ∨ f (u / 2) < target)} :=
  if h : target ≤ f b then ⟨b, Nat.le_refl _, h, Or.inl rfl⟩
  else
    let next := doublingUpper f hf target (2 * b) (by omega)
    ⟨next.1, by have := next.2.1; omega, next.2.2.1, Or.inr (by
      rcases next.2.2.2 with heq | hprev
      · simpa [heq] using (Nat.lt_of_not_ge h)
      · exact hprev)⟩
termination_by target + 1 - b
decreasing_by have _h := hf.le_apply (x := b); omega

/-- None is the source's fictitious -1 lower sentinel. -/
structure Bracket (f : Nat → Nat) (target : Nat) where
  lower : Option Nat
  upper : Nat
  upper_hit : target ≤ f upper
  lower_miss : ∀ a, lower = some a → f a < target
  nonempty : ∀ a, lower = some a → a < upper

def bound (f : Nat → Nat) (hf : Increasing f) (target : Nat) : Bracket f target :=
  if h : target ≤ f 0 then ⟨none, 0, h, by simp, by simp⟩
  else
    let result := doublingUpper f hf target 1 (by decide)
    ⟨some (result.1 / 2), result.1, result.2.2.1, by
      intro a ha
      have he : a = result.1 / 2 := by simpa using ha.symm
      subst a
      rcases result.2.2.2 with heq | hprev
      · simpa [heq] using (Nat.lt_of_not_ge h)
      · exact hprev,
      by intro a ha; have he : a = result.1 / 2 := by simpa using ha.symm
         rw [he]; exact Nat.div_lt_self (by have := result.2.1; omega) (by decide)⟩

def LeastThreshold (f : Nat → Nat) (target result : Nat) : Prop :=
  target ≤ f result ∧ ∀ x, target ≤ f x → result ≤ x

theorem threshold_global_of_bracket (pick : Nat → Nat) (hp : ∀ n, 0 < n → pick n < n)
    (f : Nat → Nat) (hf : Increasing f) (target start upper : Nat)
    (hstart : start ≤ upper) (hupper : target ≤ f upper)
    (hbefore : ∀ x, x < start → f x < target) :
    LeastThreshold f target (lowerBoundWith pick hp f target start (upper - start)) := by
  have spec := lowerBoundWith_spec pick hp f hf.monotone target start (upper - start)
  rcases spec with ⟨hl, hu, hpre, hpost⟩
  constructor
  · by_cases he : lowerBoundWith pick hp f target start (upper - start) = upper
    · simpa [he] using hupper
    · exact hpost _ (Nat.le_refl _) (by omega)
  · intro x hx
    apply Nat.le_of_not_lt
    intro hlt
    by_cases hs : x < start
    · have := hbefore x hs; omega
    · have := hpre x (by omega) hlt; omega

/-- Recovered variant: searches from zero, without trimming the lower bracket. -/
def smallest (f : Nat → Nat) (target : Nat) (bracket : Bracket f target) : Nat :=
  lowerBound f target 0 bracket.upper

theorem smallest_spec (f : Nat → Nat) (hf : Increasing f) (target : Nat)
    (bracket : Bracket f target) : LeastThreshold f target (smallest f target bracket) := by
  simpa [smallest, lowerBound] using threshold_global_of_bracket upperPick upperPick_lt f hf
    target 0 bracket.upper (by omega) bracket.upper_hit (fun _ h => False.elim (by omega))

def bracketStart (lower : Option Nat) : Nat :=
  match lower with
  | none => 0
  | some a => a + 1

/-- Book variant: trim the known-missing lower part and use the lower midpoint. -/
def sourceSmallest (f : Nat → Nat) (target : Nat) (bracket : Bracket f target) : Nat :=
  let start := bracketStart bracket.lower
  lowerBoundWith lowerPick lowerPick_lt f target start (bracket.upper - start)

theorem sourceSmallest_spec (f : Nat → Nat) (hf : Increasing f) (target : Nat)
    (bracket : Bracket f target) : LeastThreshold f target (sourceSmallest f target bracket) := by
  apply threshold_global_of_bracket lowerPick lowerPick_lt f hf target
    (bracketStart bracket.lower) bracket.upper
  · cases h : bracket.lower with
    | none => simp [bracketStart]
    | some a => have := bracket.nonempty a h; simp only [bracketStart]; omega
  · exact bracket.upper_hit
  · intro x hx
    cases h : bracket.lower with
    | none => simp [bracketStart, h] at hx
    | some a =>
      have ha := bracket.lower_miss a h
      have hxa : x ≤ a := by simp only [bracketStart, h] at hx; omega
      have := hf.monotone hxa
      omega

theorem leastThreshold_unique (f : Nat → Nat) (target x y : Nat)
    (hx : LeastThreshold f target x) (hy : LeastThreshold f target y) : x = y := by
  exact Nat.le_antisymm (hx.2 y hy.1) (hy.2 x hx.1)

theorem smallest_eq_sourceSmallest (f : Nat → Nat) (hf : Increasing f) (target : Nat)
    (bracket : Bracket f target) : smallest f target bracket = sourceSmallest f target bracket :=
  leastThreshold_unique f target _ _ (smallest_spec f hf target bracket)
    (sourceSmallest_spec f hf target bracket)

def search4 (f : Nat → Nat) (hf : Increasing f) (target : Nat) : List Nat :=
  let x := smallest f target (bound f hf target)
  if f x = target then [x] else []

def sourceSearch4 (f : Nat → Nat) (hf : Increasing f) (target : Nat) : List Nat :=
  let x := sourceSmallest f target (bound f hf target)
  if f x = target then [x] else []

theorem search4_eq_source (f : Nat → Nat) (hf : Increasing f) (target : Nat) :
    search4 f hf target = sourceSearch4 f hf target := by
  simp only [search4, sourceSearch4, smallest_eq_sourceSmallest f hf]

theorem mem_search4 (f : Nat → Nat) (hf : Increasing f) (target x : Nat) :
    x ∈ search4 f hf target ↔ f x = target := by
  have hs := smallest_spec f hf target (bound f hf target)
  unfold search4
  dsimp only
  split
  · rename_i he
    simp only [List.mem_singleton]
    constructor
    · intro hx; simpa [hx] using he
    · intro hx; exact hf.injective (hx.trans he.symm)
  · rename_i he
    simp only [List.not_mem_nil, false_iff]
    intro hx
    have hlo := hs.2 x (by omega)
    have hhit := hs.1
    have hhi : x ≤ smallest f target (bound f hf target) := by
      apply Nat.le_of_not_lt
      intro hn
      have h := hf hn
      omega
    have heq := Nat.le_antisymm hlo hhi
    exact he (heq ▸ hx)

theorem search4_eq_search (f : Nat → Nat) (hf : Increasing f) (target : Nat) :
    search4 f hf target = search f target := by
  apply short_lists_eq
  · unfold search4; dsimp only; split <;> simp
  · rw [← search1_eq_search]
    exact exhaustiveInterval_length_le f hf target 0 (target + 1)
  · intro x; rw [mem_search4, mem_search f hf]

theorem sourceSearch4_eq_search (f : Nat → Nat) (hf : Increasing f) (target : Nat) :
    sourceSearch4 f hf target = search f target := by
  rw [← search4_eq_source, search4_eq_search]

/-- Midpoint arithmetic connecting the source closed interval to lower/count. -/
theorem lowerPick_closed_midpoint (lower count : Nat) (h : 0 < count) :
    lower + lowerPick count = (lower + (lower + count - 1)) / 2 := by
  unfold lowerPick
  omega

theorem lowerPick_sentinel_midpoint (start count : Nat) (h : 0 < count) :
    (Int.ofNat (start + lowerPick count)) =
      ((Int.ofNat start - 1) + Int.ofNat (start + count)) / 2 := by
  simp only [lowerPick, Int.ofNat_eq_natCast, Int.natCast_add]
  omega

end OrderedSearch

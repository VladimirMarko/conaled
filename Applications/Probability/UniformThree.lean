import Applications.Probability.CoinPaths
import Applications.Probability.Results

/-!
# Uniform-three rejection execution

Each transition inspects one tape bit. The partial-block state retains the first
bit until the second arrives. Blocks 00, 01, 10 return 0, 1, 2; 11 retries.
The returned cursor counts consumed bits; the transition count charges bit
inspections, not the host cost of natural-number arithmetic.
-/
namespace Applications.Probability.UniformThree
open CoinPaths

abbrev State := ℕ × Option Bool
abbrev Return := Fin 3 × ℕ

/-- A single bit inspection, including the stored first bit of a block. -/
def step (ω : Tape) : Progress.Machine State Return
  | (s, none) => .inr (s + 1, some (ω s))
  | (s, some false) => .inl (if ω s then 1 else 0, s + 1)
  | (s, some true) => if ω s then .inr (s + 1, none) else .inl (2, s + 1)

/-- The accepted block for one of the three outputs. -/
def firstBit (a : Fin 3) : Bool := decide (a = 2)
def secondBit (a : Fin 3) : Bool := decide (a = 1)

/-- Exactly `n` rejected blocks followed by the chosen accepted block. -/
def Accept (ω : Tape) (s n : ℕ) (a : Fin 3) : Prop :=
  (∀ i, s ≤ i → i < s + 2 * n → ω i = true) ∧
  ω (s + 2 * n) = firstBit a ∧ ω (s + 2 * n + 1) = secondBit a

theorem accept_zero (ω : Tape) (s : ℕ) (a : Fin 3) :
    Accept ω s 0 a ↔ ω s = firstBit a ∧ ω (s + 1) = secondBit a := by
  simp [Accept]
  omega

theorem accept_succ (ω : Tape) (s n : ℕ) (a : Fin 3) :
    Accept ω s (n + 1) a ↔
      ω s = true ∧ ω (s + 1) = true ∧ Accept ω (s + 2) n a := by
  unfold Accept
  have he : s + 2 * (n + 1) = s + 2 + 2 * n := by omega
  rw [he]
  constructor
  · rintro ⟨h, ha, hb⟩
    exact ⟨h s (by omega) (by omega), h (s+1) (by omega) (by omega),
      ⟨fun i hi hj => h i (by omega) hj, ha, hb⟩⟩
  · rintro ⟨h0, h1, h, ha, hb⟩
    refine ⟨?_, ha, hb⟩
    intro i hi hj
    by_cases hsi : i = s
    · simpa [hsi] using h0
    by_cases hsi1 : i = s + 1
    · simpa [hsi1] using h1
    exact h i (by omega) hj

/-- Each accepted prefix is a genuine machine derivation with its exact cursor
and transition count. -/
theorem evaluates_of_accept {ω : Tape} {s n : ℕ} {a : Fin 3}
    (h : Accept ω s n a) :
    Progress.Evaluates (step ω) (s, none) (a, s + 2 * (n + 1)) (2 * (n + 1)) := by
  induction n generalizing s with
  | zero =>
    rw [accept_zero] at h
    rcases h with ⟨h0, h1⟩
    fin_cases a <;> simp [firstBit, secondBit] at h0 h1 <;>
      exact .next (t := (s+1, some (ω s))) rfl (.done (by simp [step, h0, h1, Nat.add_assoc]))
  | succ n ih =>
    rw [accept_succ] at h
    obtain ⟨h0, h1, rest⟩ := h
    have hr := ih rest
    have hn := Progress.Evaluates.next (step := step ω)
      (s := (s+1, some true)) (by simp [step, h1]) hr
    have hn' := Progress.Evaluates.next (step := step ω)
      (s := (s, none)) (by simp [step, h0]) hn
    convert hn' using 1; congr 1; omega

/-- Any finite execution has exactly one accepted prefix. -/
theorem accept_of_evaluates {ω : Tape} {s : ℕ} {a : Fin 3} {t k : ℕ}
    (h : Progress.Evaluates (step ω) (s, none) (a, t) k) :
    ∃ n, Accept ω s n a ∧ t = s + 2 * (n + 1) ∧ k = 2 * (n + 1) := by
  induction k using Nat.strong_induction_on generalizing s t with
  | h k ih =>
    cases h with
    | done e => simp [step] at e
    | @next _ u _ l e h =>
      simp only [step, Sum.inr.injEq] at e
      subst u
      cases h with
      | done e =>
        cases h0 : ω s <;> cases h1 : ω (s+1) <;>
          simp [step, h0, h1] at e
        all_goals
          rcases e with ⟨rfl, rfl⟩
          exact ⟨0, (accept_zero _ _ _).mpr (by simp [firstBit, secondBit, h0, h1]),
            by omega, rfl⟩
      | @next _ v _ j e h =>
        cases h0 : ω s <;> cases h1 : ω (s+1) <;>
          simp [step, h0, h1] at e
        subst v
        obtain ⟨n, hn, ht, hk⟩ := ih j (by omega) h
        refine ⟨n+1, (accept_succ _ _ _ _).mpr ⟨h0, h1, ?_⟩, ?_, ?_⟩
        · simpa [Nat.add_assoc] using hn
        · omega
        · omega

theorem evaluates_iff (ω : Tape) (s n : ℕ) (a : Fin 3) :
    Progress.Evaluates (step ω) (s, none) (a, s + 2 * (n+1)) (2 * (n+1)) ↔
      Accept ω s n a := by
  constructor
  · intro h
    obtain ⟨m, hm, _, hk⟩ := accept_of_evaluates h
    have : m = n := by omega
    simpa [this] using hm
  · exact evaluates_of_accept

theorem measurableSteps : ProbabilityProgress.MeasurableSteps step := by
  intro s r
  have eq : {ω | step ω s = r} =
      ({ω : Tape | ω s.1 = false} ∩ {ω | step (fun _ => false) s = r}) ∪
      ({ω : Tape | ω s.1 = true} ∩ {ω | step (fun _ => true) s = r}) := by
    ext ω
    rcases s with ⟨s, b⟩
    cases b with
    | none => cases hb : ω s <;> simp [step, hb]
    | some b => cases b <;> cases hb : ω s <;> simp [step, hb]
  rw [eq]
  have hm : Measurable (fun ω : Tape => ω s.1) := measurable_pi_apply s.1
  exact ((hm (measurableSet_singleton false)).inter
    (MeasurableSet.const _)).union
    ((hm (measurableSet_singleton true)).inter
    (MeasurableSet.const _))

/-- Rejection of the first `n` complete blocks. -/
def Reject (ω : Tape) (s n : ℕ) : Prop :=
  ∀ i, s ≤ i → i < s + 2*n → ω i = true

theorem reject_succ (ω : Tape) (s n : ℕ) :
    Reject ω s (n+1) ↔ ω s = true ∧ ω (s+1) = true ∧ Reject ω (s+2) n := by
  unfold Reject
  constructor
  · intro h
    exact ⟨h s (by omega) (by omega), h (s+1) (by omega) (by omega),
      fun i hi hj => h i (by omega) (by omega)⟩
  · rintro ⟨h0,h1,h⟩ i hi hj
    by_cases hsi : i = s
    · simpa [hsi] using h0
    by_cases hsi1 : i = s+1
    · simpa [hsi1] using h1
    exact h i (by omega) (by omega)

/-- Exhausting `2*n` transitions means precisely that all `n` complete blocks
were rejected. It does not imply divergence. -/
theorem search_none_even_iff (ω : Tape) (s n : ℕ) :
    Progress.search (step ω) (2*n) (s,none) = none ↔ Reject ω s n := by
  induction n generalizing s with
  | zero => simp [Progress.search, Reject]; omega
  | succ n ih =>
    rw [reject_succ]
    have he : 2*(n+1) = 2*n+1+1 := by omega
    rw [he]
    cases h0 : ω s <;> cases h1 : ω (s+1) <;>
      simp [Progress.search, step, h0, h1, ih, Nat.add_assoc]

/-- The all-true tape retries forever. -/
theorem all_true_diverges (s : ℕ) : ¬ Progress.Terminates (step (fun _ => true)) (s,none) := by
  rintro ⟨⟨a,t⟩,k,h⟩
  obtain ⟨n,hn,_,_⟩ := accept_of_evaluates h
  rcases hn with ⟨_,h0,h1⟩
  fin_cases a <;> simp [firstBit,secondBit] at h0 h1

end Applications.Probability.UniformThree

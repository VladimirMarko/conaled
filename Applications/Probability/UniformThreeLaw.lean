import Applications.Probability.UniformThree
import Mathlib.Probability.Independence.InfinitePi

/-!
# The law of uniform-three execution

Termination atoms retain the exact returned cursor and bit count. Their
probabilities come from the independent tape law, not from a sampler premise.
-/
namespace Applications.Probability.UniformThree
open CoinPaths MeasureTheory
open scoped ENNReal NNReal

/-- The finite bit assignment for a terminal execution. -/
def terminalBits (s n : ℕ) (a : Fin 3) : Tape := fun i =>
  if i < s + 2*n then true else if i = s + 2*n then firstBit a else secondBit a

theorem accept_eq_cylinder (s n : ℕ) (a : Fin 3) :
    {ω | Accept ω s n a} =
      Set.pi (Finset.Ico s (s + 2*(n+1))) (fun i => {terminalBits s n a i}) := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_pi, Finset.mem_coe, Finset.mem_Ico,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨h, h0, h1⟩ i ⟨hi, hj⟩
    unfold terminalBits
    split
    · exact h i hi (by assumption)
    · split
      · next he => simpa [he] using h0
      · have : i = s + 2*n+1 := by omega
        simpa [this] using h1
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i hi hj
      simpa [terminalBits, hj] using h i ⟨hi, by omega⟩
    · simpa [terminalBits] using h (s+2*n) ⟨by omega, by omega⟩
    · simpa [terminalBits] using h (s+2*n+1) ⟨by omega, by omega⟩

theorem measurableSet_accept (s n : ℕ) (a : Fin 3) :
    MeasurableSet {ω | Accept ω s n a} := by
  rw [accept_eq_cylinder]
  exact MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ => measurableSet_singleton _)

/-- Exact mass of each returned output, retry count, cursor and transition count. -/
theorem accept_mass (s n : ℕ) (a : Fin 3) :
    law {ω | Accept ω s n a} = (4⁻¹ : ℝ≥0∞) ^ (n+1) := by
  rw [accept_eq_cylinder, cylinder_mass]
  simp only [Nat.card_Ico, Nat.add_sub_cancel_left]
  rw [pow_mul, ← ENNReal.inv_pow]
  norm_num

theorem results_atom (s n : ℕ) (a : Fin 3) :
    ProbabilityProgress.results law step (s, none)
      {Sum.inr ((a, s + 2*(n+1)), 2*(n+1))} = (4⁻¹ : ℝ≥0∞) ^ (n+1) := by
  rw [ProbabilityProgress.results_some law step measurableSteps]
  simp only [evaluates_iff]
  exact accept_mass s n a

theorem accept_disjoint (s : ℕ) :
    Pairwise (fun p q : ℕ × Fin 3 => Disjoint {ω | Accept ω s p.1 p.2}
      {ω | Accept ω s q.1 q.2}) := by
  intro p q hne
  rw [Set.disjoint_left]
  intro ω hp hq
  obtain ⟨ha, hk⟩ := (evaluates_of_accept hp).unique (evaluates_of_accept hq)
  have hn : p.1 = q.1 := by omega
  have hv : p.2 = q.2 := congrArg Prod.fst ha
  exact hne (Prod.ext hn hv)

/-- The unbounded operational event, including any finite cursor and cost. -/
def returns (s : ℕ) (a : Fin 3) : Set Tape :=
  {ω | ∃ t k, Progress.Evaluates (step ω) (s, none) (a,t) k}

theorem returns_eq (s : ℕ) (a : Fin 3) :
    returns s a = ⋃ n, {ω | Accept ω s n a} := by
  ext ω
  simp only [returns, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨t, k, h⟩
    obtain ⟨n, hn, _, _⟩ := accept_of_evaluates h
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨_, _, evaluates_of_accept hn⟩

theorem measurableSet_returns (s : ℕ) (a : Fin 3) : MeasurableSet (returns s a) := by
  rw [returns_eq]
  exact MeasurableSet.iUnion fun n => measurableSet_accept s n a

/-- Each of the three values has mass one third under actual unbounded execution. -/
theorem returns_mass (s : ℕ) (a : Fin 3) : law (returns s a) = (3⁻¹ : ℝ≥0∞) := by
  rw [returns_eq, measure_iUnion]
  · simp only [accept_mass]
    rw [ENNReal.tsum_geometric_add_one]
    have hsub : (1 - (4 : ℝ≥0)⁻¹) = 3/4 := by
      apply NNReal.eq
      rw [NNReal.coe_sub ((inv_le_one₀ (by norm_num : (0 : ℝ≥0) < 4)).mpr (by norm_num))]
      norm_num
    change ((4 : ℝ≥0) : ℝ≥0∞)⁻¹ *
      (((1 : ℝ≥0) : ℝ≥0∞) - ((4 : ℝ≥0) : ℝ≥0∞)⁻¹)⁻¹ =
      ((3 : ℝ≥0) : ℝ≥0∞)⁻¹
    rw [← ENNReal.coe_inv (by norm_num : (4 : ℝ≥0) ≠ 0),
      ← ENNReal.coe_sub, hsub, ← ENNReal.coe_inv (by norm_num : (3/4 : ℝ≥0) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (3 : ℝ≥0) ≠ 0), ← ENNReal.coe_mul]
    norm_num
  · intro i j hij
    exact accept_disjoint s (i := (i,a)) (j := (j,a)) (by simpa using hij)
  · exact fun n => measurableSet_accept s n a

theorem termination_eq (s : ℕ) :
    ProbabilityProgress.termination step (s, none) = ⋃ a, returns s a := by
  ext ω
  simp only [ProbabilityProgress.termination, Progress.Terminates, returns,
    Set.mem_ofPred_eq, Set.mem_iUnion, Prod.exists]

theorem returns_disjoint (s : ℕ) : Pairwise (fun a b => Disjoint (returns s a) (returns s b)) := by
  intro a b hab
  rw [Set.disjoint_left]
  rintro ω ⟨t, k, h⟩ ⟨u, l, j⟩
  exact hab (congrArg Prod.fst (h.unique j).1)

theorem termination_mass (s : ℕ) :
    law (ProbabilityProgress.termination step (s, none)) = 1 := by
  rw [termination_eq, measure_iUnion (returns_disjoint s) (measurableSet_returns s)]
  simp [returns_mass, tsum_fintype]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

theorem ae_terminates (s : ℕ) : ∀ᵐ ω ∂law, Progress.Terminates (step ω) (s, none) := by
  rw [ae_iff]
  change law (ProbabilityProgress.termination step (s, none))ᶜ = 0
  rw [prob_compl_eq_one_sub (ProbabilityProgress.measurable_termination step measurableSteps _),
    termination_mass, tsub_self]

theorem results_mass_one (s : ℕ) :
    ProbabilityProgress.results law step (s, none) Set.univ = 1 := by
  rw [ProbabilityProgress.results_mass law step measurableSteps, termination_mass]

/-- Reindex the entire unused suffix, with no finite truncation. -/
def suffix (n : ℕ) (ω : Tape) : Tape := fun i => ω (n+i)

theorem measurable_suffix (n : ℕ) : Measurable (suffix n) := by
  unfold suffix
  fun_prop

theorem suffix_law (n : ℕ) : law.map (suffix n) = law := by
  exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => fairCoin)
    (f := fun i => n+i) (by intro i j h; exact Nat.add_left_cancel h)

/-- The finite prefix is independent of the entire infinite suffix. -/
theorem prefix_suffix_independent (n : ℕ) :
    ProbabilityTheory.IndepFun (fun ω : Tape => fun i : Fin n => ω i)
      (suffix n) law := by
  have hi : ProbabilityTheory.iIndepFun (fun i (ω : Tape) => ω i) law :=
    ProbabilityTheory.iIndepFun_infinitePi (X := fun _ (b : Bool) => b)
      (fun _ => measurable_id)
  have hd : Disjoint {i : ℕ | i < n} {i : ℕ | n ≤ i} := by
    rw [Set.disjoint_left]
    intro i h1 h2
    exact Nat.not_lt_of_ge h2 h1
  have h := hi.indepFun_set {i | i < n} {i | n ≤ i} hd
    (fun i => measurable_pi_apply i)
  exact h.comp
    (φ := fun f => fun i : Fin n => f ⟨i, i.isLt⟩)
    (ψ := fun f : ({i : ℕ | n ≤ i} → Bool) => fun i : ℕ => f ⟨n+i, Nat.le_add_right n i⟩)
    (by fun_prop) (by fun_prop)

theorem prefix_suffix_mass (n : ℕ) (E : Set (Fin n → Bool)) (B : Set Tape)
    (hB : MeasurableSet B) :
    law ({ω | (fun i : Fin n => ω i) ∈ E} ∩ suffix n ⁻¹' B) =
      law {ω | (fun i : Fin n => ω i) ∈ E} * law B := by
  have h := (prefix_suffix_independent n).measure_inter_preimage_eq_mul E B
    (Set.to_countable E).measurableSet hB
  rw [← Measure.map_apply (measurable_suffix n) hB, suffix_law] at h
  exact h

/-- A terminal atom is independent of every measurable event of the entire
unused suffix, at the cursor returned by that atom. -/
theorem accept_suffix_mass (s n : ℕ) (a : Fin 3) (B : Set Tape)
    (hB : MeasurableSet B) :
    law ({ω | Accept ω s n a} ∩ suffix (s+2*(n+1)) ⁻¹' B) =
      (4⁻¹ : ℝ≥0∞)^(n+1) * law B := by
  let cut := s+2*(n+1)
  let E : Set (Fin cut → Bool) := {f | ∀ i : Fin cut, s ≤ i → f i = terminalBits s n a i}
  have he : {ω : Tape | (fun i : Fin cut => ω i) ∈ E} = {ω | Accept ω s n a} := by
    rw [accept_eq_cylinder]
    ext ω
    simp only [E, Set.mem_ofPred_eq, Set.mem_pi, Finset.mem_coe, Finset.mem_Ico,
      Set.mem_singleton_iff]
    constructor
    · intro h i hi
      exact h ⟨i, hi.2⟩ hi.1
    · intro h i hi
      exact h i ⟨hi, i.isLt⟩
  have h := prefix_suffix_mass cut E B hB
  rw [he, accept_mass] at h
  exact h

/-- An arbitrary predicate on the retained retry count and result. The actual
cursor and transition count are determined by these observations. -/
def selected (s : ℕ) (C : ℕ → Fin 3 → Prop) : Set Tape :=
  ⋃ p : ℕ × Fin 3, {ω | Accept ω s p.1 p.2 ∧ C p.1 p.2}

/-- Observe a suffix event after the random finite return, not after a fixed
number of bits. Divergent tapes belong to neither event. -/
def selectedSuffix (s : ℕ) (C : ℕ → Fin 3 → Prop) (B : Set Tape) : Set Tape :=
  ⋃ p : ℕ × Fin 3,
    ({ω | Accept ω s p.1 p.2 ∧ C p.1 p.2} ∩ suffix (s+2*(p.1+1)) ⁻¹' B)

theorem selected_atom_measurable (s : ℕ) (C : ℕ → Fin 3 → Prop) (p : ℕ × Fin 3) :
    MeasurableSet {ω | Accept ω s p.1 p.2 ∧ C p.1 p.2} :=
  (measurableSet_accept s p.1 p.2).inter (MeasurableSet.const _)

/-- Freshness jointly with the result and retry count at the actual stopping
cursor. In particular, it permits downstream events selected by the first result. -/
theorem random_cursor_fresh (s : ℕ) (C : ℕ → Fin 3 → Prop) (B : Set Tape)
    (hB : MeasurableSet B) :
    law (selectedSuffix s C B) = law (selected s C) * law B := by
  have hd : Pairwise (fun p q : ℕ × Fin 3 =>
      Disjoint {ω | Accept ω s p.1 p.2 ∧ C p.1 p.2}
        {ω | Accept ω s q.1 q.2 ∧ C q.1 q.2}) := by
    intro p q hpq
    exact (accept_disjoint s hpq).mono (fun _ h => h.1) (fun _ h => h.1)
  unfold selectedSuffix selected
  rw [measure_iUnion (fun p q hpq => (hd hpq).mono Set.inter_subset_left Set.inter_subset_left)
    (fun p => (selected_atom_measurable s C p).inter ((measurable_suffix _) hB)),
    measure_iUnion hd (selected_atom_measurable s C), ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro p
  by_cases hc : C p.1 p.2
  · simp only [hc, and_true]
    rw [accept_suffix_mass s p.1 p.2 B hB, accept_mass]
  · simp [hc]

/-- The exact retry tail charges two actual bit inspections per block. -/
theorem search_timeout_mass (s n : ℕ) :
    law {ω | Progress.search (step ω) (2*n) (s,none) = none} = (4⁻¹ : ℝ≥0∞)^n := by
  have he : {ω | Progress.search (step ω) (2*n) (s,none) = none} =
      Set.pi (Finset.Ico s (s+2*n)) (fun _ => {true}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, search_none_even_iff, Reject, Set.mem_pi,
      Finset.mem_coe, Finset.mem_Ico, Set.mem_singleton_iff]
    aesop
  rw [he, cylinder_mass (bits := fun _ => true)]
  simp only [Nat.card_Ico, Nat.add_sub_cancel_left]
  rw [pow_mul, ← ENNReal.inv_pow]
  norm_num

theorem search_timeout_pos (s n : ℕ) :
    0 < law {ω | Progress.search (step ω) (2*n) (s,none) = none} := by
  rw [search_timeout_mass]
  exact bot_lt_iff_ne_bot.mpr (pow_ne_zero n (by simp))

end Applications.Probability.UniformThree

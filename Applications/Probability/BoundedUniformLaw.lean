import Applications.Probability.BoundedUniform

/-!
# Operational law and fresh suffix of bounded uniform sampling

Each accepted result is obtained after a geometrically distributed number of
rejected binary blocks. All claims refer to the bit-reading machine and retain
its returned cursor and actual number of transitions.
-/
namespace Applications.Probability.BoundedUniform
open CoinPaths CoinSuffix BinaryBlock MeasureTheory
open scoped ENNReal NNReal

/-- Exact rejection probability of one block. -/
noncomputable def rejection (n : ℕ) : ℝ≥0∞ :=
  (2^width n-n : ℕ) * (2⁻¹ : ℝ≥0∞)^(width n)

theorem first_reject_mass (n s : ℕ) :
    law {ω | n ≤ read ω s (width n)}=rejection n :=
  BinaryBlock.reject_mass s (width n) n (bound_le_capacity n)

theorem accept_suffix_iff (n : ℕ) (ω : Tape) (s t r : ℕ) (a : Fin n) :
    Accept n (suffix s ω) t r a ↔ Accept n ω (s+t) r a := by
  induction r generalizing t with
  | zero => simp [Accept,read_suffix_add]
  | succ r ih => simp [Accept,read_suffix_add,ih,Nat.add_assoc]

theorem reject_suffix_iff (n : ℕ) (ω : Tape) (s t r : ℕ) :
    Reject n (suffix s ω) t r ↔ Reject n ω (s+t) r := by
  induction r generalizing t with
  | zero => simp [Reject]
  | succ r ih => simp [Reject,read_suffix_add,ih,Nat.add_assoc]

theorem measurableSet_accept (n s r : ℕ) (a : Fin n) :
    MeasurableSet {ω | Accept n ω s r a} := by
  induction r generalizing s with
  | zero => exact (measurable_read s (width n)) (measurableSet_singleton _)
  | succ r ih =>
    exact ((measurable_read s (width n)) (Set.to_countable {v | n ≤ v}).measurableSet).inter (ih _)

theorem measurableSet_reject (n s r : ℕ) : MeasurableSet {ω | Reject n ω s r} := by
  induction r generalizing s with
  | zero => exact MeasurableSet.univ
  | succ r ih =>
    exact ((measurable_read s (width n)) (Set.to_countable {v | n ≤ v}).measurableSet).inter (ih _)

/-- Prefix dependence is proved for the operational terminal event, including
all possible histories of rejected block values. -/
theorem accept_prefix (n s r : ℕ) (a : Fin n) :
    PrefixEvent (s+width n*(r+1)) {ω | Accept n ω s r a} := by
  induction r generalizing s with
  | zero => simpa [Accept] using read_prefix s (width n) (fun v => v=a.val)
  | succ r ih =>
    intro ω η h
    change (n ≤ read ω s (width n) ∧ Accept n ω (s+width n) r a) ↔
      (n ≤ read η s (width n) ∧ Accept n η (s+width n) r a)
    have he : read ω s (width n)=read η s (width n) :=
      read_congr (fun i _ hi => h i (by nlinarith))
    rw [he]
    apply and_congr_right
    intro _
    exact ih _ ω η (fun i hi => h i (by nlinarith))

theorem accept_mass (n s r : ℕ) (a : Fin n) :
    law {ω | Accept n ω s r a}=rejection n^r * (2⁻¹ : ℝ≥0∞)^width n := by
  induction r generalizing s with
  | zero =>
    simpa [Accept] using read_mass s (width n) ⟨a.val,lt_of_lt_of_le a.isLt (bound_le_capacity n)⟩
  | succ r ih =>
    have h := prefix_event_mass (s+width n) {ω | n ≤ read ω s (width n)}
      {ω | Accept n ω 0 r a} (read_prefix _ _ _) (measurableSet_accept _ _ _ _)
    have he : {ω | Accept n ω s (r+1) a} =
        {ω | n ≤ read ω s (width n)} ∩ suffix (s+width n) ⁻¹' {ω | Accept n ω 0 r a} := by
      ext ω
      simp [Accept,accept_suffix_iff]
    rw [he,h,first_reject_mass,ih]
    ring

theorem reject_mass (n s r : ℕ) : law {ω | Reject n ω s r}=rejection n^r := by
  induction r generalizing s with
  | zero => simp [Reject]
  | succ r ih =>
    have h := prefix_event_mass (s+width n) {ω | n ≤ read ω s (width n)}
      {ω | Reject n ω 0 r} (read_prefix _ _ _) (measurableSet_reject _ _ _)
    have he : {ω | Reject n ω s (r+1)} =
        {ω | n ≤ read ω s (width n)} ∩ suffix (s+width n) ⁻¹' {ω | Reject n ω 0 r} := by
      ext ω
      simp [Reject,reject_suffix_iff]
    rw [he,h,first_reject_mass,ih,pow_succ']

theorem results_atom (n s r : ℕ) (a : Fin n) :
    ProbabilityProgress.results law (step n) (start n s)
      {Sum.inr ((a,s+width n*(r+1)),width n*(r+1))} =
      rejection n^r*(2⁻¹ : ℝ≥0∞)^width n := by
  rw [ProbabilityProgress.results_some law (step n) (measurableSteps n)]
  simp only [evaluates_iff]
  exact accept_mass n s r a

/-- Exact risk for any supplied fuel, including an incomplete final block. -/
theorem search_timeout_mass (n s fuel : ℕ) :
    law {ω | Progress.search (step n ω) fuel (start n s)=none} =
      rejection n^(fuel/width n) := by
  simp only [search_none_iff]
  exact reject_mass n s _

private noncomputable def rejectionNN (n : ℕ) : ℝ≥0 :=
  ((2^width n-n : ℕ) : ℝ≥0) / (2^width n : ℝ≥0)

private theorem rejection_eq_nn (n : ℕ) : rejection n=(rejectionNN n : ℝ≥0∞) := by
  rw [rejectionNN,ENNReal.coe_div (by positivity)]
  simp [rejection,div_eq_mul_inv,ENNReal.inv_pow]

private theorem rejectionNN_lt_one (n : ℕ) (hn : 0<n) : rejectionNN n<1 := by
  apply (div_lt_one (by positivity : (0 : ℝ≥0)<2^width n)).mpr
  exact_mod_cast Nat.sub_lt (by positivity : 0<2^width n) hn

theorem rejection_lt_one (n : ℕ) (hn : 0<n) : rejection n<1 := by
  rw [rejection_eq_nn]
  exact_mod_cast rejectionNN_lt_one n hn

private theorem normalizer (n : ℕ) (hn : 0<n) :
    (1-rejection n)⁻¹*(2⁻¹ : ℝ≥0∞)^width n=(n : ℝ≥0∞)⁻¹ := by
  have hq := rejectionNN_lt_one n hn
  have hM : (2^width n : ℝ≥0) ≠ 0 := by positivity
  have hn' : (n : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hsub : (1 : ℝ≥0)-rejectionNN n = (n : ℝ≥0)/2^width n := by
    apply NNReal.eq
    rw [NNReal.coe_sub hq.le]
    simp only [rejectionNN,NNReal.coe_div,NNReal.coe_natCast,NNReal.coe_pow,NNReal.coe_ofNat,
      NNReal.coe_one]
    rw [Nat.cast_sub (bound_le_capacity n)]
    push_cast
    field_simp
    ring
  have hsub0 : (1 : ℝ≥0)-rejectionNN n ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr hq)
  have hbit : (2⁻¹ : ℝ≥0∞)^width n = (((2^width n : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_inv hM,ENNReal.coe_pow,ENNReal.coe_ofNat,ENNReal.inv_pow]
  rw [rejection_eq_nn,← ENNReal.coe_one,← ENNReal.coe_sub,
    ← ENNReal.coe_inv hsub0,hbit,← ENNReal.coe_mul]
  change (( ((1-rejectionNN n)⁻¹*(2^width n)⁻¹ : ℝ≥0) ) : ℝ≥0∞) =
    ((n : ℝ≥0) : ℝ≥0∞)⁻¹
  rw [← ENNReal.coe_inv hn']
  congr 1
  rw [hsub]
  field_simp

/-- The unbounded returned-value event is defined by actual machine evaluation. -/
def returns (n s : ℕ) (a : Fin n) : Set Tape :=
  {ω | ∃ t k, Progress.Evaluates (step n ω) (start n s) (a,t) k}

theorem returns_eq (n s : ℕ) (a : Fin n) :
    returns n s a = ⋃ r, {ω | Accept n ω s r a} := by
  ext ω
  simp only [returns,Set.mem_ofPred_eq,Set.mem_iUnion]
  constructor
  · rintro ⟨t,k,h⟩
    obtain ⟨r,hr,_,_⟩ := accept_of_evaluates h
    exact ⟨r,hr⟩
  · rintro ⟨r,hr⟩
    exact ⟨_,_,evaluates_of_accept hr⟩

theorem accept_disjoint (n s : ℕ) : Pairwise (fun p q : ℕ × Fin n =>
    Disjoint {ω | Accept n ω s p.1 p.2} {ω | Accept n ω s q.1 q.2}) := by
  intro p q hpq
  apply Set.disjoint_left.mpr
  intro ω hp hq
  obtain ⟨ha,hk⟩ := (evaluates_of_accept hp).unique (evaluates_of_accept hq)
  have hr : p.1=q.1 := by have := width_pos n; nlinarith
  exact hpq (Prod.ext hr (congrArg Prod.fst ha))

theorem measurableSet_returns (n s : ℕ) (a : Fin n) : MeasurableSet (returns n s a) := by
  rw [returns_eq]
  exact MeasurableSet.iUnion fun r => measurableSet_accept n s r a

/-- Every possible result has exactly probability 1/n. -/
theorem returns_mass (n s : ℕ) (a : Fin n) : law (returns n s a)=(n : ℝ≥0∞)⁻¹ := by
  rw [returns_eq,measure_iUnion]
  · simp only [accept_mass,ENNReal.tsum_mul_right,ENNReal.tsum_geometric]
    exact normalizer n (Nat.zero_lt_of_lt a.isLt)
  · intro i j hij
    exact accept_disjoint n s (i := (i,a)) (j := (j,a)) (by simpa using hij)
  · exact fun r => measurableSet_accept n s r a

theorem termination_mass (n s : ℕ) (hn : 0<n) :
    law (ProbabilityProgress.termination (step n) (start n s))=1 := by
  have he : ProbabilityProgress.termination (step n) (start n s)=⋃ a, returns n s a := by
    ext ω
    simp only [ProbabilityProgress.termination,Progress.Terminates,returns,
      Set.mem_ofPred_eq,Set.mem_iUnion,Prod.exists]
  rw [he,measure_iUnion]
  · simp only [returns_mass,tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast Nat.ne_of_gt hn) (by simp)
  · intro a b hab
    apply Set.disjoint_left.mpr
    rintro ω ⟨t,k,h⟩ ⟨u,l,j⟩
    exact hab (congrArg Prod.fst (h.unique j).1)
  · exact measurableSet_returns n s

theorem ae_terminates (n s : ℕ) (hn : 0<n) :
    ∀ᵐ ω ∂law, Progress.Terminates (step n ω) (start n s) :=
  (mem_ae_iff_prob_eq_one (ProbabilityProgress.measurable_termination (step n) (measurableSteps n) _)).mpr
    (termination_mass n s hn)

theorem results_mass_one (n s : ℕ) (hn : 0<n) :
    ProbabilityProgress.results law (step n) (start n s) Set.univ=1 := by
  rw [ProbabilityProgress.results_mass law (step n) (measurableSteps n),termination_mass n s hn]

/-- Terminal events factor against every measurable event of the entire unused
suffix at their actual returned cursor. -/
theorem accept_suffix_mass (n s r : ℕ) (a : Fin n) (B : Set Tape) (hB : MeasurableSet B) :
    law ({ω | Accept n ω s r a} ∩ suffix (s+width n*(r+1)) ⁻¹' B) =
      (rejection n^r*(2⁻¹ : ℝ≥0∞)^width n)*law B := by
  rw [prefix_event_mass _ _ _ (accept_prefix n s r a) hB,accept_mass]

/-- Select arbitrary observations of the returned result and retry count.
Together these determine the returned cursor and complete bit work. -/
def selected (n s : ℕ) (C : ℕ → Fin n → Prop) : Set Tape :=
  ⋃ p : ℕ × Fin n, {ω | Accept n ω s p.1 p.2 ∧ C p.1 p.2}

def selectedSuffix (n s : ℕ) (C : ℕ → Fin n → Prop) (B : Set Tape) : Set Tape :=
  ⋃ p : ℕ × Fin n,
    ({ω | Accept n ω s p.1 p.2 ∧ C p.1 p.2} ∩ suffix (s+width n*(p.1+1)) ⁻¹' B)

/-- Freshness at the randomly returned cursor, jointly with result and work.
Divergent tapes are excluded from both events; their mass is separately zero
when the bound is positive. -/
theorem random_cursor_fresh (n s : ℕ) (C : ℕ → Fin n → Prop) (B : Set Tape)
    (hB : MeasurableSet B) : law (selectedSuffix n s C B)=law (selected n s C)*law B := by
  have hm (p : ℕ × Fin n) : MeasurableSet {ω | Accept n ω s p.1 p.2 ∧ C p.1 p.2} :=
    (measurableSet_accept n s p.1 p.2).inter (MeasurableSet.const _)
  have hd : Pairwise (fun p q : ℕ × Fin n =>
      Disjoint {ω | Accept n ω s p.1 p.2 ∧ C p.1 p.2}
        {ω | Accept n ω s q.1 q.2 ∧ C q.1 q.2}) := by
    intro p q hpq
    exact (accept_disjoint n s hpq).mono (fun _ h => h.1) (fun _ h => h.1)
  unfold selectedSuffix selected
  rw [measure_iUnion (fun p q hpq => (hd hpq).mono Set.inter_subset_left Set.inter_subset_left)
    (fun p => (hm p).inter ((measurable_suffix _) hB)),measure_iUnion hd hm,
    ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro p
  by_cases hc : C p.1 p.2
  · simp only [hc,and_true]
    rw [accept_suffix_mass _ _ _ _ B hB,accept_mass]
  · simp [hc]

theorem rejection_zero (n : ℕ) (h : 2^width n=n) : rejection n=0 := by
  simp [rejection,h]

theorem rejection_pos (n : ℕ) (h : n<2^width n) : 0<rejection n := by
  apply bot_lt_iff_ne_bot.mpr
  apply mul_ne_zero
  · exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt h)
  · exact pow_ne_zero _ (by simp)

end Applications.Probability.BoundedUniform

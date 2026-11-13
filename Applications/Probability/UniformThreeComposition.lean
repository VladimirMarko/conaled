import Applications.Probability.UniformThreeLaw

/-!
# Two samples from one tape

The second sample starts at the first sample's returned cursor. Its interpreted
value is the sum of the first and second sampled values, so its meaning depends
on the first result. The joint law retains both draws and their work.
-/
namespace Applications.Probability.UniformThree
open CoinPaths MeasureTheory
open scoped ENNReal NNReal

/-- A second sampler retaining the first value and interpreting the new value
as its sum with the first. -/
def second (ω : Tape) : Progress.Machine (Return × State) (Return × ℕ × ℕ)
  | (first,q) => match step ω q with
    | .inl (b,t) => .inl (first,first.1.val+b.val,t)
    | .inr q' => .inr (first,q')

/-- Run both samplers with one tape and the actual returned cursor. -/
def pairStep (ω : Tape) := Progress.sequential (step ω) (second ω)
  (fun first => (first,(first.2,none)))

theorem second_evaluates {ω : Tape} {q : State} {r : Return} {k : ℕ}
    (h : Progress.Evaluates (step ω) q r k) (first : Return) :
    Progress.Evaluates (second ω) (first,q) (first,first.1.val+r.1.val,r.2) k := by
  induction h with
  | done h => exact .done (by simp [second,h])
  | next h _ ih => exact .next (by simp [second,h]) ih

/-- The complete operational two-stage derivation, with exact bit work. -/
theorem pair_evaluates {ω : Tape} {s n m : ℕ} {a b : Fin 3}
    (h : Accept ω s n a) (j : Accept ω (s+2*(n+1)) m b) :
    Progress.Evaluates (pairStep ω) (.inl (s,none))
      ((a,s+2*(n+1)),a.val+b.val,s+2*(n+1)+2*(m+1)) (2*(n+1)+2*(m+1)) :=
  Progress.sequential_evaluates (evaluates_of_accept h)
    (second_evaluates (evaluates_of_accept j) (a,s+2*(n+1)))

private theorem sequential_right_inv {S T A B : Type} {f : Progress.Machine S A}
    {g : Progress.Machine T B} {start : A → T} {t : T} {b : B} {k : ℕ}
    (h : Progress.Evaluates (Progress.sequential f g start) (.inr t) b k) :
    Progress.Evaluates g t b k := by
  induction k using Nat.strong_induction_on generalizing t with
  | h k ih =>
    cases h with
    | done e =>
      cases hg : g t with
      | inl v => simp [Progress.sequential,hg] at e; subst v; exact .done hg
      | inr u => simp [Progress.sequential,hg] at e
    | @next _ u _ l e h =>
      cases hg : g t with
      | inl v => simp [Progress.sequential,hg] at e
      | inr v =>
        simp only [Progress.sequential,hg,Sum.inr.injEq] at e
        subst u
        exact .next hg (ih l (by omega) h)

private theorem sequential_left_inv {S T A B : Type} {f : Progress.Machine S A}
    {g : Progress.Machine T B} {start : A → T} {s : S} {b : B} {k : ℕ}
    (h : Progress.Evaluates (Progress.sequential f g start) (.inl s) b k) :
    ∃ a i j, Progress.Evaluates f s a i ∧ Progress.Evaluates g (start a) b j ∧ k=i+j := by
  induction k using Nat.strong_induction_on generalizing s with
  | h k ih =>
    cases h with
    | done e => cases hf : f s <;> simp [Progress.sequential,hf] at e
    | @next _ u _ l e h =>
      cases hf : f s with
      | inl a =>
        simp only [Progress.sequential,hf,Sum.inr.injEq] at e
        subst u
        exact ⟨a,1,l,.done hf,sequential_right_inv h,by omega⟩
      | inr v =>
        simp only [Progress.sequential,hf,Sum.inr.injEq] at e
        subst u
        obtain ⟨a,i,j,hi,hj,hk⟩ := ih l (by omega) h
        exact ⟨a,i+1,j,.next hf hi,hj,by omega⟩

theorem second_evaluates_inv {ω : Tape} {first : Return} {q : State}
    {r : Return × ℕ × ℕ} {k : ℕ}
    (h : Progress.Evaluates (second ω) (first,q) r k) :
    ∃ b t, Progress.Evaluates (step ω) q (b,t) k ∧ r=(first,first.1.val+b.val,t) := by
  induction k using Nat.strong_induction_on generalizing q with
  | h k ih =>
    cases h with
    | done e =>
      cases hs : step ω q with
      | inl v =>
        rcases v with ⟨b,t⟩
        simp only [second,hs,Sum.inl.injEq] at e
        exact ⟨b,t,.done hs,e.symm⟩
      | inr v => simp [second,hs] at e
    | @next _ u _ l e h =>
      cases hs : step ω q with
      | inl v => rcases v with ⟨b,t⟩; simp [second,hs] at e
      | inr v =>
        simp only [second,hs,Sum.inr.injEq] at e
        subst u
        obtain ⟨b,t,hb,hr⟩ := ih l (by omega) h
        exact ⟨b,t,.next hs hb,hr⟩

/-- Every paired return comes from two accepted prefixes at the actual cursor. -/
theorem pair_evaluates_inv {ω : Tape} {s : ℕ} {r : Return × ℕ × ℕ} {k : ℕ}
    (h : Progress.Evaluates (pairStep ω) (.inl (s,none)) r k) :
    ∃ n m a b, Accept ω s n a ∧ Accept ω (s+2*(n+1)) m b ∧
      r=((a,s+2*(n+1)),a.val+b.val,s+2*(n+1)+2*(m+1)) ∧
      k=2*(n+1)+2*(m+1) := by
  obtain ⟨⟨a,t⟩,i,j,hi,hj,hk⟩ := sequential_left_inv h
  obtain ⟨n,hn,ht,hi'⟩ := accept_of_evaluates hi
  subst t
  obtain ⟨b,u,hb,hr⟩ := second_evaluates_inv hj
  obtain ⟨m,hm,hu,hj'⟩ := accept_of_evaluates hb
  subst u
  exact ⟨n,m,a,b,hn,hm,hr,by omega⟩

theorem pair_evaluates_iff (ω : Tape) (s n m : ℕ) (a b : Fin 3) :
    Progress.Evaluates (pairStep ω) (.inl (s,none))
      ((a,s+2*(n+1)),a.val+b.val,s+2*(n+1)+2*(m+1)) (2*(n+1)+2*(m+1)) ↔
    Accept ω s n a ∧ Accept ω (s+2*(n+1)) m b := by
  constructor
  · intro h
    obtain ⟨n',m',a',b',hn,hm,hr,hk⟩ := pair_evaluates_inv h
    simp only [Prod.mk.injEq] at hr
    have ha : a=a' := hr.1.1
    have hn' : n=n' := by omega
    have hm' : m=m' := by omega
    have hb : b=b' := Fin.ext (by omega)
    simpa [ha,hn',hm',hb] using And.intro hn hm
  · rintro ⟨h,j⟩
    exact pair_evaluates h j

/-- Prefix interpretation commutes with moving to a suffix. -/
theorem accept_suffix_iff (ω : Tape) (t m : ℕ) (b : Fin 3) :
    Accept (suffix t ω) 0 m b ↔ Accept ω t m b := by
  simp only [Accept, suffix, zero_add]
  constructor
  · rintro ⟨h,h0,h1⟩
    refine ⟨?_,h0,?_⟩
    · intro i hi hj
      have := h (i-t) (by omega) (by omega)
      simpa [Nat.add_sub_of_le hi] using this
    · simpa [Nat.add_assoc] using h1
  · rintro ⟨h,h0,h1⟩
    refine ⟨?_,h0,?_⟩
    · intro i _ hi
      exact h (t+i) (by omega) (by omega)
    · simpa [Nat.add_assoc] using h1

/-- The full two-draw atom factors at the random first cursor.
Both retry counts, output values, final cursor and total work are retained. -/
theorem pair_atom_mass (s n m : ℕ) (a b : Fin 3) :
    law {ω | Accept ω s n a ∧ Accept ω (s+2*(n+1)) m b} =
      (4⁻¹ : ℝ≥0∞)^(n+1) * (4⁻¹ : ℝ≥0∞)^(m+1) := by
  have h := accept_suffix_mass s n a {ω | Accept ω 0 m b} (measurableSet_accept 0 m b)
  rw [accept_mass] at h
  convert h using 1
  congr 1
  ext ω
  simp [accept_suffix_iff]

theorem measurableSteps_second : ProbabilityProgress.MeasurableSteps second := by
  intro s r
  let f : Sum Return State → Sum (Return × ℕ × ℕ) (Return × State) := fun x =>
    match x with
    | .inl (b,t) => .inl (s.1,s.1.1.val+b.val,t)
    | .inr q => .inr (s.1,q)
  have he : {ω | second ω s=r} =
      ⋃ x, ({ω | step ω s.2=x} ∩ {ω | f x=r}) := by
    ext ω
    simp only [Set.mem_iUnion,Set.mem_inter_iff,Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨step ω s.2,rfl,h⟩
    · rintro ⟨x,hx,hr⟩
      change f (step ω s.2)=r
      rwa [hx]
  rw [he]
  exact MeasurableSet.iUnion fun x => (measurableSteps s.2 x).inter (MeasurableSet.const _)

theorem measurableSteps_pair : ProbabilityProgress.MeasurableSteps pairStep :=
  ProbabilityProgress.measurableSteps_sequential step second _ measurableSteps measurableSteps_second

/-- The result measure retains both cursors, the dependent output and total work. -/
theorem pair_results_atom (s n m : ℕ) (a b : Fin 3) :
    ProbabilityProgress.results law pairStep (.inl (s,none))
      {Sum.inr (((a,s+2*(n+1)),a.val+b.val,s+2*(n+1)+2*(m+1)),
        2*(n+1)+2*(m+1))} =
      (4⁻¹ : ℝ≥0∞)^(n+1) * (4⁻¹ : ℝ≥0∞)^(m+1) := by
  rw [ProbabilityProgress.results_some law pairStep measurableSteps_pair]
  simp only [pair_evaluates_iff]
  exact pair_atom_mass s n m a b

/-- Joint output event after forgetting cursors and work, but retaining the first
value and the dependent second interpretation. -/
def pairReturns (s : ℕ) (a : Fin 3) (v : ℕ) : Set Tape :=
  {ω | ∃ t u k, Progress.Evaluates (pairStep ω) (.inl (s,none)) ((a,t),v,u) k}

theorem selected_value (s : ℕ) (a : Fin 3) :
    selected s (fun _ v => v=a) = returns s a := by
  rw [returns_eq]
  ext ω
  simp only [selected,Set.mem_iUnion,Set.mem_ofPred_eq,Prod.exists]
  aesop

theorem pairReturns_eq (s : ℕ) (a b : Fin 3) :
    pairReturns s a (a.val+b.val) =
      selectedSuffix s (fun _ v => v=a) (returns 0 b) := by
  ext ω
  simp only [pairReturns,selectedSuffix,Set.mem_iUnion,Set.mem_inter_iff,
    Set.mem_ofPred_eq,Set.mem_preimage,Prod.exists,returns_eq]
  constructor
  · rintro ⟨t,u,k,h⟩
    obtain ⟨n,m,a',b',hn,hm,hr,hk⟩ := pair_evaluates_inv h
    simp only [Prod.mk.injEq] at hr
    have ha : a=a' := hr.1.1
    have hb : b=b' := Fin.ext (by omega)
    subst a'; subst b'
    refine ⟨n,a,⟨hn,rfl⟩,?_⟩
    exact ⟨m,(accept_suffix_iff _ _ _ _).mpr hm⟩
  · rintro ⟨n,a',⟨hn,rfl⟩,hm⟩
    obtain ⟨m,hm⟩ := hm
    exact ⟨_,_,_,pair_evaluates hn ((accept_suffix_iff _ _ _ _).mp hm)⟩

/-- All nine possible joint interpreted outputs have their exact probability. -/
theorem pairReturns_mass (s : ℕ) (a b : Fin 3) :
    law (pairReturns s a (a.val+b.val)) = (9⁻¹ : ℝ≥0∞) := by
  rw [pairReturns_eq,random_cursor_fresh _ _ _ (measurableSet_returns 0 b),
    selected_value,returns_mass,returns_mass,← ENNReal.mul_inv (by simp) (by simp)]
  norm_num

/-- Outputs outside the dependent interpretation's support cannot be returned. -/
theorem pairReturns_outside (s : ℕ) (a : Fin 3) (v : ℕ)
    (hv : ∀ b : Fin 3, v ≠ a.val+b.val) : pairReturns s a v = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro ω ⟨t,u,k,h⟩
  obtain ⟨n,m,a',b,_,_,hr,_⟩ := pair_evaluates_inv h
  simp only [Prod.mk.injEq] at hr
  exact hv b (by simpa [hr.1.1] using hr.2.1)

theorem ae_pair_terminates (s : ℕ) :
    ∀ᵐ ω ∂law, Progress.Terminates (pairStep ω) (.inl (s,none)) := by
  have hall : ∀ᵐ ω ∂law, ∀ t, Progress.Terminates (step ω) (t,none) :=
    (ae_all_iff).mpr ae_terminates
  filter_upwards [hall] with ω h
  obtain ⟨first,k,hfirst⟩ := h s
  obtain ⟨r,l,hlast⟩ := h first.2
  exact ⟨_,k+l,Progress.sequential_evaluates hfirst (second_evaluates hlast first)⟩

theorem pair_results_mass_one (s : ℕ) :
    ProbabilityProgress.results law pairStep (.inl (s,none)) Set.univ = 1 := by
  rw [ProbabilityProgress.results_mass law pairStep measurableSteps_pair]
  exact (mem_ae_iff_prob_eq_one (ProbabilityProgress.measurable_termination pairStep
    measurableSteps_pair _)).mp (ae_pair_terminates s)

/-- Separating implementation: deliberately restart the second sampler at the
original cursor, reusing the first draw's random bits. -/
def reusedPairStep (s : ℕ) (ω : Tape) := Progress.sequential (step ω) (second ω)
  (fun first => (first,(s,none)))

def reusedPairReturns (s : ℕ) (a : Fin 3) (v : ℕ) : Set Tape :=
  {ω | ∃ t u k, Progress.Evaluates (reusedPairStep s ω) (.inl (s,none)) ((a,t),v,u) k}

theorem reusedPairReturns_off_diagonal (s : ℕ) (a : Fin 3) (v : ℕ)
    (hv : v ≠ a.val+a.val) : reusedPairReturns s a v = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro ω ⟨t,u,k,h⟩
  obtain ⟨first,i,j,hfirst,hsecond,_⟩ := sequential_left_inv h
  obtain ⟨b,z,hb,hr⟩ := second_evaluates_inv hsecond
  have he := (hfirst.unique hb).1
  rcases first with ⟨a',t'⟩
  simp only [Prod.mk.injEq] at hr he
  exact hv (by omega)

/-- Tape reuse changes a full joint event from probability one ninth to zero. -/
theorem fresh_ne_reused (s : ℕ) :
    law (pairReturns s 0 1) = (9⁻¹ : ℝ≥0∞) ∧
      law (reusedPairReturns s 0 1) = 0 := by
  constructor
  · exact pairReturns_mass s 0 1
  · rw [reusedPairReturns_off_diagonal s 0 1 (by decide),measure_empty]

end Applications.Probability.UniformThree

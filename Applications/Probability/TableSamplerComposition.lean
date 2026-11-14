import Applications.Probability.TableSampler

/-!
# Sequential sampling at returned cursors

Prefix dependence comes from the actual row machine. Independence below applies
to its random returned cursor, retaining the first outcome and work.
-/
namespace Applications.Probability.PreparedRow
open CoinPaths CoinSuffix MeasureTheory
open scoped ENNReal
variable {β γ : Type} (p : PreparedRow β)

theorem evaluates_shift (ω : Tape) (s u k : ℕ) (b : β) :
    Progress.Evaluates (p.step (suffix s ω)) (p.start 0) (b,u) k ↔
      Progress.Evaluates (p.step ω) (p.start s) (b,s+u) k := by
  simp only [evaluates_iff,BoundedUniform.accept_suffix_iff,Nat.add_zero,zero_add,
    Nat.add_left_cancel_iff]

theorem evaluates_prefix (s : ℕ) (b : β) (t k : ℕ) :
    PrefixEvent t {ω | Progress.Evaluates (p.step ω) (p.start s) (b,t) k} := by
  intro ω η he
  have transfer (ω η : Tape) (he : ∀ i, i<t → ω i=η i)
      (h : Progress.Evaluates (p.step ω) (p.start s) (b,t) k) :
      Progress.Evaluates (p.step η) (p.start s) (b,t) k := by
    obtain ⟨r,a,ha,hb,ht,hk⟩ := (p.evaluates_iff _ _ _ _ _).mp h
    apply (p.evaluates_iff _ _ _ _ _).mpr
    refine ⟨r,a,?_,hb,ht,hk⟩
    exact (BoundedUniform.accept_prefix p.total s r a ω η (by simpa [← ht] using he)).mp ha
  exact ⟨transfer ω η he,transfer η ω (fun i hi => (he i hi).symm)⟩

theorem evaluates_suffix_mass (s : ℕ) (b : β) (t k : ℕ) (B : Set Tape)
    (hB : MeasurableSet B) :
    law ({ω | Progress.Evaluates (p.step ω) (p.start s) (b,t) k} ∩ suffix t ⁻¹' B)=
      law {ω | Progress.Evaluates (p.step ω) (p.start s) (b,t) k}*law B :=
  prefix_event_mass t _ B (p.evaluates_prefix s b t k) hB

theorem returns_shift (ω : Tape) (s : ℕ) (b : β) :
    suffix s ω∈p.returns 0 b ↔ ω∈p.returns s b := by
  constructor
  · rintro ⟨u,k,h⟩
    exact ⟨s+u,k,(p.evaluates_shift ω s u k b).mp h⟩
  · rintro ⟨t,k,h⟩
    obtain ⟨r,a,ha,hb,ht,hk⟩ := (p.evaluates_iff _ _ _ _ _).mp h
    subst t
    exact ⟨_,k,(p.evaluates_shift ω s _ k b).mpr h⟩

theorem measurable_returns (s : ℕ) (b : β) : MeasurableSet (p.returns s b) := by
  rw [p.returns_eq]
  exact MeasurableSet.iUnion fun a =>
    (BoundedUniform.measurableSet_returns _ _ _).inter (MeasurableSet.const _)

/-- A general stopping-output event, retaining arbitrary restrictions on the
returned value, absolute cursor, and exact work. -/
def selected (s : ℕ) (C : β → ℕ → ℕ → Prop) : Set Tape :=
  ⋃ v : β × ℕ × ℕ, {ω | Progress.Evaluates (p.step ω) (p.start s) (v.1,v.2.1) v.2.2 ∧
    C v.1 v.2.1 v.2.2}

def selectedSuffix (s : ℕ) (C : β → ℕ → ℕ → Prop) (B : Set Tape) : Set Tape :=
  ⋃ v : β × ℕ × ℕ, ({ω | Progress.Evaluates (p.step ω) (p.start s) (v.1,v.2.1) v.2.2 ∧
    C v.1 v.2.1 v.2.2} ∩ suffix v.2.1 ⁻¹' B)

theorem random_cursor_fresh [Countable β] (s : ℕ) (C : β → ℕ → ℕ → Prop)
    (B : Set Tape) (hB : MeasurableSet B) :
    law (p.selectedSuffix s C B)=law (p.selected s C)*law B := by
  have hm (v : β × ℕ × ℕ) : MeasurableSet {ω |
      Progress.Evaluates (p.step ω) (p.start s) (v.1,v.2.1) v.2.2 ∧ C v.1 v.2.1 v.2.2} :=
    (ProbabilityProgress.measurable_evaluates _ p.measurableSteps _ _ _).inter (MeasurableSet.const _)
  have hd : Pairwise (fun v w : β × ℕ × ℕ => Disjoint
      {ω | Progress.Evaluates (p.step ω) (p.start s) (v.1,v.2.1) v.2.2 ∧ C v.1 v.2.1 v.2.2}
      {ω | Progress.Evaluates (p.step ω) (p.start s) (w.1,w.2.1) w.2.2 ∧ C w.1 w.2.1 w.2.2}) := by
    intro v w hvw
    apply Set.disjoint_left.mpr
    rintro ω ⟨hv,_⟩ ⟨hw,_⟩
    obtain ⟨ha,hk⟩ := hv.unique hw
    have h1 : v.1=w.1 := congrArg (fun z : β × ℕ => z.1) ha
    have h2 : v.2.1=w.2.1 := congrArg (fun z : β × ℕ => z.2) ha
    exact hvw (Prod.ext h1 (Prod.ext h2 hk))
  unfold selectedSuffix selected
  rw [measure_iUnion (fun v w hvw => (hd hvw).mono Set.inter_subset_left Set.inter_subset_left)
    (fun v => (hm v).inter ((measurable_suffix _) hB)),measure_iUnion hd hm,
    ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro v
  by_cases h : C v.1 v.2.1 v.2.2
  · simp only [h,and_true]
    exact p.evaluates_suffix_mass _ _ _ _ B hB
  · simp [h]

/-- Full two-output event, with the second row allowed to depend on the first
value and with its start cursor taken from the actual first return. -/
def joint (q : β → PreparedRow γ) (s : ℕ) (a : β) (b : γ) : Set Tape :=
  {ω | ∃ t k, Progress.Evaluates (p.step ω) (p.start s) (a,t) k ∧ ω∈(q a).returns t b}

theorem joint_mass (q : β → PreparedRow γ) (s : ℕ) (a : β) (b : γ) :
    law (p.joint q s a b)=law (p.returns s a)*law ((q a).returns 0 b) := by
  have he : p.joint q s a b=⋃ v : ℕ × ℕ,
      ({ω | Progress.Evaluates (p.step ω) (p.start s) (a,v.1) v.2} ∩
        suffix v.1 ⁻¹' (q a).returns 0 b) := by
    ext ω
    simp only [joint,Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff,
      Set.mem_preimage,returns_shift,Prod.exists]
  have hr : p.returns s a=⋃ v : ℕ × ℕ,
      {ω | Progress.Evaluates (p.step ω) (p.start s) (a,v.1) v.2} := by
    ext ω; simp [returns,Prod.exists]
  have hd : Pairwise (fun v w : ℕ × ℕ => Disjoint
      {ω | Progress.Evaluates (p.step ω) (p.start s) (a,v.1) v.2}
      {ω | Progress.Evaluates (p.step ω) (p.start s) (a,w.1) w.2}) := by
    intro v w hvw
    apply Set.disjoint_left.mpr
    intro ω hv hw
    obtain ⟨ha,hk⟩ := hv.unique hw
    exact hvw (Prod.ext (congrArg Prod.snd ha) hk)
  have hm (v : ℕ × ℕ) := ProbabilityProgress.measurable_evaluates _ p.measurableSteps (p.start s) (a,v.1) v.2
  rw [he,hr,measure_iUnion (fun v w h => (hd h).mono Set.inter_subset_left Set.inter_subset_left)
    (fun v => (hm v).inter ((measurable_suffix _) ((q a).measurable_returns 0 b))),
    measure_iUnion hd hm,← ENNReal.tsum_mul_right]
  exact tsum_congr fun v => p.evaluates_suffix_mass _ _ _ _ _ ((q a).measurable_returns 0 b)

theorem stopped_mass (s : ℕ) (a : β) (B : Set Tape) (hB : MeasurableSet B) :
    law ({ω | ∃ t k, Progress.Evaluates (p.step ω) (p.start s) (a,t) k ∧ suffix t ω∈B})=law (p.returns s a)*law (B) := by
  have he : {ω | ∃ t k, Progress.Evaluates (p.step ω) (p.start s) (a,t) k ∧ suffix t ω∈B}=⋃ v : ℕ × ℕ,
      ({ω | Progress.Evaluates (p.step ω) (p.start s) (a,v.1) v.2} ∩
        suffix v.1 ⁻¹' B) := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff,
      Set.mem_preimage,Prod.exists]
  have hr : p.returns s a=⋃ v : ℕ × ℕ,
      {ω | Progress.Evaluates (p.step ω) (p.start s) (a,v.1) v.2} := by
    ext ω; simp [returns,Prod.exists]
  have hd : Pairwise (fun v w : ℕ × ℕ => Disjoint
      {ω | Progress.Evaluates (p.step ω) (p.start s) (a,v.1) v.2}
      {ω | Progress.Evaluates (p.step ω) (p.start s) (a,w.1) w.2}) := by
    intro v w hvw
    apply Set.disjoint_left.mpr
    intro ω hv hw
    obtain ⟨ha,hk⟩ := hv.unique hw
    exact hvw (Prod.ext (congrArg Prod.snd ha) hk)
  have hm (v : ℕ × ℕ) := ProbabilityProgress.measurable_evaluates _ p.measurableSteps (p.start s) (a,v.1) v.2
  rw [he,hr,measure_iUnion (fun v w h => (hd h).mono Set.inter_subset_left Set.inter_subset_left)
    (fun v => (hm v).inter ((measurable_suffix _) hB)),
    measure_iUnion hd hm,← ENNReal.tsum_mul_right]
  exact tsum_congr fun v => p.evaluates_suffix_mass _ _ _ _ _ hB

/-- The second machine retains the complete first return. -/
def second (q : β → PreparedRow γ) (ω : Tape) :
    Progress.Machine ((β × ℕ) × State) ((β × ℕ) × (γ × ℕ)) :=
  Progress.family (fun first => Progress.mapReturn (fun r => (first,r)) ((q first.1).step ω))

def pairStep (q : β → PreparedRow γ) (ω : Tape) :=
  Progress.sequential (p.step ω) (second q ω)
    (fun first => (first,(q first.1).start first.2))

theorem pair_evaluates_iff (q : β → PreparedRow γ) (ω : Tape) (s : ℕ)
    (a : β) (t : ℕ) (b : γ) (u k : ℕ) :
    Progress.Evaluates (p.pairStep q ω) (.inl (p.start s)) ((a,t),(b,u)) k ↔
      ∃ i j, Progress.Evaluates (p.step ω) (p.start s) (a,t) i ∧
        Progress.Evaluates ((q a).step ω) ((q a).start t) (b,u) j ∧ k=i+j := by
  constructor
  · intro h
    obtain ⟨first,i,j,hi,hj,hk⟩ := Progress.sequential_left_inv h
    have hs := Progress.family_evaluates_inv
      (f := fun first : β × ℕ => Progress.mapReturn (fun r => (first,r)) ((q first.1).step ω)) hj
    obtain ⟨r,hr,he⟩ := Progress.mapReturn_evaluates_inv hs
    simp only [Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩
    exact ⟨i,j,hi,hr,hk⟩
  · rintro ⟨i,j,hi,hj,rfl⟩
    exact Progress.sequential_evaluates hi (Progress.family_evaluates
      (Progress.mapReturn_evaluates hj))

theorem pair_joint (q : β → PreparedRow γ) (s : ℕ) (a : β) (b : γ) :
    {ω | ∃ t u k, Progress.Evaluates (p.pairStep q ω) (.inl (p.start s)) ((a,t),(b,u)) k}=
      p.joint q s a b := by
  ext ω
  simp only [Set.mem_ofPred_eq,pair_evaluates_iff,joint,returns]
  constructor
  · rintro ⟨t,u,k,i,j,hi,hj,_⟩; exact ⟨t,i,hi,u,j,hj⟩
  · rintro ⟨t,i,hi,u,j,hj⟩; exact ⟨t,u,i+j,i,j,hi,hj,rfl⟩

/-- Joint mass belongs to the actual sequential machine, not an independent
product machine or a restarted tape. Both outputs are retained. -/
theorem pair_joint_mass (q : β → PreparedRow γ) (s : ℕ) (a : β) (b : γ) :
    law {ω | ∃ t u k, Progress.Evaluates (p.pairStep q ω) (.inl (p.start s))
      ((a,t),(b,u)) k}=law (p.returns s a)*law ((q a).returns 0 b) := by
  rw [p.pair_joint,p.joint_mass]

theorem evaluates_cursor {ω : Tape} {s : ℕ} {a : β} {t k : ℕ}
    (h : Progress.Evaluates (p.step ω) (p.start s) (a,t) k) : t=s+k := by
  obtain ⟨r,c,hc,ha,ht,hk⟩ := (p.evaluates_iff _ _ _ _ _).mp h
  omega

/-- Full joint value/cursor/work atom factorization. The first cursor is s+i,
the second s+i+j; i and j count the actual bit inspections in each draw. -/
theorem pair_atom_mass (q : β → PreparedRow γ) (s i j : ℕ) (a : β) (b : γ) :
    law {ω | Progress.Evaluates (p.pairStep q ω) (.inl (p.start s))
      ((a,s+i),(b,s+i+j)) (i+j)}=
      law {ω | Progress.Evaluates (p.step ω) (p.start s) (a,s+i) i}*
      law {ω | Progress.Evaluates ((q a).step ω) ((q a).start 0) (b,j) j} := by
  have he : {ω | Progress.Evaluates (p.pairStep q ω) (.inl (p.start s))
      ((a,s+i),(b,s+i+j)) (i+j)}=
      {ω | Progress.Evaluates (p.step ω) (p.start s) (a,s+i) i} ∩
      CoinSuffix.suffix (s+i) ⁻¹' {ω | Progress.Evaluates ((q a).step ω) ((q a).start 0) (b,j) j} := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_preimage,
      pair_evaluates_iff,evaluates_shift]
    constructor
    · rintro ⟨i',j',hi,hj,hk⟩
      have hcur := p.evaluates_cursor hi
      have he : i'=i := by omega
      have hj' : j'=j := by omega
      subst i'; subst j'
      exact ⟨hi,hj⟩
    · rintro ⟨hi,hj⟩; exact ⟨i,j,hi,hj,rfl⟩
  rw [he]
  exact p.evaluates_suffix_mass _ _ _ _ _
    (ProbabilityProgress.measurable_evaluates _ (q a).measurableSteps _ _ _)

/-- Deliberate tape-reuse control: restart the second identical row at s. -/
def reusedPairStep (s : ℕ) (ω : Tape) :=
  Progress.sequential (p.step ω) (second (fun _ => p) ω)
    (fun first => (first,p.start s))

theorem reused_equal {s : ℕ} {ω : Tape} {a b : β} {t u k : ℕ}
    (h : Progress.Evaluates (p.reusedPairStep s ω) (.inl (p.start s)) ((a,t),(b,u)) k) : a=b := by
  obtain ⟨first,i,j,hi,hj,_⟩ := Progress.sequential_left_inv h
  have hs := Progress.family_evaluates_inv
    (f := fun first : β × ℕ => Progress.mapReturn (fun r => (first,r)) (p.step ω)) hj
  obtain ⟨r,hr,he⟩ := Progress.mapReturn_evaluates_inv hs
  simp only [Prod.mk.injEq] at he
  rcases he with ⟨rfl,rfl⟩
  exact congrArg Prod.fst (hi.unique hr).1

theorem reused_off_diagonal (s : ℕ) (a b : β) (h : a≠b) :
    law {ω | ∃ t u k, Progress.Evaluates (p.reusedPairStep s ω) (.inl (p.start s))
      ((a,t),(b,u)) k}=0 := by
  have he : {ω | ∃ t u k, Progress.Evaluates (p.reusedPairStep s ω) (.inl (p.start s))
      ((a,t),(b,u)) k}=∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
    rintro ⟨t,u,k,hk⟩
    exact h (p.reused_equal hk)
  rw [he,measure_empty]

end Applications.Probability.PreparedRow

namespace Applications.Probability.Table
open CoinPaths
open scoped ENNReal
variable {α β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

theorem sequential_joint_mass {m n : ℕ} (t : Table α β) (u : Table β γ)
    (e : Fin m ≃ β) (f : Fin n ≃ γ) (x : α) (a : β) (b : γ) (s : ℕ) :
    law {ω | ∃ v w k, Progress.Evaluates ((t.prepare e x).pairStep (u.prepare f) ω)
      (.inl ((t.prepare e x).start s)) ((a,v),(b,w)) k}=
      mass (t.entry x a)*mass (u.entry a b) := by
  rw [PreparedRow.pair_joint_mass,t.prepare_returns_mass,u.prepare_returns_mass]

end Applications.Probability.Table

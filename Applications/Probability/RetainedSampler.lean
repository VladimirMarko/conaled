import Applications.Probability.TableSamplerComposition

/-! Three sequential prepared rows retain their outputs and actual cursors.
The second and third rows may depend on previously sampled values. -/
namespace Applications.Probability.RetainedSampler
open CoinPaths CoinSuffix MeasureTheory
open scoped ENNReal
variable {α β γ : Type}

def tail (q : α → PreparedRow β) (r : α → β → PreparedRow γ) (ω : Tape) :=
  Progress.family (fun first : α × ℕ =>
    Progress.mapReturn (fun rest => (first,rest)) ((q first.1).pairStep (r first.1) ω))

def step (p : PreparedRow α) (q : α → PreparedRow β)
    (r : α → β → PreparedRow γ) (ω : Tape) :=
  Progress.sequential (p.step ω) (tail q r ω)
    (fun first => (first,Sum.inl ((q first.1).start first.2)))

theorem evaluates_iff (p : PreparedRow α) (q : α → PreparedRow β)
    (r : α → β → PreparedRow γ) (ω : Tape) (s : ℕ)
    (a : α) (t : ℕ) (b : β) (u : ℕ) (c : γ) (v k : ℕ) :
    Progress.Evaluates (step p q r ω) (.inl (p.start s)) ((a,t),(b,u),(c,v)) k ↔
      ∃ i j l, Progress.Evaluates (p.step ω) (p.start s) (a,t) i ∧
        Progress.Evaluates ((q a).step ω) ((q a).start t) (b,u) j ∧
        Progress.Evaluates ((r a b).step ω) ((r a b).start u) (c,v) l ∧ k=i+(j+l) := by
  constructor
  · intro h
    obtain ⟨first,i,n,hi,hn,hk⟩ := Progress.sequential_left_inv h
    have ht := Progress.family_evaluates_inv
      (f := fun first : α × ℕ => Progress.mapReturn (fun rest => (first,rest))
        ((q first.1).pairStep (r first.1) ω)) hn
    obtain ⟨rest,hr,he⟩ := Progress.mapReturn_evaluates_inv ht
    simp only [Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩
    obtain ⟨j,l,hj,hl,rfl⟩ := ((q a).pair_evaluates_iff (r a) ω t b u c v n).mp hr
    exact ⟨i,j,l,hi,hj,hl,hk⟩
  · rintro ⟨i,j,l,hi,hj,hl,rfl⟩
    exact Progress.sequential_evaluates hi (Progress.family_evaluates
      (Progress.mapReturn_evaluates (((q a).pair_evaluates_iff (r a) ω t b u c v
        (j+l)).mpr ⟨j,l,hj,hl,rfl⟩)))

theorem returns_shift_add (p : PreparedRow α) (ω : Tape) (s v : ℕ) (a : α) :
    suffix s ω ∈ p.returns v a ↔ ω ∈ p.returns (s+v) a := by
  have hs : suffix v (suffix s ω)=suffix (s+v) ω := by
    funext i; simp [suffix,Nat.add_assoc]
  rw [← p.returns_shift (suffix s ω) v a,hs,p.returns_shift]

theorem joint_atoms (p : PreparedRow α) (q : α → PreparedRow β)
    (ω : Tape) (s : ℕ) (a : α) (b : β) :
    ω ∈ p.joint q s a b ↔ ∃ n, ∃ ticket : Fin p.total,
      BoundedUniform.Accept p.total ω s n ticket ∧ p.select ticket=a ∧
        ω ∈ (q a).returns (s+BoundedUniform.width p.total*(n+1)) b := by
  constructor
  · rintro ⟨t,k,h,hr⟩
    obtain ⟨n,ticket,hn,ha,rfl,_⟩ := (p.evaluates_iff _ _ _ _ _).mp h
    exact ⟨n,ticket,hn,ha,hr⟩
  · rintro ⟨n,ticket,hn,ha,hr⟩
    exact ⟨_,_,(p.evaluates_iff _ _ _ _ _).mpr ⟨n,ticket,hn,ha,rfl,rfl⟩,hr⟩

theorem joint_shift (p : PreparedRow α) (q : α → PreparedRow β)
    (ω : Tape) (s v : ℕ) (a : α) (b : β) :
    suffix s ω ∈ p.joint q v a b ↔ ω ∈ p.joint q (s+v) a b := by
  simp only [joint_atoms,BoundedUniform.accept_suffix_iff,returns_shift_add,Nat.add_assoc]

theorem measurable_joint (p : PreparedRow α) (q : α → PreparedRow β)
    (s : ℕ) (a : α) (b : β) : MeasurableSet (p.joint q s a b) := by
  simp only [PreparedRow.joint,Set.ofPred_exists]
  exact MeasurableSet.iUnion fun t => MeasurableSet.iUnion fun k =>
    (ProbabilityProgress.measurable_evaluates _ p.measurableSteps _ _ _).inter
      ((q a).measurable_returns t b)

/-- All three outputs are retained; the cursor and work are existentially
hidden only at this value-law observation. -/
def event (p : PreparedRow α) (q : α → PreparedRow β)
    (r : α → β → PreparedRow γ) (s : ℕ) (a : α) (b : β) (c : γ) : Set Tape :=
  {ω | ∃ t u v k, Progress.Evaluates (step p q r ω) (.inl (p.start s))
    ((a,t),(b,u),(c,v)) k}

theorem event_eq (p : PreparedRow α) (q : α → PreparedRow β)
    (r : α → β → PreparedRow γ) (s : ℕ) (a : α) (b : β) (c : γ) :
    event p q r s a b c = {ω | ∃ t i,
      Progress.Evaluates (p.step ω) (p.start s) (a,t) i ∧
        suffix t ω ∈ (q a).joint (r a) 0 b c} := by
  ext ω
  simp only [event,Set.mem_ofPred_eq,evaluates_iff,joint_shift,Nat.add_zero]
  simp only [PreparedRow.joint,PreparedRow.returns,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t,u,v,k,i,j,l,hi,hj,hl,_⟩
    exact ⟨t,i,hi,u,j,hj,v,l,hl⟩
  · rintro ⟨t,i,hi,u,j,hj,v,l,hl⟩
    exact ⟨t,u,v,i+(j+l),i,j,l,hi,hj,hl,rfl⟩

theorem event_mass (p : PreparedRow α) (q : α → PreparedRow β)
    (r : α → β → PreparedRow γ) (s : ℕ) (a : α) (b : β) (c : γ) :
    law (event p q r s a b c) =
      law (p.returns s a) * (law ((q a).returns 0 b) * law ((r a b).returns 0 c)) := by
  rw [event_eq,p.stopped_mass _ _ _ (measurable_joint _ _ _ _ _),PreparedRow.joint_mass]

theorem measurable_event (p : PreparedRow α) (q : α → PreparedRow β)
    (r : α → β → PreparedRow γ) (s : ℕ) (a : α) (b : β) (c : γ) :
    MeasurableSet (event p q r s a b c) := by
  rw [event_eq]
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion fun t => MeasurableSet.iUnion fun k =>
    (ProbabilityProgress.measurable_evaluates _ p.measurableSteps _ _ _).inter
      ((measurable_suffix t) (measurable_joint _ _ _ _ _))

theorem event_unique {p : PreparedRow α} {q : α → PreparedRow β}
    {r : α → β → PreparedRow γ} {s : ℕ} {ω : Tape}
    {a a' : α} {b b' : β} {c c' : γ}
    (h : ω ∈ event p q r s a b c) (h' : ω ∈ event p q r s a' b' c') :
    a=a' ∧ b=b' ∧ c=c' := by
  obtain ⟨t,u,v,k,h⟩ := h
  obtain ⟨t',u',v',k',h'⟩ := h'
  have he := (h.unique h').1
  exact ⟨congrArg (fun z => z.1.1) he,congrArg (fun z => z.2.1.1) he,
    congrArg (fun z => z.2.2.1) he⟩

/-- Forget cursors only at the declared value observation. -/
def values (z : (α × ℕ) × (β × ℕ) × (γ × ℕ)) : (α × β) × γ :=
  ((z.1.1,z.2.1.1),z.2.2.1)

/-- The finite value subprobability is assembled from actual execution events.
This mathematical observation introduces no selection into executable code. -/
noncomputable def valueLaw [Fintype α] [Fintype β] [Fintype γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (p : PreparedRow α) (q : α → PreparedRow β) (r : α → β → PreparedRow γ) (s : ℕ) :
    Measure ((α × β) × γ) :=
  ∑ z, law (event p q r s z.1.1 z.1.2 z.2) • Measure.dirac z

theorem valueLaw_apply [Fintype α] [Fintype β] [Fintype γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (p : PreparedRow α) (q : α → PreparedRow β) (r : α → β → PreparedRow γ)
    (s : ℕ) (B : Set ((α × β) × γ)) (hB : MeasurableSet B) :
    valueLaw p q r s B = law {ω | ∃ z k,
      Progress.Evaluates (step p q r ω) (.inl (p.start s)) z k ∧ values z ∈ B} := by
  classical
  let E (z : (α × β) × γ) := if z ∈ B then event p q r s z.1.1 z.1.2 z.2 else ∅
  have he : {ω | ∃ z k, Progress.Evaluates (step p q r ω) (.inl (p.start s)) z k ∧
      values z ∈ B} = ⋃ z, E z := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · rintro ⟨⟨⟨a,t⟩,⟨b,u⟩,⟨c,v⟩⟩,k,h,hB⟩
      refine ⟨((a,b),c),?_⟩
      simp only [values] at hB
      simp only [E,hB,ite_true]
      exact ⟨t,u,v,k,h⟩
    · rintro ⟨⟨⟨a,b⟩,c⟩,h⟩
      by_cases hz : ((a,b),c) ∈ B
      · simp only [E,hz,ite_true] at h
        obtain ⟨t,u,v,k,h⟩ := h
        exact ⟨_,k,h,hz⟩
      · simp only [E,hz,ite_false,Set.mem_empty_iff_false] at h
  have hd : Pairwise (fun z w => Disjoint (E z) (E w)) := by
    intro z w hzw
    by_cases hz : z ∈ B
    · by_cases hw : w ∈ B
      · simp only [E,hz,hw,ite_true]
        apply Set.disjoint_left.mpr
        intro ω h h'
        obtain ⟨ha,hb,hc⟩ := event_unique h h'
        exact hzw (Prod.ext (Prod.ext ha hb) hc)
      · simp [E,hw]
    · simp [E,hz]
  have hm : ∀ z, MeasurableSet (E z) := by
    intro z
    by_cases hz : z ∈ B
    · simpa only [E,hz,ite_true] using measurable_event p q r s z.1.1 z.1.2 z.2
    · simp [E,hz]
  rw [he,measure_iUnion hd hm,tsum_fintype,valueLaw,Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : z ∈ B <;> simp [E,hz,Measure.smul_apply,Measure.dirac_apply' _ hB]

theorem ae_terminates [Countable α] [Countable β]
    (p : PreparedRow α) (q : α → PreparedRow β) (r : α → β → PreparedRow γ) (s : ℕ) :
    ∀ᵐ ω ∂law, Progress.Terminates (step p q r ω) (.inl (p.start s)) := by
  have hq : ∀ᵐ ω ∂law, ∀ a t, Progress.Terminates ((q a).step ω) ((q a).start t) :=
    ae_all_iff.mpr fun a => ae_all_iff.mpr fun t => (q a).ae_terminates t
  have hr : ∀ᵐ ω ∂law, ∀ a b u, Progress.Terminates ((r a b).step ω) ((r a b).start u) :=
    ae_all_iff.mpr fun a => ae_all_iff.mpr fun b => ae_all_iff.mpr fun u =>
      (r a b).ae_terminates u
  filter_upwards [p.ae_terminates s,hq,hr] with ω hp hq hr
  obtain ⟨⟨a,t⟩,i,hi⟩ := hp
  obtain ⟨⟨b,u⟩,j,hj⟩ := hq a t
  obtain ⟨⟨c,v⟩,l,hl⟩ := hr a b u
  exact ⟨_,_,(evaluates_iff _ _ _ _ _ _ _ _ _ _ _ _).mpr ⟨i,j,l,hi,hj,hl,rfl⟩⟩

end Applications.Probability.RetainedSampler

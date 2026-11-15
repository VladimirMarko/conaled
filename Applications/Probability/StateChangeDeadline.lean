import Applications.Probability.StateChangeWork
import Applications.Probability.StateChangeSampler

/-! Quantitative waiting bounds for suppressed self-transitions. -/
namespace Applications.Probability.StateChangeDeadline
open CoinPaths CoinSuffix MeasureTheory
open scoped ENNReal
variable {α : Type} [DecidableEq α]

/-- A distinct return occurs within the next attempts raw rows, each of which
finishes within its bit deadline. Every continuation uses its returned cursor. -/
def fastChange (p : α → PreparedRow α) : ℕ → α → ℕ → Set Tape
  | 0,_,_ => ∅
  | attempts+1,x,b => {ω | ∃ a t k,
      Progress.Evaluates ((p x).step ω) ((p x).start 0) (a,t) k ∧ k≤b ∧
        (a ≠ x ∨ suffix t ω ∈ fastChange p attempts x b)}

omit [DecidableEq α] in
theorem measurable_fastChange [Countable α] (p : α → PreparedRow α)
    (attempts : ℕ) (x : α) (b : ℕ) : MeasurableSet (fastChange p attempts x b) := by
  induction attempts with
  | zero => exact MeasurableSet.empty
  | succ attempts ih =>
    simp only [fastChange,Set.ofPred_exists,Set.ofPred_and,Set.ofPred_or]
    exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun t => MeasurableSet.iUnion fun k =>
      (ProbabilityProgress.measurable_evaluates _ (p x).measurableSteps _ _ _).inter
        ((MeasurableSet.const _).inter ((MeasurableSet.const _).union
          ((measurable_suffix t) ih)))

/-- The two failure sources are staying in the same state and exceeding a raw
row's bit deadline. Dependence between consecutive rows is not discarded. -/
theorem fastChange_failure_bound [Countable α] (p : α → PreparedRow α)
    (x : α) (b : ℕ) (r q : ℝ≥0∞) (hr : r≤1)
    (hself : law ((p x).returns 0 x)≤r)
    (hrow : law {ω | Progress.search ((p x).step ω) b ((p x).start 0)=none}≤q)
    (attempts : ℕ) :
    law (fastChange p attempts x b)ᶜ≤r^attempts+attempts*q := by
  induction attempts with
  | zero => simp [fastChange]
  | succ attempts ih =>
    let E : Set Tape := {ω | ∃ t k,
      Progress.Evaluates ((p x).step ω) ((p x).start 0) (x,t) k ∧
        suffix t ω ∈ (fastChange p attempts x b)ᶜ}
    have hsub : (fastChange p (attempts+1) x b)ᶜ ⊆
        {ω | Progress.search ((p x).step ω) b ((p x).start 0)=none} ∪ E := by
      intro ω h
      cases hs : Progress.search ((p x).step ω) b ((p x).start 0) with
      | none => exact .inl hs
      | some result =>
        rcases result with ⟨⟨a,t⟩,k⟩
        have he := Progress.search_sound hs
        have hk := ProbabilityProgress.search_cost_le hs
        by_cases ha : a=x
        · subst a
          refine .inr ⟨t,k,he,?_⟩
          intro hrest
          exact h ⟨x,t,k,he,hk,.inr hrest⟩
        · exact False.elim (h ⟨a,t,k,he,hk,.inl ha⟩)
    calc
      _ ≤ law ({ω | Progress.search ((p x).step ω) b ((p x).start 0)=none} ∪ E) := measure_mono hsub
      _ ≤ law {ω | Progress.search ((p x).step ω) b ((p x).start 0)=none}+law E := measure_union_le _ _
      _ = law {ω | Progress.search ((p x).step ω) b ((p x).start 0)=none}+
          law ((p x).returns 0 x)*law (fastChange p attempts x b)ᶜ := by
        rw [(p x).stopped_mass 0 x _ (measurable_fastChange p attempts x b).compl]
      _ ≤ q+r*(r^attempts+attempts*q) := add_le_add hrow (mul_le_mul' hself ih)
      _ = r^(attempts+1)+q+r*(attempts*q) := by rw [pow_succ]; ring
      _ ≤ r^(attempts+1)+q+1*(attempts*q) := by gcongr
      _ = r^(attempts+1)+(attempts+1 : ℕ)*q := by
        simp only [one_mul,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
        ac_rfl

open StateChangeSampler

theorem fastChange_delivers (p : α → PreparedRow α) (attempts : ℕ) (x : α)
    (b s : ℕ) (ω : Tape) (h : suffix s ω ∈ fastChange p attempts x b) :
    ∃ a u k, ChangeTrace p ω x ((p x).start s) a u k ∧ k≤attempts*b := by
  induction attempts generalizing s with
  | zero => exact h.elim
  | succ attempts ih =>
    obtain ⟨a,u,k,hrow,hk,rest⟩ := h
    have row := ((p x).evaluates_shift ω s u k a).mp hrow
    by_cases ha : a=x
    · subst a
      have hcomp : suffix u (suffix s ω)=suffix (s+u) ω := by
        funext i; simp [suffix,Nat.add_assoc]
      have hrest := rest.resolve_left (not_not_intro rfl)
      rw [hcomp] at hrest
      obtain ⟨a,v,j,tail,hj⟩ := ih (s+u) hrest
      exact ⟨a,v,k+j,.self row tail,by nlinarith⟩
    · exact ⟨a,s+u,k,.change row ha,by nlinarith⟩

theorem change_timeout_bound [Fintype α] (p : α → PreparedRow α) (x : α)
    (b attempts : ℕ) (r q : ℝ≥0∞) (hr : r≤1)
    (hself : law ((p x).returns 0 x)≤r)
    (hrow : law {ω | Progress.search ((p x).step ω) b ((p x).start 0)=none}≤q) :
    law {ω | Progress.search (TableProducer.changes p ω) (attempts*b)
      (TableProducer.start p x 0)=none}≤r^attempts+attempts*q := by
  have hsub : {ω | Progress.search (TableProducer.changes p ω) (attempts*b)
      (TableProducer.start p x 0)=none} ⊆ (fastChange p attempts x b)ᶜ := by
    intro ω h hf
    have hf' : suffix 0 ω ∈ fastChange p attempts x b := by
      have he : CoinSuffix.suffix 0 ω=ω := by funext i; exact congrArg ω (Nat.zero_add i)
      rw [he]
      exact hf
    obtain ⟨a,u,k,ht,hk⟩ := fastChange_delivers p attempts x b 0 ω hf'
    have hs := Progress.search_complete ht.evaluates hk
    change Progress.search _ _ (TableProducer.start p x 0)=_ at hs
    rw [h] at hs
    contradiction
  exact (measure_mono hsub).trans (fastChange_failure_bound p x b r q hr hself hrow attempts)

/-- Each successive actual changed output arrives by its local bit deadline. -/
def fastPrefixes (p : α → PreparedRow α) : ℕ → α → ℕ → Set Tape
  | 0,_,_ => Set.univ
  | n+1,x,b => {ω | ∃ a u k, Progress.Evaluates (TableProducer.changes p ω)
      (TableProducer.start p x 0) (a,TableProducer.start p a u) k ∧ k≤b ∧
        suffix u ω ∈ fastPrefixes p n a b}

theorem measurable_fastPrefixes [Countable α] (p : α → PreparedRow α)
    (n : ℕ) (x : α) (b : ℕ) : MeasurableSet (fastPrefixes p n x b) := by
  induction n generalizing x with
  | zero => exact MeasurableSet.univ
  | succ n ih =>
    simp only [fastPrefixes,Set.ofPred_exists,Set.ofPred_and]
    exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun u => MeasurableSet.iUnion fun k =>
      (ProbabilityProgress.measurable_evaluates _ (StateChangeSampler.measurableSteps p) _ _ _).inter
        ((MeasurableSet.const _).inter ((measurable_suffix u) (ih a)))

theorem fastPrefixes_delivers (p : α → PreparedRow α) (n : ℕ) (x : α)
    (b s : ℕ) (ω : Tape) (h : suffix s ω ∈ fastPrefixes p n x b) :
    ∃ ys z k, ys.length=n ∧ k≤n*b ∧
      Progress.Delivers (TableProducer.changes p ω) (TableProducer.start p x s) ys z k := by
  induction n generalizing x s with
  | zero => exact ⟨[],_,0,rfl,by simp,.nil _⟩
  | succ n ih =>
    obtain ⟨a,u,k,hchange,hk,rest⟩ := h
    have hcomp : suffix u (suffix s ω)=suffix (s+u) ω := by
      funext i; simp [suffix,Nat.add_assoc]
    rw [hcomp] at rest
    obtain ⟨ys,z,j,hlen,hj,hd⟩ := ih a (s+u) rest
    have ht := (trace_iff_evaluates p (suffix s ω) x a ((p x).start 0) u k).mpr hchange
    have hs := (ht.shift s).evaluates
    refine ⟨a::ys,z,k+j,by simp [hlen],by nlinarith,?_⟩
    exact .cons (by simpa [TableProducer.start] using hs) hd

theorem fastPrefixes_failure_bound [Fintype α] (t : Table α α)
    (positive : ∀ x,0<exit t x) (p : α → PreparedRow α)
    (hp : ∀ x s a, law ((p x).returns s a)=mass (t.entry x a))
    (b : ℕ) (q : ℝ≥0∞)
    (hb : ∀ x,law {ω | Progress.search (TableProducer.changes p ω) b
      (TableProducer.start p x 0)=none}≤q) (n : ℕ) (x : α) :
    law (fastPrefixes p n x b)ᶜ≤n*q := by
  induction n generalizing x with
  | zero => simp [fastPrefixes]
  | succ n ih =>
    let E (a : α) : Set Tape := {ω | ∃ u k, Progress.Evaluates (TableProducer.changes p ω)
      (TableProducer.start p x 0) (a,TableProducer.start p a u) k ∧
        suffix u ω ∈ (fastPrefixes p n a b)ᶜ}
    have hsub : (fastPrefixes p (n+1) x b)ᶜ ⊆
        {ω | Progress.search (TableProducer.changes p ω) b
          (TableProducer.start p x 0)=none} ∪ ⋃ a,E a := by
      intro ω h
      cases hs : Progress.search (TableProducer.changes p ω) b (TableProducer.start p x 0) with
      | none => exact .inl hs
      | some result =>
        rcases result with ⟨⟨a,z⟩,k⟩
        have he := Progress.search_sound hs
        have hk := ProbabilityProgress.search_cost_le hs
        obtain ⟨u,rfl,ht⟩ := trace_of_change he
        refine .inr (Set.mem_iUnion.mpr ⟨a,u,k,he,?_⟩)
        intro rest
        exact h ⟨a,u,k,he,hk,rest⟩
    calc
      _ ≤ law ({ω | Progress.search (TableProducer.changes p ω) b
          (TableProducer.start p x 0)=none} ∪ ⋃ a,E a) := measure_mono hsub
      _ ≤ law {ω | Progress.search (TableProducer.changes p ω) b
          (TableProducer.start p x 0)=none}+law (⋃ a,E a) := measure_union_le _ _
      _ ≤ q+∑' a,law (E a) := add_le_add (hb x) (measure_iUnion_le _)
      _ = q+∑ a,mass ((jump t positive).entry x a)*law (fastPrefixes p n a b)ᶜ := by
        simp only [tsum_fintype]
        congr 1
        exact Finset.sum_congr rfl fun a _ => change_stopped_mass_evaluates t positive p hp x a 0 _
          (measurable_fastPrefixes p n a b).compl
      _ ≤ q+∑ a,mass ((jump t positive).entry x a)*(n*q) := by
        gcongr with a
        exact ih a
      _ = (n+1 : ℕ)*q := by
        rw [← Finset.sum_mul,← mass_sum _ _ (fun a _ => (jump t positive).nonneg x a),
          (jump t positive).sum_row,mass_one]
        simp [Nat.cast_add,add_mul,add_comm]

/-- Actual failure to deliver the requested number of changes by a bit deadline. -/
def deadline (p : α → PreparedRow α) (n : ℕ) (x : α) (s bits : ℕ) : Set Tape :=
  (ProbabilityProgress.prefixDelivered (TableProducer.changes p) (TableProducer.start p x s) n bits)ᶜ

theorem deadline_bound [Fintype α] (t : Table α α) (positive : ∀ x,0<exit t x)
    (p : α → PreparedRow α)
    (hp : ∀ x s a, law ((p x).returns s a)=mass (t.entry x a))
    (r : ℝ≥0∞) (hr : r<1) (hself : ∀ x,mass (t.entry x x)≤r)
    (n : ℕ) (x : α) (s attempts blocks : ℕ) :
    law (deadline p n x s (n*(attempts*(SamplerExpectedWork.maxWidth p*blocks))))≤
      n*(r^attempts+attempts*(2⁻¹ : ℝ≥0∞)^blocks) := by
  let b := attempts*(SamplerExpectedWork.maxWidth p*blocks)
  have hb (x : α) : law {ω | Progress.search (TableProducer.changes p ω) b
      (TableProducer.start p x 0)=none}≤r^attempts+attempts*(2⁻¹ : ℝ≥0∞)^blocks :=
    change_timeout_bound p x _ attempts r _ hr.le
      (by rw [hp]; exact hself x) (SamplerExpectedWork.row_deadline p x blocks)
  have hsub : deadline p n x s (n*b) ⊆ suffix s ⁻¹' (fastPrefixes p n x b)ᶜ := by
    intro ω h hf
    obtain ⟨ys,z,k,hlen,hk,hd⟩ := fastPrefixes_delivers p n x b s ω hf
    exact h ⟨ys,z,k,hlen,hk,hd⟩
  calc
    _ ≤ law (suffix s ⁻¹' (fastPrefixes p n x b)ᶜ) := measure_mono hsub
    _ = law (fastPrefixes p n x b)ᶜ := by
      rw [← Measure.map_apply (measurable_suffix s) (measurable_fastPrefixes p n x b).compl,suffix_law]
    _ ≤ _ := fastPrefixes_failure_bound t positive p hp b _ hb n x

/-- Positive exits on a finite class always admit a strict uniform self bound. -/
theorem exists_self_bound [Fintype α] (t : Table α α) (positive : ∀ x,0<exit t x) :
    ∃ r : ℝ≥0∞,r<1 ∧ ∀ x,mass (t.entry x x)≤r := by
  have hx (x : α) : mass (t.entry x x)<1 := by
    change ENNReal.ofReal (t.entry x x : ℝ)<1
    rw [← ENNReal.ofReal_one,ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    have h : t.entry x x<1 := by have := positive x; unfold exit at this; linarith
    exact_mod_cast h
  have hs : ∀ s : Finset α, ∃ r : ℝ≥0∞,r<1 ∧ ∀ x∈s,mass (t.entry x x)≤r := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0,by norm_num,by simp⟩
    | @insert x s hnot ih =>
      obtain ⟨r,hr,hb⟩ := ih
      refine ⟨max (mass (t.entry x x)) r,max_lt (hx x) hr,?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact le_max_left _ _
      · exact (hb y hy).trans (le_max_right _ _)
  obtain ⟨r,hr,hb⟩ := hs Finset.univ
  exact ⟨r,hr,fun x => hb x (Finset.mem_univ x)⟩

open SamplerWorkload SamplerWork

/-- Failure includes non-delivery even when every declared tariff is zero. -/
def workDeadline (load : Loader α) (p : α → PreparedRow α) (τ : Tariff)
    (o : Overhead) (compareCost setup n : ℕ) (x : α) (s budget : ℕ) : Set Tape :=
  {ω | ¬∃ ys z k, ys.length=n ∧
    Progress.Delivers (TableProducer.changes p ω) (TableProducer.start p x s) ys z k ∧
      setup+(StateChangeWork.workload load τ o compareCost ω x s k).2≤budget}

theorem measurable_workDeadline [Countable α] (load : Loader α) (p : α → PreparedRow α)
    (τ : Tariff) (o : Overhead) (compareCost setup n : ℕ) (x : α) (s budget : ℕ) :
    MeasurableSet (workDeadline load p τ o compareCost setup n x s budget) := by
  change MeasurableSet ({ω | ∃ ys z k, ys.length=n ∧
    Progress.Delivers (TableProducer.changes p ω) (TableProducer.start p x s) ys z k ∧
      setup+(StateChangeWork.workload load τ o compareCost ω x s k).2≤budget}ᶜ)
  apply MeasurableSet.compl
  simp only [Set.ofPred_exists,Set.ofPred_and]
  exact MeasurableSet.iUnion fun ys => MeasurableSet.iUnion fun z => MeasurableSet.iUnion fun k =>
    (MeasurableSet.const _).inter
      ((ProbabilityProgress.measurable_delivers _ (StateChangeSampler.measurableSteps p) _ _ _ _).inter
        (measurableSet_le (measurable_const.add
          (StateChangeWork.measurable_workload load τ o compareCost x s k)) measurable_const))

/-- Setup, every suppressed row, eager prefetch, comparisons and retained output
handling are included. This is a bound on the actual stopped measured workload. -/
theorem workDeadline_bound [Fintype α] (t : Table α α) (positive : ∀ x,0<exit t x)
    (p : α → PreparedRow α)
    (hp : ∀ x s a, law ((p x).returns s a)=mass (t.entry x a))
    (load : Loader α) (he : ∀ x,(load x).1=p x) (τ : Tariff) (o : Overhead)
    (compareCost setup M L : ℕ) (hm : ∀ x,perBitBound (p x) τ≤M)
    (hl : ∀ x,(load x).2≤L) (r : ℝ≥0∞) (hr : r<1)
    (hself : ∀ x,mass (t.entry x x)≤r) (n : ℕ) (x : α) (s attempts blocks : ℕ) :
    law (workDeadline load p τ o compareCost setup n x s
      (setup+(load x).2+initialization τ+
        (n*(attempts*(SamplerExpectedWork.maxWidth p*blocks)))*
          (M+L+initialization τ+compareCost+o.emit)+n*o.finish))≤
      n*(r^attempts+attempts*(2⁻¹ : ℝ≥0∞)^blocks) := by
  let bits := n*(attempts*(SamplerExpectedWork.maxWidth p*blocks))
  have hsub : workDeadline load p τ o compareCost setup n x s
      (setup+(load x).2+initialization τ+bits*(M+L+initialization τ+compareCost+o.emit)+n*o.finish) ⊆
        deadline p n x s bits := by
    intro ω h hd
    obtain ⟨ys,z,k,hlen,hk,hd⟩ := hd
    have hc := StateChangeWork.workload_bound load p he τ o compareCost ω M L hm hl x s hd
    rw [hlen] at hc
    have hk' := Nat.mul_le_mul_right (M+L+initialization τ+compareCost+o.emit) hk
    exact h ⟨ys,z,k,hlen,hd,by omega⟩
  exact (measure_mono hsub).trans (deadline_bound t positive p hp r hr hself n x s attempts blocks)

end Applications.Probability.StateChangeDeadline

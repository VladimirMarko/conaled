import Applications.Probability.RationalRow
import Applications.Probability.BoundedUniformLaw
import Applications.Progress.Sequential

/-! Exact operational sampling of prepared finite rational rows. -/
namespace Applications.Probability.PreparedRow
open CoinPaths MeasureTheory
open scoped ENNReal BigOperators
variable {β : Type} (p : PreparedRow β)

abbrev State := BoundedUniform.State
abbrev Return (β : Type) := β × ℕ

def start (s : ℕ) : State := BoundedUniform.start p.total s

def step (ω : Tape) : Progress.Machine State (Return β) :=
  Progress.mapReturn (fun a => (p.select a.1,a.2)) (BoundedUniform.step p.total ω)

/-- Every row return is exactly an interpreted bounded-sampler return. -/
theorem evaluates_codes (ω : Tape) (s : ℕ) (b : β) (t k : ℕ) :
    Progress.Evaluates (p.step ω) (p.start s) (b,t) k ↔
      ∃ a : Fin p.total, Progress.Evaluates (BoundedUniform.step p.total ω)
        (BoundedUniform.start p.total s) (a,t) k ∧ p.select a=b := by
  constructor
  · intro h
    obtain ⟨⟨a,u⟩,ha,he⟩ := Progress.mapReturn_evaluates_inv h
    simp only [Prod.mk.injEq] at he
    rcases he with ⟨hb,rfl⟩
    exact ⟨a,ha,hb⟩
  · rintro ⟨a,ha,rfl⟩
    exact Progress.mapReturn_evaluates ha

theorem evaluates_iff (ω : Tape) (s : ℕ) (b : β) (t k : ℕ) :
    Progress.Evaluates (p.step ω) (p.start s) (b,t) k ↔
      ∃ r, ∃ a : Fin p.total, BoundedUniform.Accept p.total ω s r a ∧
        p.select a=b ∧ t=s+BoundedUniform.width p.total*(r+1) ∧
        k=BoundedUniform.width p.total*(r+1) := by
  rw [evaluates_codes]
  constructor
  · rintro ⟨a,ha,hb⟩
    obtain ⟨r,hr,ht,hk⟩ := BoundedUniform.accept_of_evaluates ha
    exact ⟨r,a,hr,hb,ht,hk⟩
  · rintro ⟨r,a,ha,hb,rfl,rfl⟩
    exact ⟨a,BoundedUniform.evaluates_of_accept ha,hb⟩

def returns (s : ℕ) (b : β) : Set Tape :=
  {ω | ∃ t k, Progress.Evaluates (p.step ω) (p.start s) (b,t) k}

theorem returns_eq (s : ℕ) (b : β) : p.returns s b=
    ⋃ a : Fin p.total, {ω | ω∈BoundedUniform.returns p.total s a ∧ p.select a=b} := by
  ext ω
  simp only [returns,Set.mem_ofPred_eq,Set.mem_iUnion,evaluates_codes,
    BoundedUniform.returns]
  constructor
  · rintro ⟨t,k,a,ha,hb⟩; exact ⟨a,⟨t,k,ha⟩,hb⟩
  · rintro ⟨a,⟨t,k,ha⟩,hb⟩; exact ⟨t,k,a,ha,hb⟩

theorem returns_mass [DecidableEq β] (s : ℕ) (b : β) :
    law (p.returns s b)=∑ a : Fin p.total, if p.select a=b then (p.total : ℝ≥0∞)⁻¹ else 0 := by
  classical
  rw [returns_eq,measure_iUnion]
  · simp only [tsum_fintype]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : p.select a=b
    · simp only [h,and_true,ite_true]; exact BoundedUniform.returns_mass _ _ _
    · simp [h]
  · intro a c hac
    apply Set.disjoint_left.mpr
    rintro ω ⟨⟨t,k,ha⟩,_⟩ ⟨⟨u,l,hc⟩,_⟩
    exact hac (congrArg Prod.fst (ha.unique hc).1)
  · intro a
    exact (BoundedUniform.measurableSet_returns _ _ _).inter (MeasurableSet.const _)

theorem measurableSteps : ProbabilityProgress.MeasurableSteps p.step := by
  intro q r
  have he : {ω | p.step ω q=r} =
      ({ω : Tape | ω q.1=false} ∩ {ω | p.step (fun _ => false) q=r}) ∪
      ({ω : Tape | ω q.1=true} ∩ {ω | p.step (fun _ => true) q=r}) := by
    ext ω
    cases hb : ω q.1 <;> simp [step,Progress.mapReturn,BoundedUniform.step,hb]
  rw [he]
  have hm : Measurable (fun ω : Tape => ω q.1) := measurable_pi_apply q.1
  exact ((hm (measurableSet_singleton false)).inter (MeasurableSet.const _)).union
    ((hm (measurableSet_singleton true)).inter (MeasurableSet.const _))

theorem terminates_iff (ω : Tape) (s : ℕ) :
    Progress.Terminates (p.step ω) (p.start s) ↔
      Progress.Terminates (BoundedUniform.step p.total ω) (BoundedUniform.start p.total s) := by
  constructor
  · rintro ⟨⟨b,t⟩,k,h⟩
    obtain ⟨a,ha,_⟩ := (p.evaluates_codes ω s b t k).mp h
    exact ⟨(a,t),k,ha⟩
  · rintro ⟨⟨a,t⟩,k,h⟩
    exact ⟨(p.select a,t),k,Progress.mapReturn_evaluates h⟩

theorem termination_mass (s : ℕ) :
    law (ProbabilityProgress.termination p.step (p.start s))=1 := by
  have he : ProbabilityProgress.termination p.step (p.start s)=
      ProbabilityProgress.termination (BoundedUniform.step p.total) (BoundedUniform.start p.total s) := by
    ext ω; exact p.terminates_iff ω s
  rw [he]
  exact BoundedUniform.termination_mass _ _ p.positive

theorem ae_terminates (s : ℕ) : ∀ᵐ ω ∂law, Progress.Terminates (p.step ω) (p.start s) := by
  filter_upwards [BoundedUniform.ae_terminates p.total s p.positive] with ω h
  exact (p.terminates_iff ω s).mpr h

theorem divergence_mass [Countable β] (s : ℕ) :
    law (ProbabilityProgress.termination p.step (p.start s))ᶜ=0 := by
  rw [prob_compl_eq_one_sub (ProbabilityProgress.measurable_termination _ p.measurableSteps _),
    p.termination_mass,tsub_self]

/-- Finite search with exactly one block retains its subprobability law. -/
theorem one_block_mass [DecidableEq β] (s : ℕ) (b : β) :
    law {ω | Progress.search (p.step ω) (BoundedUniform.width p.total) (p.start s)=
      some ((b,s+BoundedUniform.width p.total),BoundedUniform.width p.total)}=
      ∑ a : Fin p.total, if p.select a=b then (2⁻¹ : ℝ≥0∞)^BoundedUniform.width p.total else 0 := by
  have he : {ω | Progress.search (p.step ω) (BoundedUniform.width p.total) (p.start s)=
      some ((b,s+BoundedUniform.width p.total),BoundedUniform.width p.total)}=
      ⋃ a : Fin p.total, {ω | BoundedUniform.Accept p.total ω s 0 a ∧ p.select a=b} := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · intro h
      obtain ⟨a,ha,hb⟩ := (p.evaluates_codes _ _ _ _ _).mp (Progress.search_sound h)
      refine ⟨a,?_,hb⟩
      exact (BoundedUniform.evaluates_iff p.total ω s 0 a).mp (by simpa using ha)
    · rintro ⟨a,ha,hb⟩
      apply Progress.search_complete _ (le_refl _)
      apply (p.evaluates_codes _ _ _ _ _).mpr
      exact ⟨a,by simpa using BoundedUniform.evaluates_of_accept ha,hb⟩
  rw [he,measure_iUnion]
  · simp only [tsum_fintype]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : p.select a=b
    · simp only [h,and_true,ite_true]
      rw [BoundedUniform.accept_mass,pow_zero,one_mul]
    · simp [h]
  · intro a c hac
    exact (BoundedUniform.accept_disjoint p.total s (i := (0,a)) (j := (0,c))
      (by simpa using hac)).mono (fun _ h => h.1) (fun _ h => h.1)
  · intro a
    exact (BoundedUniform.measurableSet_accept p.total s 0 a).inter (MeasurableSet.const (p.select a=b))

/-- Operational value event, retaining missing mass rather than totalizing divergence. -/
def outputEvent (s : ℕ) (B : Set β) : Set Tape := {ω | ∃ b∈B, ω∈p.returns s b}

theorem outputEvent_mass [Fintype β] (s : ℕ) (B : Set β) [DecidablePred (·∈B)] :
    law (p.outputEvent s B)=∑ b, if b∈B then law (p.returns s b) else 0 := by
  classical
  have he : p.outputEvent s B=⋃ b, p.returns s b ∩ {ω : Tape | b∈B} := by
    ext ω; simp only [outputEvent,Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff]
    exact ⟨fun ⟨b,hb,h⟩ => ⟨b,h,hb⟩,fun ⟨b,h,hb⟩ => ⟨b,hb,h⟩⟩
  rw [he,measure_iUnion]
  · simp only [tsum_fintype]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : b∈B <;> simp [h]
  · intro a b hab
    apply Set.disjoint_left.mpr
    rintro ω ⟨⟨t,k,ha⟩,_⟩ ⟨⟨u,l,hb⟩,_⟩
    exact hab (congrArg Prod.fst (ha.unique hb).1)
  · intro b
    have hm : MeasurableSet (p.returns s b) := by
      rw [p.returns_eq]
      exact MeasurableSet.iUnion fun a =>
        (BoundedUniform.measurableSet_returns _ _ _).inter (MeasurableSet.const _)
    exact hm.inter (MeasurableSet.const _)

theorem search_none_iff (ω : Tape) (s fuel : ℕ) :
    Progress.search (p.step ω) fuel (p.start s)=none ↔
      Progress.search (BoundedUniform.step p.total ω) fuel (BoundedUniform.start p.total s)=none := by
  constructor
  · intro h
    cases hb : Progress.search (BoundedUniform.step p.total ω) fuel (BoundedUniform.start p.total s) with
    | none => rfl
    | some r =>
      rcases r with ⟨⟨a,t⟩,k⟩
      have hr := Progress.search_complete (Progress.mapReturn_evaluates
        (f := fun a => (p.select a.1,a.2)) (Progress.search_sound hb))
        (ProbabilityProgress.search_cost_le hb)
      change Progress.search (p.step ω) fuel (p.start s)=some _ at hr
      rw [h] at hr
      contradiction
  · intro h
    cases hp : Progress.search (p.step ω) fuel (p.start s) with
    | none => rfl
    | some r =>
      rcases r with ⟨⟨b,t⟩,k⟩
      obtain ⟨a,ha,_⟩ := (p.evaluates_codes _ _ _ _ _).mp (Progress.search_sound hp)
      have hr := Progress.search_complete ha (ProbabilityProgress.search_cost_le hp)
      rw [h] at hr
      contradiction

theorem search_timeout_mass (s fuel : ℕ) :
    law {ω | Progress.search (p.step ω) fuel (p.start s)=none}=
      BoundedUniform.rejection p.total^(fuel/BoundedUniform.width p.total) := by
  have he : {ω | Progress.search (p.step ω) fuel (p.start s)=none}=
      {ω | Progress.search (BoundedUniform.step p.total ω) fuel (BoundedUniform.start p.total s)=none} :=
    Set.ext (fun ω => p.search_none_iff ω s fuel)
  rw [he,BoundedUniform.search_timeout_mass]

end Applications.Probability.PreparedRow

namespace Applications.Probability.Table
open CoinPaths MeasureTheory
open scoped ENNReal BigOperators
variable {α β : Type} [Fintype β] [DecidableEq β] {m : ℕ}

theorem prepare_returns_mass (t : Table α β) (e : Fin m ≃ β) (x : α) (s : ℕ) (b : β) :
    law ((t.prepare e x).returns s b)=mass (t.entry x b) := by
  rw [PreparedRow.returns_mass]
  rw [(t.prepare e x).sum_select (fun y => if y=b then ((t.prepare e x).total : ℝ≥0∞)⁻¹ else 0)]
  change (∑ i : Fin m, ((t.prepare e x).weight i : ℝ≥0∞)*
    (if e i=b then ((t.prepare e x).total : ℝ≥0∞)⁻¹ else 0))=_
  simp only [prepare_weight]
  change (∑ i : Fin m, (RationalWeights.weight (fun i => t.entry x (e i)) i : ℝ≥0∞)*
    (if e i=b then ((t.prepare e x).total : ℝ≥0∞)⁻¹ else 0))=_
  simp only [mul_ite,mul_zero]
  have hw (i : Fin m) :
      (RationalWeights.weight (fun i => t.entry x (e i)) i : ℝ≥0∞)*
        ((t.prepare e x).total : ℝ≥0∞)⁻¹=mass (t.entry x (e i)) := by
    rw [prepare_total]
    exact RationalWeights.weight_mass _ (fun i => t.nonneg x (e i)) i
  simp_rw [hw]
  exact (e.sum_comp (fun y => if y=b then mass (t.entry x y) else 0)).trans (by simp)

variable [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Actual tape execution has exactly the existing table-kernel singleton law. -/
theorem prepare_kernel (t : Table α β) [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] (e : Fin m ≃ β) (x : α) (s : ℕ) (b : β) :
    law ((t.prepare e x).returns s b)=t.kernel x {b} := by
  rw [prepare_returns_mass,Table.kernel_singleton]

/-- Equality with the existing kernel on every event of the finite output space. -/
theorem prepare_kernel_event (t : Table α β) [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] (e : Fin m ≃ β) (x : α) (s : ℕ) (B : Set β) :
    law ((t.prepare e x).outputEvent s B)=t.kernel x B := by
  classical
  rw [PreparedRow.outputEvent_mass,Table.kernel_apply]
  simp only [prepare_returns_mass]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : b∈B <;> simp [h]

end Applications.Probability.Table

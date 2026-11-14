import Applications.Probability.TableProducer
import Applications.Probability.FiniteMHSampler

/-! Joint finite blocks of one producer, observed after an arbitrary finite shift. -/
namespace Applications.Probability.TableProducer
open CoinPaths MeasureTheory
open scoped ENNReal
variable {α : Type}

/-- Observe the ordered block ys after n emissions, hiding only the preceding
outputs. The witness is a delivery by the same producer on the same tape. -/
def blockEvent (p : α → PreparedRow α) (n : ℕ) (x : α) (s : ℕ) (ys : List α) : Set Tape :=
  {ω | ∃ zs, zs.length=n+ys.length ∧ zs.drop n=ys ∧ ω∈prefixEvent p x s zs}

theorem block_zero (p : α → PreparedRow α) (x : α) (s : ℕ) (ys : List α) :
    blockEvent p 0 x s ys=prefixEvent p x s ys := by
  ext ω
  simp [blockEvent]

theorem block_succ (p : α → PreparedRow α) (n : ℕ) (x : α) (s : ℕ)
    (ys : List α) (ω : Tape) :
    ω∈blockEvent p (n+1) x s ys ↔ ∃ a t k,
      Progress.Evaluates ((p x).step ω) ((p x).start s) (a,t) k ∧
        ω∈blockEvent p n a t ys := by
  simp only [blockEvent,Set.mem_ofPred_eq,prefix_eq]
  constructor
  · rintro ⟨zs,hlen,hdrop,h⟩
    cases zs with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons a zs =>
      obtain ⟨t,k,ha,hr⟩ := (RowChain.returns_cons _ _ _ _ _ _ _).mp h
      exact ⟨a,t,k,ha,zs,by simp only [List.length_cons] at hlen; omega,
        hdrop,hr⟩
  · rintro ⟨a,t,k,ha,zs,hlen,hdrop,hr⟩
    refine ⟨a::zs,by simp [hlen,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm],hdrop,?_⟩
    exact (RowChain.returns_cons _ _ _ _ _ _ _).mpr ⟨t,k,ha,hr⟩

theorem block_shift (p : α → PreparedRow α) (n : ℕ) (x : α) (s : ℕ)
    (ys : List α) (ω : Tape) :
    CoinSuffix.suffix s ω∈blockEvent p n x 0 ys ↔ ω∈blockEvent p n x s ys := by
  simp only [blockEvent,Set.mem_ofPred_eq,prefix_eq,RowChain.returns_shift,Nat.add_zero]

theorem measurable_block [Countable α] (p : α → PreparedRow α) (n : ℕ)
    (x : α) (s : ℕ) (ys : List α) : MeasurableSet (blockEvent p n x s ys) := by
  simp only [blockEvent,Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro zs
  simp only [Set.ofPred_and,prefix_eq]
  exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    (RowChain.measurable_returns _ _ _ _ _))

theorem block_succ_mass [Fintype α] (p : α → PreparedRow α) (n : ℕ)
    (x : α) (s : ℕ) (ys : List α) :
    law (blockEvent p (n+1) x s ys)=∑ a,
      law ((p x).returns s a)*law (blockEvent p n a 0 ys) := by
  have he : blockEvent p (n+1) x s ys=⋃ a : α, {ω | ∃ t k,
      Progress.Evaluates ((p x).step ω) ((p x).start s) (a,t) k ∧
        CoinSuffix.suffix t ω∈blockEvent p n a 0 ys} := by
    ext ω
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq,block_succ,block_shift]
  have hm (a : α) : MeasurableSet {ω | ∃ t k,
      Progress.Evaluates ((p x).step ω) ((p x).start s) (a,t) k ∧
        CoinSuffix.suffix t ω∈blockEvent p n a 0 ys} := by
    simp only [Set.ofPred_exists,Set.ofPred_and]
    exact MeasurableSet.iUnion fun t => MeasurableSet.iUnion fun k =>
      (ProbabilityProgress.measurable_evaluates _ (p x).measurableSteps _ _ _).inter
        ((CoinSuffix.measurable_suffix t) (measurable_block p n a 0 ys))
  rw [he,measure_iUnion]
  · simp only [tsum_fintype]
    exact Finset.sum_congr rfl fun a _ => (p x).stopped_mass s a _ (measurable_block p n a 0 ys)
  · intro a b hab
    apply Set.disjoint_left.mpr
    rintro ω ⟨t,k,ha,_⟩ ⟨u,l,hb,_⟩
    exact hab (congrArg Prod.fst (ha.unique hb).1)
  · exact hm

/-- A stationary initialization preserves the entire ordered block distribution
under a finite observation shift, not only each separate output marginal. -/
theorem stationary_blocks [Fintype α] [DecidableEq α] {m : ℕ}
    (t : Table α α) (e : Fin m ≃ α) (π : α → ℝ≥0∞)
    (hπ : ∀ a, ∑ x, π x*mass (t.entry x a)=π a)
    (n : ℕ) (s : ℕ) (ys : List α) :
    ∑ x, π x*law (blockEvent (t.prepare e) n x s ys)=
      ∑ x, π x*mass (RowChain.pathMass t x ys) := by
  induction n generalizing s with
  | zero => simp only [block_zero,prefix_mass]
  | succ n ih =>
    simp_rw [block_succ_mass,t.prepare_returns_mass,Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc,← Finset.sum_mul,hπ]
    exact ih 0

end Applications.Probability.TableProducer

namespace Applications.Probability.FiniteMH
open CoinPaths MeasureTheory
open scoped ENNReal

/-- The target-initialized MH producer has stationary joint finite blocks.
The target is mixed independently of the fair tape through the displayed sum. -/
theorem producer_stationary_blocks {α : Type} [Fintype α] [DecidableEq α]
    [Nonempty α] (m : FiniteMH α) {d : ℕ} (e : Fin d ≃ α) (n s : ℕ) (ys : List α) :
    ∑ x, mass (m.target x)*law (TableProducer.blockEvent (m.transition.prepare e) n x s ys)=
      ∑ x, mass (m.target x)*mass (RowChain.pathMass m.transition x ys) := by
  apply TableProducer.stationary_blocks
  intro a
  simp_rw [← mass_mul _ _ (m.target_nonneg _)]
  rw [← mass_sum _ _ (fun x _ => mul_nonneg (m.target_nonneg x) (m.transition.nonneg x a)),m.stationary]

end Applications.Probability.FiniteMH

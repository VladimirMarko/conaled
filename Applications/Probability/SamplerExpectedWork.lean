import Applications.Probability.SamplerWorkload
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Logic.Equiv.Fin.Basic

/-! Finite-prefix deadlines and nonnegative expected work for actual samplers. -/
namespace Applications.Probability.SamplerExpectedWork
open CoinPaths CoinSuffix MeasureTheory
open scoped ENNReal NNReal
variable {α : Type}

/-- Each of the next n rows finishes within b bits. Subsequent tests use the
actual returned cursor, so this is a joint stopped-execution event. -/
def fast (p : α → PreparedRow α) : ℕ → α → ℕ → Set Tape
  | 0,_,_ => Set.univ
  | n+1,x,b => {ω | ∃ a t k, Progress.Evaluates ((p x).step ω) ((p x).start 0) (a,t) k ∧
      k≤b ∧ suffix t ω∈fast p n a b}

theorem measurable_fast [Countable α] (p : α → PreparedRow α) (n : ℕ) (x : α) (b : ℕ) :
    MeasurableSet (fast p n x b) := by
  induction n generalizing x with
  | zero => exact MeasurableSet.univ
  | succ n ih =>
    simp only [fast,Set.ofPred_exists,Set.ofPred_and]
    exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun t => MeasurableSet.iUnion fun k =>
      (ProbabilityProgress.measurable_evaluates _ (p x).measurableSteps _ _ _).inter
        ((MeasurableSet.const _).inter ((measurable_suffix t) (ih a)))

theorem fast_delivers (p : α → PreparedRow α) (n : ℕ) (x : α) (b s : ℕ) (ω : Tape)
    (h : suffix s ω∈fast p n x b) :
    ∃ ys z k, ys.length=n ∧ k≤n*b ∧
      Progress.Delivers (TableProducer.step p ω) (TableProducer.start p x s) ys z k := by
  induction n generalizing x s with
  | zero => exact ⟨[],_,0,rfl,by simp,.nil _⟩
  | succ n ih =>
    obtain ⟨a,t,k,hrow,hk,hr⟩ := h
    have hcomp : suffix t (suffix s ω)=suffix (s+t) ω := by
      funext i; simp [suffix,Nat.add_assoc]
    rw [hcomp] at hr
    obtain ⟨ys,z,l,hlen,hl,hd⟩ := ih a (s+t) hr
    have he := TableProducer.evaluates_of_row ((p x).evaluates_shift ω s t k a |>.mp hrow)
    refine ⟨a::ys,z,k+l,by simp [hlen],by nlinarith,?_⟩
    exact .cons he hd

/-- Failure of a finite per-row deadline uses a union bound and the full suffix
law at the first returned cursor. Dependent row costs need not be independent. -/
theorem fast_failure_bound [Fintype α] (p : α → PreparedRow α) (b : ℕ) (q : ℝ≥0∞)
    (hb : ∀ x, law {ω | Progress.search ((p x).step ω) b ((p x).start 0)=none}≤q)
    (hnorm : ∀ x, ∑ a, law ((p x).returns 0 a)=1) (n : ℕ) (x : α) :
    law (fast p n x b)ᶜ≤n*q := by
  induction n generalizing x with
  | zero => simp [fast]
  | succ n ih =>
    let E (a : α) : Set Tape := {ω | ∃ t k,
      Progress.Evaluates ((p x).step ω) ((p x).start 0) (a,t) k ∧
        suffix t ω∈(fast p n a b)ᶜ}
    have hsub : (fast p (n+1) x b)ᶜ ⊆
        {ω | Progress.search ((p x).step ω) b ((p x).start 0)=none} ∪ ⋃ a,E a := by
      intro ω h
      cases hs : Progress.search ((p x).step ω) b ((p x).start 0) with
      | none => exact Or.inl hs
      | some r =>
        rcases r with ⟨⟨a,t⟩,k⟩
        right
        refine Set.mem_iUnion.mpr ⟨a,t,k,Progress.search_sound hs,?_⟩
        intro hr
        exact h ⟨a,t,k,Progress.search_sound hs,ProbabilityProgress.search_cost_le hs,hr⟩
    calc
      _ ≤ law ({ω | Progress.search ((p x).step ω) b ((p x).start 0)=none} ∪ ⋃ a,E a) := measure_mono hsub
      _ ≤ law {ω | Progress.search ((p x).step ω) b ((p x).start 0)=none}+law (⋃ a,E a) := measure_union_le _ _
      _ ≤ q+∑' a,law (E a) := add_le_add (hb x) (measure_iUnion_le _)
      _ = q+∑ a,law ((p x).returns 0 a)*law (fast p n a b)ᶜ := by
        simp only [tsum_fintype]
        congr 1
        exact Finset.sum_congr rfl fun a _ => (p x).stopped_mass 0 a _ (measurable_fast p n a b).compl
      _ ≤ q+∑ a,law ((p x).returns 0 a)*(n*q) := by
        gcongr with a
        exact ih a
      _ = (n+1 : ℕ)*q := by rw [← Finset.sum_mul,hnorm]; simp [Nat.cast_add,add_mul,add_comm]

/-- Actual failure to deliver n outputs by a bit deadline, including divergence. -/
def deadline (p : α → PreparedRow α) (n : ℕ) (x : α) (s budget : ℕ) : Set Tape :=
  (ProbabilityProgress.prefixDelivered (TableProducer.step p) (TableProducer.start p x s) n budget)ᶜ

theorem deadline_bound [Fintype α] (p : α → PreparedRow α) (b : ℕ) (q : ℝ≥0∞)
    (hb : ∀ x, law {ω | Progress.search ((p x).step ω) b ((p x).start 0)=none}≤q)
    (hnorm : ∀ x, ∑ a, law ((p x).returns 0 a)=1) (n : ℕ) (x : α) (s : ℕ) :
    law (deadline p n x s (n*b))≤n*q := by
  have hsub : deadline p n x s (n*b) ⊆ suffix s ⁻¹' (fast p n x b)ᶜ := by
    intro ω h hf
    obtain ⟨ys,z,k,hlen,hk,hd⟩ := fast_delivers p n x b s ω hf
    exact h ⟨ys,z,k,hlen,hk,hd⟩
  calc
    _ ≤ law (suffix s ⁻¹' (fast p n x b)ᶜ) := measure_mono hsub
    _ = law (fast p n x b)ᶜ := by
      rw [← Measure.map_apply (measurable_suffix s) (measurable_fast p n x b).compl,suffix_law]
    _ ≤ _ := fast_failure_bound p b q hb hnorm n x

theorem rejection_half (n : ℕ) (hn : 0<n) : BoundedUniform.rejection n ≤ (2⁻¹ : ℝ≥0∞) := by
  have hcap := BoundedUniform.capacity_le_double n hn
  have hle := BoundedUniform.bound_le_capacity n
  have hreal : ((2^BoundedUniform.width n-n : ℕ) : ℝ≥0) / (2^BoundedUniform.width n : ℝ≥0) ≤ (2 : ℝ≥0)⁻¹ := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hd : 2 * (2^BoundedUniform.width n-n) ≤ 2^BoundedUniform.width n := by omega
    have hd' : (2 : ℝ≥0) * (2^BoundedUniform.width n-n : ℕ) ≤ 2^BoundedUniform.width n := by exact_mod_cast hd
    nlinarith
  have hM : (2^BoundedUniform.width n : ℝ≥0) ≠ 0 := by positivity
  have he : BoundedUniform.rejection n = (((2^BoundedUniform.width n-n : ℕ) : ℝ≥0) / (2^BoundedUniform.width n : ℝ≥0) : ℝ≥0) := by
    rw [BoundedUniform.rejection, ENNReal.coe_div hM]
    simp [div_eq_mul_inv, ENNReal.inv_pow]
  rw [he]
  have hc := ENNReal.coe_le_coe.mpr hreal
  simpa only [ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using hc

/-- An explicit finite uniform width, also defined for an empty state type. -/
def maxWidth [Fintype α] (p : α → PreparedRow α) : ℕ :=
  1+Finset.univ.sup (fun x => BoundedUniform.width (p x).total)

theorem width_le_max [Fintype α] (p : α → PreparedRow α) (x : α) :
    BoundedUniform.width (p x).total≤maxWidth p := by
  have := Finset.le_sup (f := fun x => BoundedUniform.width (p x).total) (Finset.mem_univ x)
  unfold maxWidth
  omega

theorem row_deadline [Fintype α] (p : α → PreparedRow α) (x : α) (r : ℕ) :
    law {ω | Progress.search ((p x).step ω) (maxWidth p*r) ((p x).start 0)=none}≤
      (2⁻¹ : ℝ≥0∞)^r := by
  rw [(p x).search_timeout_mass]
  have he : r≤maxWidth p*r/BoundedUniform.width (p x).total := by
    apply (Nat.le_div_iff_mul_le (BoundedUniform.width_pos _)).mpr
    exact Nat.mul_le_mul_left r (width_le_max p x) |>.trans_eq (Nat.mul_comm _ _)
  exact (pow_le_pow_left' (rejection_half _ (p x).positive) _).trans
    (pow_le_pow_right_of_le_one' (by norm_num) he)

theorem rows_deadline [Fintype α] [DecidableEq α]
    (p : α → PreparedRow α) (n : ℕ) (x : α) (s r : ℕ) :
    law (deadline p n x s (n*(maxWidth p*r)))≤
      n*(2⁻¹ : ℝ≥0∞)^r := by
  apply deadline_bound _ _ _ (fun x => row_deadline _ x r)
  exact fun x => (p x).returns_sum 0

theorem table_deadline [Fintype α] [DecidableEq α] {m : ℕ}
    (t : Table α α) (e : Fin m ≃ α) (n : ℕ) (x : α) (s r : ℕ) :
    law (deadline (t.prepare e) n x s (n*(maxWidth (t.prepare e)*r)))≤
      n*(2⁻¹ : ℝ≥0∞)^r :=
  rows_deadline (t.prepare e) n x s r

theorem deadline_antitone (p : α → PreparedRow α) (n : ℕ) (x : α) (s : ℕ)
    {b c : ℕ} (h : b≤c) : deadline p n x s c⊆deadline p n x s b := by
  intro ω hc hb
  obtain ⟨ys,z,k,hlen,hk,hd⟩ := hb
  exact hc ⟨ys,z,k,hlen,hk.trans h,hd⟩

theorem rows_deadline_any [Fintype α] [DecidableEq α]
    (p : α → PreparedRow α) (n : ℕ) (x : α) (s b : ℕ) :
    law (deadline p n x s b)≤
      n*(2⁻¹ : ℝ≥0∞)^(b/(n*maxWidth p)) := by
  have hle : n*(maxWidth p*(b/(n*maxWidth p)))≤b := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_div_le _ _
  exact (measure_mono (deadline_antitone _ _ _ _ hle)).trans (rows_deadline p n x s _)

theorem table_deadline_any [Fintype α] [DecidableEq α] {m : ℕ}
    (t : Table α α) (e : Fin m ≃ α) (n : ℕ) (x : α) (s b : ℕ) :
    law (deadline (t.prepare e) n x s b)≤
      n*(2⁻¹ : ℝ≥0∞)^(b/(n*maxWidth (t.prepare e))) :=
  rows_deadline_any (t.prepare e) n x s b

/-- Actual prefix bit count via deadline indicators: finite counts are recovered
below, while a missing finite delivery has value infinity. -/
noncomputable def bitWork (p : α → PreparedRow α) (n : ℕ) (x : α) (s : ℕ) (ω : Tape) : ℝ≥0∞ :=
  ∑' b : ℕ,(deadline p n x s b).indicator (fun _ => (1 : ℝ≥0∞)) ω

theorem deadline_iff_of_delivers (p : α → PreparedRow α) (x : α) (s : ℕ)
    {ω : Tape} {ys : List α} {z : TableProducer.State α} {k : ℕ}
    (h : Progress.Delivers (TableProducer.step p ω) (TableProducer.start p x s) ys z k) (b : ℕ) :
    ω∈deadline p ys.length x s b ↔ b<k := by
  constructor
  · intro hb
    by_contra hk
    exact hb ⟨ys,z,k,rfl,by omega,h⟩
  · intro hb hd
    obtain ⟨xs,t,l,hlen,hl,hx⟩ := hd
    have hsame : ys=xs := by
      have hc := h.coherent hx
      rw [hlen,List.take_length,List.take_of_length_le (le_of_eq hlen)] at hc
      exact hc
    subst xs
    have := (h.unique hx).2
    omega

theorem bitWork_of_delivers (p : α → PreparedRow α) (x : α) (s : ℕ)
    {ω : Tape} {ys : List α} {z : TableProducer.State α} {k : ℕ}
    (h : Progress.Delivers (TableProducer.step p ω) (TableProducer.start p x s) ys z k) :
    bitWork p ys.length x s ω=k := by
  classical
  unfold bitWork
  have he (b : ℕ) : (deadline p ys.length x s b).indicator (fun _ => (1 : ℝ≥0∞)) ω=
      if b<k then 1 else 0 := by simp [Set.indicator_apply,deadline_iff_of_delivers p x s h]
  simp_rw [he]
  rw [tsum_eq_sum (s := Finset.range k)]
  · simp only [Finset.sum_ite_of_true (fun b hb => Finset.mem_range.mp hb),Finset.sum_const,
      Finset.card_range,nsmul_eq_mul,mul_one]
  · intro b hb
    simp only [Finset.mem_range,not_lt] at hb
    simp [Nat.not_lt.mpr hb]

theorem bitWork_of_divergence (p : α → PreparedRow α) (n : ℕ) (x : α) (s : ℕ) (ω : Tape)
    (h : ¬∃ ys z k, ys.length=n ∧ Progress.Delivers (TableProducer.step p ω)
      (TableProducer.start p x s) ys z k) : bitWork p n x s ω=∞ := by
  have hd (b : ℕ) : ω∈deadline p n x s b := by
    rintro ⟨ys,z,k,hlen,_,he⟩; exact h ⟨ys,z,k,hlen,he⟩
  simp [bitWork,Set.indicator_of_mem,hd]

theorem lintegral_bitWork [Countable α] (p : α → PreparedRow α) (n : ℕ) (x : α) (s : ℕ) :
    (∫⁻ ω,bitWork p n x s ω ∂law)=∑' b,law (deadline p n x s b) := by
  have hm (b : ℕ) : MeasurableSet (deadline p n x s b) :=
    ProbabilityProgress.measurable_prefixTimeout _ (TableProducer.measurableSteps p) _ _ _
  simp only [bitWork]
  rw [lintegral_tsum (fun b => (measurable_const.indicator (hm b)).aemeasurable)]
  congr 1
  funext b
  exact lintegral_indicator_one (hm b)

private theorem tsum_blocks (B : ℕ) (hB : 0<B) (q : ℝ≥0∞) :
    (∑' b : ℕ,q^(b/B))=(B : ℝ≥0∞)*(1-q)⁻¹ := by
  let : NeZero B := ⟨Nat.ne_of_gt hB⟩
  have he := (Nat.divModEquiv B).tsum_eq (fun p : ℕ × Fin B => q^p.1)
  change (∑' b : ℕ,q^(b/B))=_ at he
  rw [he,ENNReal.tsum_prod']
  simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    ENNReal.tsum_mul_left,ENNReal.tsum_geometric]

/-- A conservative quadratic horizon bound. Finiteness follows from geometric
row tails and stopped suffix laws, not merely almost-sure productivity. -/
theorem expected_bits_rows [Fintype α] [DecidableEq α]
    (p : α → PreparedRow α) (n : ℕ) (x : α) (s : ℕ) :
    (∫⁻ ω,bitWork p n x s ω ∂law)≤(2*n*(n*maxWidth p) : ℕ) := by
  rw [lintegral_bitWork]
  by_cases hn : n=0
  · subst n
    have hz (b : ℕ) : deadline p 0 x s b=∅ := by
      ext ω; simp only [Set.mem_empty_iff_false,iff_false]
      intro h; exact h ⟨[],_,0,rfl,Nat.zero_le _,.nil _⟩
    simp [hz]
  calc
    _ ≤ ∑' b : ℕ,(n : ℝ≥0∞)*(2⁻¹ : ℝ≥0∞)^(b/(n*maxWidth p)) :=
      ENNReal.tsum_le_tsum (fun b => rows_deadline_any p n x s b)
    _ = _ := by
      rw [ENNReal.tsum_mul_left,tsum_blocks _ (by unfold maxWidth; positivity)]
      norm_num
      ring

theorem expected_bits_le [Fintype α] [DecidableEq α] {m : ℕ}
    (t : Table α α) (e : Fin m ≃ α) (n : ℕ) (x : α) (s : ℕ) :
    (∫⁻ ω,bitWork (t.prepare e) n x s ω ∂law)≤(2*n*(n*maxWidth (t.prepare e)) : ℕ) :=
  expected_bits_rows (t.prepare e) n x s


open SamplerWorkload SamplerWork

private theorem tick_bit (load : Loader α) (τ : Tariff) (o : Overhead) (ω η : Tape)
    (z : State α) (h : ω z.blockState.1=η z.blockState.1) :
    tick load τ o ω () z=tick load τ o η () z := by
  simp [tick,measuredStep,BoundedUniform.step,h]

/-- Finite workload observations are measurable by splitting on the one bit
inspected at each tick. Cached rows need no measurable function-space structure. -/
theorem measurable_run (load : Loader α) (τ : Tariff) (o : Overhead)
    (commands : List Unit) (z : State α) :
    Measurable (fun ω : Tape =>
      ((Resources.run (tick load τ o ω) commands z).1.emitted.length,
       (Resources.run (tick load τ o ω) commands z).2)) := by
  induction commands generalizing z with
  | nil => simpa only [Resources.run_nil] using (measurable_const : Measurable (fun _ : Tape => (z.emitted.length,(0 : ℕ))))
  | cons u cs ih =>
    cases u
    let a := tick load τ o (fun _ => true) () z
    let b := tick load τ o (fun _ => false) () z
    have he : (fun ω : Tape =>
        ((Resources.run (tick load τ o ω) (()::cs) z).1.emitted.length,
         (Resources.run (tick load τ o ω) (()::cs) z).2))=
        fun ω => if ω z.blockState.1=true then
          ((Resources.run (tick load τ o ω) cs a.1).1.emitted.length,
            a.2+(Resources.run (tick load τ o ω) cs a.1).2)
        else ((Resources.run (tick load τ o ω) cs b.1).1.emitted.length,
            b.2+(Resources.run (tick load τ o ω) cs b.1).2) := by
      funext ω
      cases hb : ω z.blockState.1
      · have ht := tick_bit load τ o ω (fun _ => false) z hb
        simp [Resources.run_cons,ht,b]
      · have ht := tick_bit load τ o ω (fun _ => true) z hb
        simp [Resources.run_cons,ht,a]
    rw [he]
    have hbit : Measurable (fun ω : Tape => ω z.blockState.1) := measurable_pi_apply _
    exact Measurable.ite (hbit (measurableSet_singleton true))
      ((ih a.1).fst.prodMk (measurable_const.add (ih a.1).snd))
      ((ih b.1).fst.prodMk (measurable_const.add (ih b.1).snd))

theorem measurable_workload (load : Loader α) (τ : Tariff) (o : Overhead)
    (x : α) (s k : ℕ) (chain : Bool) :
    Measurable (fun ω : Tape => (workload load τ o ω x s k chain).2) := by
  have hm := measurable_run load τ o (List.replicate k ()) (beginWork load τ x s).1
  exact measurable_const.add (hm.snd.add ((hm.fst.mul measurable_const).add measurable_const))

def deliveryAt (p : α → PreparedRow α) (n : ℕ) (x : α) (s k : ℕ) : Set Tape :=
  {ω | ∃ ys z, ys.length=n ∧ Progress.Delivers (TableProducer.step p ω)
    (TableProducer.start p x s) ys z k}

theorem measurable_deliveryAt [Countable α] (p : α → PreparedRow α) (n : ℕ)
    (x : α) (s k : ℕ) : MeasurableSet (deliveryAt p n x s k) := by
  simp only [deliveryAt,Set.ofPred_exists,Set.ofPred_and]
  exact MeasurableSet.iUnion fun ys => MeasurableSet.iUnion fun z =>
    (MeasurableSet.const _).inter (ProbabilityProgress.measurable_delivers _
      (TableProducer.measurableSteps p) _ _ _ _)

theorem deliveryAt_unique (p : α → PreparedRow α) (n : ℕ) (x : α) (s : ℕ)
    {ω : Tape} {i j : ℕ} (hi : ω∈deliveryAt p n x s i) (hj : ω∈deliveryAt p n x s j) : i=j := by
  obtain ⟨ys,z,hlen,h⟩ := hi
  obtain ⟨xs,t,xlen,hx⟩ := hj
  have he : ys=xs := by
    have hc := h.coherent hx
    rw [show xs.length=ys.length from xlen.trans hlen.symm,List.take_length,
      List.take_of_length_le (le_of_eq (xlen.trans hlen.symm))] at hc
    exact hc
  subst xs
  exact (h.unique hx).2

/-- Actual charged cost at the unique finite prefix delivery, including setup.
Absence of delivery is infinity even when all declared tariffs are zero. -/
noncomputable def chargedWork (load : Loader α) (p : α → PreparedRow α) (τ : Tariff)
    (o : Overhead) (setup n : ℕ) (x : α) (s : ℕ) (chain : Bool) (ω : Tape) : ℝ≥0∞ :=
  (∑' k : ℕ,(deliveryAt p n x s k).indicator
    (fun ω => ((setup+(workload load τ o ω x s k chain).2 : ℕ) : ℝ≥0∞)) ω)+
    (⋃ k,deliveryAt p n x s k)ᶜ.indicator (fun _ => (∞ : ℝ≥0∞)) ω

theorem measurable_chargedWork [Countable α] (load : Loader α) (p : α → PreparedRow α)
    (τ : Tariff) (o : Overhead) (setup n : ℕ) (x : α) (s : ℕ) (chain : Bool) :
    Measurable (chargedWork load p τ o setup n x s chain) := by
  apply Measurable.add
  · apply Measurable.tsum
    intro k
    exact ((measurable_of_countable (fun i : ℕ => (i : ℝ≥0∞))).comp
      (measurable_const.add (measurable_workload load τ o x s k chain))).indicator
      (measurable_deliveryAt p n x s k)
  · exact measurable_const.indicator (MeasurableSet.iUnion (measurable_deliveryAt p n x s)).compl

theorem chargedWork_of_delivers (load : Loader α) (p : α → PreparedRow α) (τ : Tariff)
    (o : Overhead) (setup : ℕ) (x : α) (s : ℕ) (chain : Bool)
    {ω : Tape} {ys : List α} {z : TableProducer.State α} {k : ℕ}
    (h : Progress.Delivers (TableProducer.step p ω) (TableProducer.start p x s) ys z k) :
    chargedWork load p τ o setup ys.length x s chain ω=setup+(workload load τ o ω x s k chain).2 := by
  classical
  have hk : ω∈deliveryAt p ys.length x s k := ⟨ys,z,rfl,h⟩
  have hm : ω∈⋃ i,deliveryAt p ys.length x s i := Set.mem_iUnion.mpr ⟨k,hk⟩
  unfold chargedWork
  rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hm),add_zero,tsum_eq_single k]
  · simp [hk]
  · intro i hi
    apply Set.indicator_of_notMem
    intro hh
    exact hi (deliveryAt_unique p ys.length x s hh hk)

theorem chargedWork_of_divergence (load : Loader α) (p : α → PreparedRow α) (τ : Tariff)
    (o : Overhead) (setup n : ℕ) (x : α) (s : ℕ) (chain : Bool) (ω : Tape)
    (h : ¬∃ ys z k, ys.length=n ∧ Progress.Delivers (TableProducer.step p ω)
      (TableProducer.start p x s) ys z k) : chargedWork load p τ o setup n x s chain ω=∞ := by
  have hm : ω∈(⋃ k,deliveryAt p n x s k)ᶜ := by
    intro he
    obtain ⟨k,ys,z,hlen,hd⟩ := Set.mem_iUnion.mp he
    exact h ⟨ys,z,k,hlen,hd⟩
  unfold chargedWork
  rw [Set.indicator_of_mem hm]
  exact add_top _


def maxPerBit [Fintype α] (p : α → PreparedRow α) (τ : Tariff) : ℕ :=
  Finset.univ.sup (fun x => perBitBound (p x) τ)

def maxLoad [Fintype α] (load : Loader α) : ℕ := Finset.univ.sup (fun x => (load x).2)

def drawCap [Fintype α] (load : Loader α) (p : α → PreparedRow α) (τ : Tariff) (o : Overhead) : ℕ :=
  maxPerBit p τ+maxLoad load+initialization τ+o.emit

def baseCost (load : Loader α) (τ : Tariff) (o : Overhead) (setup n : ℕ) (x : α) (chain : Bool) : ℕ :=
  setup+(load x).2+initialization τ+n*o.finish+(if chain then o.admin else 0)

private theorem delivered_cost_bound [Fintype α] (load : Loader α) (p : α → PreparedRow α)
    (he : ∀ x,(load x).1=p x) (τ : Tariff) (o : Overhead) (setup : ℕ) (x : α) (s : ℕ)
    {ω : Tape} {ys : List α} {z : TableProducer.State α} {k : ℕ}
    (h : Progress.Delivers (TableProducer.step p ω) (TableProducer.start p x s) ys z k)
    (chain : Bool) : setup+(workload load τ o ω x s k chain).2≤
      baseCost load τ o setup ys.length x chain+k*drawCap load p τ o := by
  have hb := workload_bound load p he τ o ω (maxPerBit p τ) (maxLoad load)
    (fun x => Finset.le_sup (f := fun x => perBitBound (p x) τ) (Finset.mem_univ x))
    (fun x => Finset.le_sup (f := fun x => (load x).2) (Finset.mem_univ x)) x s h chain
  unfold baseCost drawCap
  omega

/-- Zero tariffs still do not make a divergent execution a completed workload.
The affine comparison is almost everywhere, using proved finite delivery. -/
theorem chargedWork_rows_ae_bound [Fintype α] [DecidableEq α]
    (p : α → PreparedRow α) (load : Loader α)
    (he : ∀ x,(load x).1=p x) (τ : Tariff) (o : Overhead)
    (setup n : ℕ) (x : α) (s : ℕ) (chain : Bool) :
    ∀ᵐ ω ∂law, chargedWork load p τ o setup n x s chain ω≤
      baseCost load τ o setup n x chain+bitWork p n x s ω*drawCap load p τ o := by
  filter_upwards [TableProducer.almostSureProductive_rows p x s n] with ω h
  obtain ⟨ys,z,k,hlen,hd⟩ := h
  have hc := chargedWork_of_delivers load p τ o setup x s chain hd
  have hb := bitWork_of_delivers p x s hd
  rw [hlen] at hc hb
  rw [hc,hb]
  have hbound := delivered_cost_bound load p he τ o setup x s hd chain
  rw [hlen] at hbound
  exact_mod_cast hbound

theorem chargedWork_ae_bound [Fintype α] [DecidableEq α] {m : ℕ}
    (t : Table α α) (e : Fin m ≃ α) (load : Loader α)
    (he : ∀ x,(load x).1=t.prepare e x) (τ : Tariff) (o : Overhead)
    (setup n : ℕ) (x : α) (s : ℕ) (chain : Bool) :
    ∀ᵐ ω ∂law, chargedWork load (t.prepare e) τ o setup n x s chain ω≤
      baseCost load τ o setup n x chain+bitWork (t.prepare e) n x s ω*drawCap load (t.prepare e) τ o :=
  chargedWork_rows_ae_bound (t.prepare e) load he τ o setup n x s chain

/-- Unconditional nonnegative expected charged work is finite. The estimate is
conservative: every bit gets the largest row envelope including next-row setup. -/
theorem expected_rows_charged_le [Fintype α] [DecidableEq α]
    (p : α → PreparedRow α) (load : Loader α)
    (he : ∀ x,(load x).1=p x) (τ : Tariff) (o : Overhead)
    (setup n : ℕ) (x : α) (s : ℕ) (chain : Bool) :
    (∫⁻ ω,chargedWork load p τ o setup n x s chain ω ∂law)≤
      (baseCost load τ o setup n x chain+
        2*n*(n*maxWidth p)*drawCap load p τ o : ℕ) := by
  calc
    _ ≤ ∫⁻ ω,(baseCost load τ o setup n x chain : ℝ≥0∞)+
        bitWork p n x s ω*(drawCap load p τ o : ℝ≥0∞) ∂law :=
      lintegral_mono_ae (chargedWork_rows_ae_bound p load he τ o setup n x s chain)
    _ = (baseCost load τ o setup n x chain : ℝ≥0∞)+
        (∫⁻ ω,bitWork p n x s ω ∂law)*drawCap load p τ o := by
      rw [lintegral_add_left measurable_const,lintegral_mul_const' _ _ (by simp)]
      simp
    _ ≤ _ := by
      have hb := expected_bits_rows p n x s
      simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hb ⊢
      gcongr

theorem expected_charged_le [Fintype α] [DecidableEq α] {m : ℕ}
    (t : Table α α) (e : Fin m ≃ α) (load : Loader α)
    (he : ∀ x,(load x).1=t.prepare e x) (τ : Tariff) (o : Overhead)
    (setup n : ℕ) (x : α) (s : ℕ) (chain : Bool) :
    (∫⁻ ω,chargedWork load (t.prepare e) τ o setup n x s chain ω ∂law)≤
      (baseCost load τ o setup n x chain+
        2*n*(n*maxWidth (t.prepare e))*drawCap load (t.prepare e) τ o : ℕ) :=
  expected_rows_charged_le (t.prepare e) load he τ o setup n x s chain

theorem expected_rows_charged_finite [Fintype α] [DecidableEq α]
    (p : α → PreparedRow α) (load : Loader α)
    (he : ∀ x,(load x).1=p x) (τ : Tariff) (o : Overhead)
    (setup n : ℕ) (x : α) (s : ℕ) (chain : Bool) :
    (∫⁻ ω,chargedWork load p τ o setup n x s chain ω ∂law)<∞ :=
  (expected_rows_charged_le p load he τ o setup n x s chain).trans_lt (ENNReal.natCast_lt_top _)

theorem expected_charged_finite [Fintype α] [DecidableEq α] {m : ℕ}
    (t : Table α α) (e : Fin m ≃ α) (load : Loader α)
    (he : ∀ x,(load x).1=t.prepare e x) (τ : Tariff) (o : Overhead)
    (setup n : ℕ) (x : α) (s : ℕ) (chain : Bool) :
    (∫⁻ ω,chargedWork load (t.prepare e) τ o setup n x s chain ω ∂law)<∞ :=
  expected_rows_charged_finite (t.prepare e) load he τ o setup n x s chain

/-- Whole-workload deadline risk. Setup, lookup, preparation, selection and
final handling are priced separately; no product of marginal tails is used. -/
theorem rows_charged_deadline [Fintype α] [DecidableEq α]
    (p : α → PreparedRow α) (load : Loader α)
    (he : ∀ x,(load x).1=p x) (τ : Tariff) (o : Overhead)
    (setup n : ℕ) (x : α) (s r : ℕ) (chain : Bool) :
    law {ω | ¬chargedWork load p τ o setup n x s chain ω≤
      (baseCost load τ o setup n x chain+n*(maxWidth p*r)*
        drawCap load p τ o : ℕ)}≤n*(2⁻¹ : ℝ≥0∞)^r := by
  apply le_trans (measure_mono ?_) (rows_deadline p n x s r)
  intro ω h hd
  obtain ⟨ys,z,k,hlen,hk,hy⟩ := hd
  have hc := chargedWork_of_delivers load p τ o setup x s chain hy
  rw [hlen] at hc
  simp only [Set.mem_ofPred_eq] at h
  rw [hc] at h
  have hb := delivered_cost_bound load p he τ o setup x s hy chain
  rw [hlen] at hb
  apply h
  exact_mod_cast hb.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _)

theorem charged_deadline [Fintype α] [DecidableEq α] {m : ℕ}
    (t : Table α α) (e : Fin m ≃ α) (load : Loader α)
    (he : ∀ x,(load x).1=t.prepare e x) (τ : Tariff) (o : Overhead)
    (setup n : ℕ) (x : α) (s r : ℕ) (chain : Bool) :
    law {ω | ¬chargedWork load (t.prepare e) τ o setup n x s chain ω≤
      (baseCost load τ o setup n x chain+n*(maxWidth (t.prepare e)*r)*
        drawCap load (t.prepare e) τ o : ℕ)}≤n*(2⁻¹ : ℝ≥0∞)^r :=
  rows_charged_deadline (t.prepare e) load he τ o setup n x s r chain

end Applications.Probability.SamplerExpectedWork

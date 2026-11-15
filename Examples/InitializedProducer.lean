import Applications.Probability.InitializedProducerWork

/-! Non-dyadic initialization, retained rejection blocks and cursor-reuse controls. -/
namespace Examples.InitializedProducer
open Applications Applications.Probability MeasureTheory
open Applications.Probability.InitializedProducer
open scoped ENNReal

private def stateDecidableEq : DecidableEq (State Bool) := fun a b =>
  match a,b with
  | .inl x,.inl y => if h : x=y then isTrue (congrArg Sum.inl h)
      else isFalse (fun e => h (Sum.inl.inj e))
  | .inr x,.inr y => if h : x=y then isTrue (congrArg Sum.inr h)
      else isFalse (fun e => h (Sum.inr.inj e))
  | .inl _,.inr _ => isFalse (by intro h; cases h)
  | .inr _,.inl _ => isFalse (by intro h; cases h)

local instance : DecidableEq (State Bool) := stateDecidableEq

def initial : Table Unit Bool where
  entry _ b := if b then 2/3 else 1/3
  nonneg _ b := by cases b <;> norm_num
  sum_row _ := by norm_num [Fintype.sum_bool]

def transition : Table Bool Bool where
  entry _ b := initial.entry () b
  nonneg _ := initial.nonneg ()
  sum_row _ := initial.sum_row ()

abbrev row := initial.prepare finTwoEquiv ()
abbrev rows := transition.prepare finTwoEquiv

example : row.total=9 := by decide +kernel
example (b : Bool) : rows b=row := rfl

/-- 1111 is rejected; 0000 initializes false; 0110 then transitions to true. -/
def tape : CoinPaths.Tape := fun i => decide (i<4 ∨ i=9 ∨ i=10)

example : step row rows tape (start row 0)=.inr (.inl (1,3,1)) := by decide +kernel
example : Progress.search (step row rows tape) 4 (start row 0)=none := by decide +kernel
example : step row rows tape (.inl (4,4,0))=.inr (.inl (5,3,0)) := by decide +kernel
example : Progress.search (step row rows tape) 3 (.inl (5,3,0))=
    some ((false,.inr (TableProducer.start rows false 8)),3) := by
  decide +kernel

/-- The delivery includes initialization and retains its exact eight-bit cursor. -/
theorem retained_delivery : Progress.Delivers (step row rows tape) (start row 0)
    [false,true] (.inr (TableProducer.start rows true 12)) 12 := by
  have h₁ : Progress.Evaluates (step row rows tape) (start row 0)
      (false,.inr (TableProducer.start rows false 8)) 8 :=
    Progress.search_sound (fuel := 8) (by decide +kernel)
  have h₂ : Progress.Evaluates (step row rows tape) (.inr (TableProducer.start rows false 8))
      (true,.inr (TableProducer.start rows true 12)) 4 :=
    Progress.search_sound (fuel := 4) (by decide +kernel)
  exact .cons h₁ (.cons h₂ (.nil _))

theorem joint_false_true : CoinPaths.law (jointEvent row rows 0 false [true])=
    (2/9 : ℝ≥0∞) := by
  rw [rational_joint]
  simp only [RowChain.pathMass,mul_one]
  rw [← mass_mul _ _ (initial.nonneg () false)]
  norm_num [initial,transition,mass,ENNReal.ofReal_div_of_pos]


/-- Restarting the identical continuation row at the consumed cursor makes
this off-diagonal joint observation impossible, despite the correct marginals. -/
theorem reused_false_true : CoinPaths.law {ω | ∃ u v k,
    Progress.Evaluates (row.reusedPairStep 0 ω) (.inl (row.start 0))
      ((false,u),(true,v)) k}=0 := row.reused_off_diagonal 0 false true (by decide)

theorem stationary (n s : ℕ) :
    CoinPaths.law (blockEvent row rows n s [false,true])=(2/9 : ℝ≥0∞) := by
  have hs : ∑ x, mass (initial.entry () x)=1 := by
    rw [← mass_sum _ _ (fun x _ => initial.nonneg () x),initial.sum_row,mass_one]
  rw [stationary_blocks initial transition finTwoEquiv (by
    intro a
    change (∑ x, mass (initial.entry () x) * mass (initial.entry () a)) = _
    rw [← Finset.sum_mul,hs,one_mul])]
  simp only [RowChain.pathMass,transition]
  rw [← Finset.sum_mul,hs,one_mul,mul_one]
  norm_num [initial,mass,ENNReal.ofReal_div_of_pos]


example : ProbabilityProgress.AlmostSureProductive CoinPaths.law (step row rows)
    (fun _ => start row 0) := almostSureProductive row transition finTwoEquiv 0


/-- The all-true tape rejects every four-bit code, so initialization emits
nothing. This exceptional execution is preserved beside the almost-sure law. -/
theorem exceptional_initial : ¬Progress.Terminates (row.step (fun _ => true)) (row.start 0) := by
  rintro ⟨⟨b,t⟩,k,h⟩
  obtain ⟨r,a,ha,_,_,_⟩ := (row.evaluates_iff _ _ _ _ _).mp h
  have bad (N : ℕ) (hN : N=9) (r s : ℕ) (a : Fin N) :
      ¬BoundedUniform.Accept N (fun _ => true) s r a := by
    subst N
    induction r generalizing s with
    | zero => change ¬15=a.val; omega
    | succ r ih => exact fun h => ih _ h.2
  exact bad _ (by decide +kernel) _ _ a ha

example : ¬Progress.Productive (step row rows (fun _ => true)) (start row 0) :=
  no_first_of_initial_divergence row rows 0 _ exceptional_initial

/-- The existing asymmetric MH target is drawn before the transition chain.
The ordered pair has mass 1/4 at every finite observation shift. -/
example (n s : ℕ) : CoinPaths.law
    (blockEvent ((targetInitial FiniteMHExamples.asymmetric).prepare finTwoEquiv ())
      (FiniteMHExamples.asymmetric.transition.prepare finTwoEquiv) n s [false,true])=
      (1/4 : ℝ≥0∞) := by
  rw [mh_stationary_blocks]
  norm_num [RowChain.pathMass,FiniteMH.transition,FiniteMH.accepted,FiniteMH.acceptance,
    FiniteMH.rejection,FiniteMH.target,FiniteMH.normalizer,FiniteMHExamples.asymmetric,
    Fintype.sum_bool,mass,ENNReal.ofReal_div_of_pos]
  rw [div_eq_mul_inv,mul_right_comm,ENNReal.mul_inv_cancel (by norm_num : (3 : ℝ≥0∞)≠0) (by simp),one_mul]

abbrev tariff : SamplerWork.Tariff := ⟨1,1,1,1,1,1,1,1⟩
def handling : SamplerWorkload.Overhead := ⟨1,1,1⟩
abbrev firstLoad := SamplerWork.prepareMetered initial finTwoEquiv () tariff
abbrev laterLoad := SamplerWorkload.prepareLoader transition finTwoEquiv tariff
abbrev phaseLoad := InitializedProducerWork.loader firstLoad laterLoad

/-- Actual preparation is charged for the initial row as for every continuation. -/
example : firstLoad.2=22 ∧ (laterLoad false).2=22 := by decide +kernel

example : (SamplerWorkload.workload phaseLoad tariff handling tape none 0 12 false).1=
    ([some false,some true],(some true,(12,4,0))) := by
  have hs : (rows true).start 12=(12,4,0) := by decide +kernel
  simpa only [List.map_cons,List.map_nil,InitializedProducerWork.encode,TableProducer.start,hs] using
    InitializedProducerWork.workload_delivery row rows firstLoad laterLoad
    (SamplerWork.prepareMetered_value _ _ _ _) (SamplerWorkload.prepareLoader_value _ _ _)
    tariff handling tape 0 retained_delivery

/-- Includes the initialization draw, so zero requested transitions still has
one sampled output and its nonzero setup/bit/handling cost. -/
example (n s : ℕ) : (∫⁻ ω,InitializedProducerWork.charged row rows firstLoad laterLoad
    tariff handling 0 n s ω ∂CoinPaths.law)<∞ :=
  InitializedProducerWork.expected_finite row rows firstLoad laterLoad
    (SamplerWork.prepareMetered_value _ _ _ _) (SamplerWorkload.prepareLoader_value _ _ _)
    tariff handling 0 n s

example (n s retry : ℕ) : CoinPaths.law {ω |
    ¬InitializedProducerWork.charged row rows firstLoad laterLoad tariff handling 0 n s ω≤
      (SamplerExpectedWork.baseCost phaseLoad tariff handling 0 (n+1) none false+
       (n+1)*(SamplerExpectedWork.maxWidth (InitializedProducerWork.rows row rows)*retry)*
        SamplerExpectedWork.drawCap phaseLoad (InitializedProducerWork.rows row rows) tariff handling : ℕ)}≤
    (n+1)*(2⁻¹ : ℝ≥0∞)^retry :=
  InitializedProducerWork.budget_risk row rows firstLoad laterLoad
    (SamplerWork.prepareMetered_value _ _ _ _) (SamplerWorkload.prepareLoader_value _ _ _)
    tariff handling 0 n s retry

/-- Twelve bit steps include a rejected initial block, two completed draws,
three actual row preparations, and chronological handling of both outputs. -/
theorem measured_cost : (SamplerWorkload.workload phaseLoad tariff handling tape none 0 12 false).2=161 := by
  decide +kernel

abbrev initialMeasured := (SamplerWorkload.beginWork phaseLoad tariff none 0).1

example : (SamplerWorkload.beginWork phaseLoad tariff none 0).2=24 ∧
    (SamplerWorkload.tick phaseLoad tariff handling tape () initialMeasured).1.blockState=(1,3,1) ∧
    (SamplerWorkload.tick phaseLoad tariff handling tape () initialMeasured).2=6 := by
  decide +kernel

example : Resources.run (SamplerWorkload.tick phaseLoad tariff handling tape)
    (List.replicate 1 ()++List.replicate 11 ()) initialMeasured=
    Resources.bind (Resources.run (SamplerWorkload.tick phaseLoad tariff handling tape)
      (List.replicate 1 ()) initialMeasured)
      (Resources.run (SamplerWorkload.tick phaseLoad tariff handling tape) (List.replicate 11 ())) :=
  InitializedProducerWork.resume _ _ _ _ _ _ _ _

example : InitializedProducerWork.charged row rows firstLoad laterLoad
    tariff handling 0 1 0 tape=161 := by
  simpa only [List.length_cons,List.length_nil,Nat.zero_add,measured_cost,zero_add,
    Nat.cast_ofNat,Nat.cast_zero] using InitializedProducerWork.charged_delivery row rows firstLoad laterLoad
      tariff handling 0 0 retained_delivery

example : InitializedProducerWork.charged row rows (row,0) (SamplerWorkload.freeLoader rows)
    ⟨0,0,0,0,0,0,0,0⟩ ⟨0,0,0⟩ 0 0 0 (fun _ => true)=∞ :=
  InitializedProducerWork.charged_initial_divergence row rows (row,0) (SamplerWorkload.freeLoader rows)
    _ _ 0 0 0 _ exceptional_initial

end Examples.InitializedProducer

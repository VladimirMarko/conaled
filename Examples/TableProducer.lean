import Applications.Probability.TableProducerStationarity

/-! Resumption, self-transitions, stationary blocks, and exceptional tapes. -/
namespace Examples.TableProducer
open Applications.Probability MeasureTheory
open Applications.Probability.TableProducer
open scoped ENNReal

abbrev model := FiniteMHExamples.asymmetric
abbrev rows := model.transition.compile finTwoEquiv finTwoEquiv

def partialTape : CoinPaths.Tape := fun i => decide (i=2)

/-- One bit leaves a partial block in the same semantic state. -/
example : step rows partialTape (start rows true 2)=.inr (true,(3,3,1)) := by
  decide +kernel

/-- Resume that exact partial state. The block 1000 accepts code 8, a self-transition. -/
example : Progress.search (step rows partialTape) 3 (true,(3,3,1))=
    some ((true,start rows true 6),3) := by decide +kernel

/-- A rejected 1111 block consumes four bits; the following 0000 emits false. -/
def retryTape : CoinPaths.Tape := fun i => decide (i<4)
example : Progress.search (step rows retryTape) 4 (start rows true 0)=none := by decide +kernel
example : Progress.search (step rows retryTape) 8 (start rows true 0)=
    some ((false,start rows false 8),8) := by decide +kernel

/-- No terminal administrative step separates emissions: five bits give two outputs. -/
example : Progress.Delivers (step rows (fun _ => false)) (start rows true 0)
    [false,true] (start rows true 5) 5 := by
  have h₁ : Progress.Evaluates (step rows (fun _ => false)) (start rows true 0)
      (false,start rows false 4) 4 := Progress.search_sound (fuel := 4) (by decide +kernel)
  have h₂ : Progress.Evaluates (step rows (fun _ => false)) (start rows false 4)
      (true,start rows true 5) 1 := Progress.search_sound (fuel := 1) (by decide +kernel)
  exact .cons h₁ (.cons h₂ (.nil _))

/-- Self-proposals can be accepted: unchanged output does not identify rejection. -/
example : model.acceptance true true=1 ∧ model.proposal.entry true true=1/2 ∧
    model.rejection true=1/6 := by
  constructor
  · norm_num [FiniteMH.acceptance,FiniteMHExamples.asymmetric]
  constructor
  · norm_num [FiniteMHExamples.asymmetric]
  · exact FiniteMHExamples.asymmetric_rejection

/-- A self-transition is an emitted output, not another sampler retry. -/
example : Progress.Delivers (step rows (fun i => decide (2 ≤ i))) (start rows true 0)
    [true] (start rows true 4) 4 := by
  have h : Progress.Evaluates (step rows (fun i => decide (2 ≤ i))) (start rows true 0)
      (true,start rows true 4) 4 := Progress.search_sound (fuel := 4) (by decide +kernel)
  exact .cons h (.nil _)

example : ProbabilityProgress.AlmostSureProductive CoinPaths.law (step rows)
    (fun _ => start rows true 0) := by
  have he : rows=model.transition.prepare finTwoEquiv := by
    funext x; exact Table.compile_eq _ _ _ _
  rw [he]
  exact almostSureProductive _ _ _ _

example : CoinPaths.law (prefixEvent (model.transition.prepare finTwoEquiv) true 0 [false,true])=
    (1/3 : ℝ≥0∞) := by
  rw [prefix_mass]
  norm_num [RowChain.pathMass,FiniteMH.transition,FiniteMH.accepted,FiniteMH.acceptance,
    FiniteMH.rejection,FiniteMHExamples.asymmetric,Fintype.sum_bool,mass,ENNReal.ofReal_div_of_pos]

example : CoinPaths.law (endpointEvent (model.transition.prepare finTwoEquiv) 2 true 0 true)=
    (7/9 : ℝ≥0∞) := by
  rw [endpoint_mass]
  norm_num [Table.steps,Table.comp,Table.deterministic,FiniteMH.transition,FiniteMH.accepted,
    FiniteMH.acceptance,FiniteMH.rejection,FiniteMHExamples.asymmetric,Fintype.sum_bool,
    mass,ENNReal.ofReal_div_of_pos]

example : ∀ᵐ ω ∂CoinPaths.law, ∃ prefixes : ℕ → List Bool,
    (∀ n, (prefixes n).length=n ∧ ∃ z k,
      Progress.Delivers (step (model.transition.prepare finTwoEquiv) ω)
        (start (model.transition.prepare finTwoEquiv) true 0) (prefixes n) z k) ∧
    ∀ i j, (prefixes i).take j=(prefixes j).take i :=
  ae_coherent_prefixes _ _ _ _

/-- Under target initialization the pair (false,true) has mass 1/4 after any
number of emitted transitions. This checks a joint block, not only marginals. -/
example (n s : ℕ) :
    ∑ x, mass (model.target x)*CoinPaths.law
      (blockEvent (model.transition.prepare finTwoEquiv) n x s [false,true])=(1/4 : ℝ≥0∞) := by
  rw [FiniteMH.producer_stationary_blocks]
  norm_num [RowChain.pathMass,FiniteMH.transition,FiniteMH.accepted,FiniteMH.acceptance,
    FiniteMH.rejection,FiniteMH.target,FiniteMH.normalizer,FiniteMHExamples.asymmetric,
    Fintype.sum_bool,mass,ENNReal.ofReal_div_of_pos]
  rw [div_eq_mul_inv,mul_right_comm,ENNReal.mul_inv_cancel] <;> norm_num

/-- A deterministic semantic row still uses positive-width rejection blocks. -/
def identity : Table Unit Unit := Table.deterministic id
abbrev singletonRows := identity.prepare (Equiv.ofUnique (Fin 1) Unit)

example : ProbabilityProgress.AlmostSureProductive CoinPaths.law (step singletonRows)
    (fun _ => start singletonRows () 0) := almostSureProductive _ _ _ _

example (ω : CoinPaths.Tape) : ¬Progress.Productive (changes singletonRows ω)
    (start singletonRows () 0) := changes_not_productive _ _ _

/-- The all-true tape rejects every one-bit block, so even the first output
never arrives. This exceptional tape does not contradict almost-sure productivity. -/
theorem exceptional_not_productive :
    ¬Progress.Productive (step singletonRows (fun _ => true)) (start singletonRows () 0) := by
  intro hp
  obtain ⟨ys,z,k,hlen,h⟩ := hp 1
  cases h with
  | nil => simp at hlen
  | cons first rest =>
    obtain ⟨t,hr,_⟩ := row_of_evaluates first
    obtain ⟨r,a,ha,_,_,_⟩ := (PreparedRow.evaluates_iff _ _ _ _ _ _).mp hr
    have ht : (singletonRows ()).total=1 := by decide +kernel
    have bad (N : ℕ) (hN : N=1) (r s : ℕ) (a : Fin N) : ¬BoundedUniform.Accept N (fun _ => true) s r a := by
      subst N
      induction r generalizing s with
      | zero =>
        change ¬1=a.val
        omega
      | succ r ih =>
        intro h
        exact ih _ h.2
    exact bad _ ht _ _ a ha

end Examples.TableProducer

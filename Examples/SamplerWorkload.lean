import Applications.Probability.SamplerExpectedWork
import Applications.Probability.HeavyTail
import Examples.TableProducer
import Examples.TableSampler

/-! Checked execution, setup amortization, and unconditional work bounds. -/
namespace Examples.SamplerWorkload
open Applications Applications.Probability MeasureTheory
open SamplerWorkload SamplerExpectedWork
open scoped ENNReal

abbrev model := TableProducer.model
abbrev τ := TableSampler.unitTariff
def overhead : Overhead := ⟨1,1,1⟩
abbrev prepared := prepareLoader model.transition finTwoEquiv τ
abbrev compiled := compileLoader model.transition finTwoEquiv τ
abbrev rows := model.transition.prepare finTwoEquiv
abbrev zeros : CoinPaths.Tape := fun _ => false

/-- The prepared table has a real setup price; each later lookup costs one. -/
example : compiled.2=46 ∧ (compiled.1 true).2=1 ∧ (prepared true).2=22 := by decide +kernel

/-- Empty observations still initialize the current row. -/
example : (workload prepared τ overhead zeros true 0 0 false).2=24 ∧
    compiled.2+(workload compiled.1 τ overhead zeros true 0 0 false).2=49 := by decide +kernel

/-- Setup dominates a short run; two dependent transitions amortize it. -/
example : (workload prepared τ overhead zeros true 0 4 false).2=80 ∧
    compiled.2+(workload compiled.1 τ overhead zeros true 0 4 false).2=84 := by decide +kernel
example : (workload prepared τ overhead zeros true 0 5 false).2=117 ∧
    compiled.2+(workload compiled.1 τ overhead zeros true 0 5 false).2=100 := by decide +kernel

theorem two_deliveries : Progress.Delivers (Applications.Probability.TableProducer.step rows zeros)
    (Applications.Probability.TableProducer.start rows true 0) [false,true]
    (Applications.Probability.TableProducer.start rows true 5) 5 := by
  have h₁ : Progress.Evaluates (Applications.Probability.TableProducer.step rows zeros)
      (Applications.Probability.TableProducer.start rows true 0)
      (false,Applications.Probability.TableProducer.start rows false 4) 4 :=
    Progress.search_sound (fuel:=4) (by decide +kernel)
  have h₂ : Progress.Evaluates (Applications.Probability.TableProducer.step rows zeros)
      (Applications.Probability.TableProducer.start rows false 4)
      (true,Applications.Probability.TableProducer.start rows true 5) 1 :=
    Progress.search_sound (fuel:=1) (by decide +kernel)
  exact .cons h₁ (.cons h₂ (.nil _))

/-- The public erasure theorem preserves the dependent path and returned cursor. -/
example : (workload prepared τ overhead zeros true 0 5 false).1=
    ([false,true],Applications.Probability.TableProducer.start rows true 5) :=
  workload_delivers prepared rows (prepareLoader_value _ _ _) τ overhead zeros true 0
    two_deliveries false

example : compiled.2+(workload compiled.1 τ overhead zeros true 0 5 false).2≤
    (workload prepared τ overhead zeros true 0 5 false).2 := by
  apply (compile_amortizes model.transition finTwoEquiv τ overhead zeros true 0
    two_deliveries false).2
  decide +kernel

abbrev initial := (beginWork prepared τ true 0).1
abbrev retry := TableProducer.retryTape
/-- Pause halfway through 1111. The cached row and partial accumulator survive. -/
example : project (Resources.run (tick prepared τ overhead retry) (List.replicate 2 ()) initial).1=
    ((true,(2,2,3)),[]) := by decide +kernel
/-- Finishing that block rejects it without emitting a transition. -/
example : project (Resources.run (tick prepared τ overhead retry) (List.replicate 4 ()) initial).1=
    ((true,(4,4,0)),[]) := by decide +kernel
example : (workload prepared τ overhead retry true 0 8 false).1=
    ([false],Applications.Probability.TableProducer.start rows false 8) := by decide +kernel

/-- A nonzero input cursor is retained, and the finite adapter adds only its
separate terminal fee to the same eager-prefetch execution. -/
example : (workload prepared τ overhead zeros true 7 5 true).1=
    ([false,true],Applications.Probability.TableProducer.start rows true 12) ∧
    (workload prepared τ overhead zeros true 7 5 true).2=118 := by decide +kernel

example : (workload prepared τ overhead zeros true 0 5 true).2=
    (workload prepared τ overhead zeros true 0 5 false).2+overhead.admin :=
  workload_admin _ _ _ _ _ _ _

/-- Resumption retains the exact state and charge, including the rejected block. -/
example : Resources.run (tick prepared τ overhead retry)
    (List.replicate 2 () ++ List.replicate 6 ()) initial=
    Resources.bind (Resources.run (tick prepared τ overhead retry) (List.replicate 2 ()) initial)
      (Resources.run (tick prepared τ overhead retry) (List.replicate 6 ())) :=
  resume _ _ _ _ _ _ _

example : (∫⁻ ω,chargedWork prepared rows τ overhead 0 2 true 0 false ω ∂CoinPaths.law)<∞ :=
  expected_charged_finite model.transition finTwoEquiv prepared (prepareLoader_value _ _ _)
    τ overhead 0 2 true 0 false

example : (∫⁻ ω,bitWork rows 2 true 0 ω ∂CoinPaths.law)≤40 := by
  have hw : maxWidth rows=5 := by decide +kernel
  have hb := expected_bits_le model.transition finTwoEquiv 2 true 0
  rw [show maxWidth (model.transition.prepare finTwoEquiv)=5 from hw] at hb
  norm_num at hb
  exact hb

example : (∫⁻ ω,chargedWork compiled.1 rows τ overhead compiled.2 2 true 0 false ω
    ∂CoinPaths.law)<∞ :=
  expected_charged_finite model.transition finTwoEquiv compiled.1
    (fun x => (compileLoader_value _ _ _ x).trans (Table.compile_eq _ _ _ _))
    τ overhead compiled.2 2 true 0 false

/-- Deadline bounds retain probability of not finishing, rather than conditioning
on the outputs that happened to fit inside the budget. -/
example : CoinPaths.law {ω | ¬chargedWork prepared rows τ overhead 0 2 true 0 false ω≤
    (baseCost prepared τ overhead 0 2 true false+2*(maxWidth rows*2)*
      drawCap prepared rows τ overhead : ℕ)}≤2*(2⁻¹ : ℝ≥0∞)^2 :=
  charged_deadline model.transition finTwoEquiv prepared (prepareLoader_value _ _ _)
    τ overhead 0 2 true 0 2 false

/-- Repricing commutes with the same paused resource execution. -/
example (h : ℕ →+ ℕ) :
    Resources.reweight h (Resources.run (tick prepared τ overhead retry)
      (List.replicate 2 ()) initial)=
    Resources.run (fun u z => Resources.reweight h (tick prepared τ overhead retry u z))
      (List.replicate 2 ()) initial := reweight h _ _ _ _ _ _

private theorem exceptional_no_delivery :
    ¬∃ ys z k,ys.length=1 ∧ Progress.Delivers
      (Applications.Probability.TableProducer.step TableProducer.singletonRows (fun _ => true))
      (Applications.Probability.TableProducer.start TableProducer.singletonRows () 0) ys z k := by
  rintro ⟨ys,z,k,hlen,h⟩
  cases h with
  | nil => simp at hlen
  | cons first rest =>
    obtain ⟨t,hr,_⟩ := Applications.Probability.TableProducer.row_of_evaluates first
    obtain ⟨r,a,ha,_,_,_⟩ := (PreparedRow.evaluates_iff _ _ _ _ _ _).mp hr
    have ht : (TableProducer.singletonRows ()).total=1 := by decide +kernel
    have bad (N : ℕ) (hN : N=1) (r s : ℕ) (a : Fin N) :
        ¬BoundedUniform.Accept N (fun _ => true) s r a := by
      subst N
      induction r generalizing s with
      | zero => change ¬1=a.val; omega
      | succ r ih => exact fun h => ih _ h.2
    exact bad _ ht _ _ a ha

/-- Zero tariffs cannot make a non-delivered observation meet a deadline. -/
example : chargedWork (freeLoader TableProducer.singletonRows) TableProducer.singletonRows
    ⟨0,0,0,0,0,0,0,0⟩ ⟨0,0,0⟩ 0 1 () 0 false (fun _ => true)=∞ :=
  chargedWork_of_divergence _ _ _ _ _ _ _ _ _ _ exceptional_no_delivery

/-- Almost-sure termination alone still does not imply finite expected work. -/
example : ∫⁻ n,((2^n+1 : ℕ) : ℝ≥0∞) ∂ProbabilityProgress.HeavyTail.sampleLaw=∞ :=
  ProbabilityProgress.HeavyTail.lintegral_cost_eq_top

end Examples.SamplerWorkload

import Applications.Probability.FiniteMHSampler
import Applications.Probability.SamplerWork

/-! Checked exact rows, dependent sequential sampling, and actual MH chains. -/
namespace Examples.TableSampler
open Applications.Probability MeasureTheory
open scoped ENNReal

/-- A zero outcome alongside genuinely non-dyadic probabilities. -/
def sparse : Table Unit (Fin 3) where
  entry _ i := if i=0 then 0 else if i=1 then 1/3 else 2/3
  nonneg _ i := by fin_cases i <;> norm_num
  sum_row _ := by norm_num [Fin.sum_univ_succ]

abbrev row : PreparedRow (Fin 3) := sparse.prepare (Equiv.refl _) ()
example : row.total=9 := by decide +kernel
example : row.weight ⟨0,by decide +kernel⟩=0 ∧ row.weight ⟨1,by decide +kernel⟩=3 ∧ row.weight ⟨2,by decide +kernel⟩=6 := by decide +kernel
example : Progress.search (row.step (fun _ => false)) 4 (row.start 2)=some ((1,6),4) := by decide +kernel
example : Progress.search (row.step (fun _ => false)) 3 (row.start 2)=none := by decide +kernel
example : CoinPaths.law (row.returns 2 0)=0 := by
  rw [Table.prepare_returns_mass]; norm_num [sparse,mass]
example : CoinPaths.law (row.returns 2 1)=(3⁻¹ : ℝ≥0∞) := by
  rw [Table.prepare_returns_mass]; norm_num [sparse,mass,ENNReal.ofReal_div_of_pos]

/-- Zero weights do not occupy an interval, including before a deterministic output. -/
def deterministic : Table Unit (Fin 3) := Table.deterministic (fun _ => 2)
abbrev certain : PreparedRow (Fin 3) := deterministic.prepare (Equiv.refl _) ()
example : certain.total=1 := by decide +kernel
example : Progress.search (certain.step (fun _ => false)) 1 (certain.start 4)=some ((2,5),1) := by decide +kernel
example : Progress.search (certain.step (fun i => decide (i=4))) 1 (certain.start 4)=none := by decide +kernel
example : Progress.search (certain.step (fun i => decide (i=4))) 2 (certain.start 4)=some ((2,6),2) := by decide +kernel
example : CoinPaths.law (certain.returns 4 2)=1 := by
  rw [Table.prepare_returns_mass]; norm_num [deterministic,Table.deterministic,mass]

/-- The second row depends on the first result, retaining both outcomes. -/
def dependent : Table (Fin 3) Bool where
  entry a b := if b then (a.val : ℚ)/3 else 1-(a.val : ℚ)/3
  nonneg a b := by fin_cases a <;> cases b <;> norm_num
  sum_row a := by simp

example : CoinPaths.law {ω | ∃ v w k, Progress.Evaluates
    (row.pairStep (dependent.prepare finTwoEquiv) ω) (.inl (row.start 0))
      ((1,v),(true,w)) k}=(1/9 : ℝ≥0∞) := by
  rw [Table.sequential_joint_mass]
  norm_num [sparse,dependent,mass,ENNReal.ofReal_div_of_pos,← ENNReal.mul_inv]

/-- Existing asymmetric MH transition, concretely prepared and executable. -/
abbrev mhRows := FiniteMHExamples.asymmetric.transition.compile finTwoEquiv finTwoEquiv
example : mhRows true=FiniteMHExamples.asymmetric.transition.prepare finTwoEquiv true :=
  Table.compile_eq _ _ _ _
example : (mhRows true).total=9 := by decide +kernel
example : Progress.search ((mhRows true).step (fun _ => false)) 4 ((mhRows true).start 0)=
    some ((false,4),4) := by decide +kernel

/-- Two actual transitions, followed by the explicit administrative return.
The path and cursor show both row executions, rather than a precomposed table draw. -/
example : Progress.search (RowChain.step mhRows (fun _ => false) 2)
    6 (RowChain.start mhRows 2 true 0)=some (([false,true],5),6) := by decide +kernel
example : Progress.search (RowChain.step mhRows (fun _ => false) 2)
    5 (RowChain.start mhRows 2 true 0)=none := by decide +kernel
example : Progress.search (RowChain.step mhRows (fun _ => true) 0)
    1 (RowChain.start mhRows 0 true 7)=some (([],7),1) := by decide +kernel

example : CoinPaths.law (RowChain.returns (FiniteMHExamples.asymmetric.transition.prepare finTwoEquiv)
    2 true 0 [false,true])=(1/3 : ℝ≥0∞) := by
  rw [RowChain.table_path_mass _ _ _ _ _ _ (by decide +kernel)]
  norm_num [RowChain.pathMass,FiniteMH.transition,FiniteMH.accepted,FiniteMH.acceptance,
    FiniteMH.rejection,FiniteMHExamples.asymmetric,Fintype.sum_bool,mass,ENNReal.ofReal_div_of_pos]

/-- Restarting an identical row changes the full joint law. -/
example : CoinPaths.law {ω | ∃ t u k, Progress.Evaluates
    (row.pairStep (fun _ => row) ω) (.inl (row.start 0)) ((1,t),(2,u)) k}=(2/9 : ℝ≥0∞) := by
  rw [PreparedRow.pair_joint_mass,Table.prepare_returns_mass,Table.prepare_returns_mass]
  norm_num [sparse,mass,ENNReal.ofReal_div_of_pos]
  simp only [div_eq_mul_inv]
  rw [mul_left_comm,← ENNReal.mul_inv] <;> norm_num

example : CoinPaths.law {ω | ∃ t u k, Progress.Evaluates
    (row.reusedPairStep 0 ω) (.inl (row.start 0)) ((1,t),(2,u)) k}=0 :=
  row.reused_off_diagonal 0 1 2 (by decide)

/-- One block gives output1 mass3/16, less than its uncapped mass1/3. -/
example : CoinPaths.law {ω | Progress.search (row.step ω) 4 (row.start 0)=
    some ((1,4),4)}=(3/16 : ℝ≥0∞) := by
  have hw : BoundedUniform.width row.total=4 := by decide +kernel
  have h := row.one_block_mass 0 1
  rw [hw] at h
  simp only [zero_add] at h
  rw [h]
  have hs := row.sum_select (fun b => if b=(1 : Fin 3) then (2⁻¹ : ℝ≥0∞)^4 else 0)
  rw [hs]
  change (∑ j : Fin 3, (row.weight j : ℝ≥0∞)*(if j=1 then (2⁻¹ : ℝ≥0∞)^4 else 0))=_
  simp only [Fin.sum_univ_succ]
  norm_num [← ENNReal.inv_pow,div_eq_mul_inv]
  congr 1
  exact_mod_cast (by decide +kernel : row.weight (1 : Fin 3)=3)

/-- Unit tariffs expose the preparation/draw boundary in executable cases. -/
def unitTariff : SamplerWork.Tariff := ⟨1,1,1,1,1,1,1,1⟩
example : (SamplerWork.prepareMetered sparse (Equiv.refl _) () unitTariff).2=33 := by
  rw [SamplerWork.prepareMetered_cost]; decide
example : Progress.search (SamplerWork.measuredStep row unitTariff (fun _ => false))
    4 (row.start 2,SamplerWork.initialization unitTariff)=some (((1,6),36),4) := by
  decide +kernel
example : Progress.search (SamplerWork.measuredStep certain unitTariff (fun _ => false))
    1 (certain.start 4,SamplerWork.initialization unitTariff)=some (((2,5),15),1) := by
  decide +kernel

/-- A work budget includes initialization, bits, arithmetic and selection.
The independently charged preparation costs 33 more units for this row. -/
example : CoinPaths.law {ω | ¬∃ a t w k,
    Progress.Evaluates (SamplerWork.measuredStep row unitTariff ω)
      (row.start 2,SamplerWork.initialization unitTariff) ((a,t),w) k ∧ w ≤ 158} ≤
      BoundedUniform.rejection row.total := by
  have h := SamplerWork.measured_timeout_mass_le row unitTariff 2 4
  have hb : SamplerWork.initialization unitTariff+4*SamplerWork.perBitBound row unitTariff=158 := by
    decide +kernel
  have hw : BoundedUniform.width row.total=4 := by decide +kernel
  simpa only [hb,hw,Nat.div_self (by decide : 0<4),pow_one] using h

end Examples.TableSampler

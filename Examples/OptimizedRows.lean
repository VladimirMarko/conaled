import Applications.Probability.OptimizedRowWork
import Applications.Probability.LinearRowSelector
import Examples.TableSampler

/-! Checked representation and cost distinctions for normalized exact rows. -/
namespace Examples.OptimizedRows
open Applications.Probability MeasureTheory
open scoped ENNReal

abbrev sparse := TableSampler.sparse
abbrev old : PreparedRow (Fin 3) := sparse.prepare (Equiv.refl _) ()
abbrev normalized : PreparedRow (Fin 3) := sparse.prepareNormalized (Equiv.refl _) ()

example : normalized.total=3 ∧ old.total=9 := by decide +kernel
example : normalized.total≤old.total := Table.prepareNormalized_total_le _ _ _
example : normalized.weight ⟨0,by decide +kernel⟩=0 ∧ normalized.weight ⟨1,by decide +kernel⟩=1 ∧ normalized.weight ⟨2,by decide +kernel⟩=2 := by decide +kernel
example (s : ℕ) (b : Fin 3) :
    CoinPaths.law (normalized.returns s b)=CoinPaths.law (old.returns s b) := by
  rw [Table.prepareNormalized_returns_mass,Table.prepare_returns_mass]

/-- Equal output laws do not preserve fuel success or the returned cursor. -/
example : Progress.search (normalized.step (fun _ => false)) 2 (normalized.start 0)=some ((1,2),2) ∧
    Progress.search (old.step (fun _ => false)) 2 (old.start 0)=none := by decide +kernel
example : Progress.search (old.step (fun _ => false)) 4 (old.start 0)=some ((1,4),4) := by decide +kernel

/-- The same tape can select different values, not just different cursors. -/
example : Progress.search (normalized.step (fun i => decide (i=2 ∨ i=3))) 2 (normalized.start 0)=
    some ((1,2),2) ∧
    Progress.search (old.step (fun i => decide (i=2 ∨ i=3))) 4 (old.start 0)=some ((2,4),4) := by decide +kernel

/-- A rejection pattern changes as well: the old first four bits encode eleven,
while the normalized first two bits already accept code two. -/
example : Progress.search (normalized.step (fun i => decide (i=0 ∨ i=2 ∨ i=3))) 2
    (normalized.start 0)=some ((2,2),2) ∧
    Progress.search (old.step (fun i => decide (i=0 ∨ i=2 ∨ i=3))) 4
    (old.start 0)=none := by decide +kernel

abbrev deterministic : PreparedRow (Fin 3) := TableSampler.deterministic.prepareNormalized (Equiv.refl _) ()
example : deterministic.total=1 ∧ deterministic.weight ⟨0,by decide +kernel⟩=0 ∧ deterministic.weight ⟨2,by decide +kernel⟩=1 := by decide +kernel
example : Progress.search (deterministic.step (fun _ => false)) 1 (deterministic.start 0)=some ((2,1),1) := by decide +kernel

def mixed : Table Unit (Fin 3) where
  entry _ i := if i=0 then 1/2 else if i=1 then 1/3 else 1/6
  nonneg _ i := by fin_cases i <;> norm_num
  sum_row _ := by norm_num [Fin.sum_univ_succ]
example : (mixed.prepareNormalized (Equiv.refl _) ()).total=6 ∧
    (mixed.prepare (Equiv.refl _) ()).total=36 := by decide +kernel
example (s : ℕ) (i : Fin 3) : CoinPaths.law ((mixed.prepareNormalized (Equiv.refl _) ()).returns s i)=
    mass (mixed.entry () i) := Table.prepareNormalized_returns_mass _ _ _ _ _

def unitTariff : SamplerWork.Tariff := ⟨1,1,1,1,1,1,1,1⟩
example (k : Fin normalized.total) :
    (LinearRowSelector.rowSelect normalized unitTariff k).1=normalized.select k :=
  LinearRowSelector.rowSelect_value _ _ _
example (k : Fin normalized.total) :
    (LinearRowSelector.rowSelect normalized unitTariff k).2≤11 :=
  LinearRowSelector.rowSelect_bound _ _ _
example : (LinearRowSelector.rowSelect normalized unitTariff ⟨0,normalized.positive⟩).2=8 ∧
    (SamplerWork.rowSelect normalized unitTariff ⟨0,normalized.positive⟩).2=10 := by decide +kernel

/-- Three constant transition rows expose all caching costs, even for unused states. -/
def chain : Table (Fin 3) (Fin 3) where
  entry _ := sparse.entry ()
  nonneg _ := sparse.nonneg ()
  sum_row _ := sparse.sum_row ()

def normalizedTariff : OptimizedRowWork.Tariff := ⟨unitTariff,10⟩
def overhead : SamplerWorkload.Overhead := ⟨1,1,1⟩
abbrev oldLoader := SamplerWorkload.prepareLoader chain (Equiv.refl _) unitTariff
abbrev newLoader : SamplerWorkload.Loader (Fin 3) :=
  fun x => OptimizedRowWork.prepareMetered chain (Equiv.refl _) x normalizedTariff
abbrev compiled := OptimizedRowWork.compileLoader chain (Equiv.refl _) normalizedTariff

example : OptimizedRowWork.preparationCost 3 normalizedTariff=60 ∧
    SamplerWorkload.preparationCost 3 unitTariff=33 := by decide +kernel
example : compiled.2=186 := by
  rw [OptimizedRowWork.compileLoader_setup]
  decide +kernel
example : OptimizedRowWork.compileStorage chain (Equiv.refl _) normalizedTariff=12 := by
  rw [OptimizedRowWork.compileStorage_eq]
  rfl

/-- Up-front compilation loses on this one-output workload, including the eager
load after the final emission and final chronological output handling. -/
example : (SamplerWorkload.workload oldLoader unitTariff overhead (fun _ => false) 0 0 4 false).2=106 ∧
    compiled.2+(OptimizedRowWork.workload compiled.1 unitTariff overhead (fun _ => false) 0 0 2 false).2=214 := by
  decide +kernel

/-- The same policy wins after four outputs. Different bit counts are intentional;
this comparison retains four outputs, not a common raw-bit budget. -/
example : (SamplerWorkload.workload oldLoader unitTariff overhead (fun _ => false) 0 0 16 false).2=319 ∧
    compiled.2+(OptimizedRowWork.workload compiled.1 unitTariff overhead (fun _ => false) 0 0 8 false).2=289 := by
  decide +kernel

example : (SamplerWorkload.workload oldLoader unitTariff overhead (fun _ => false) 0 0 16 false).1.1=[1,1,1,1] ∧
    (OptimizedRowWork.workload compiled.1 unitTariff overhead (fun _ => false) 0 0 8 false).1.1=[1,1,1,1] := by
  decide +kernel

/-- Caching is not free even with normalization already selected. -/
example : (OptimizedRowWork.workload newLoader unitTariff overhead (fun _ => false) 0 0 2 false).2=146 ∧
    compiled.2+(OptimizedRowWork.workload compiled.1 unitTariff overhead (fun _ => false) 0 0 2 false).2=214 := by
  decide +kernel
example : (OptimizedRowWork.workload newLoader unitTariff overhead (fun _ => false) 0 0 8 false).2=398 ∧
    compiled.2+(OptimizedRowWork.workload compiled.1 unitTariff overhead (fun _ => false) 0 0 8 false).2=289 := by
  decide +kernel

/-- The selector alone preserves the entire workload state and output, including
unfinished blocks, while the resource observation is allowed to differ. -/
example (ω : CoinPaths.Tape) (bits : ℕ) :
    (OptimizedRowWork.workload compiled.1 unitTariff overhead ω 0 0 bits false).1=
      (SamplerWorkload.workload compiled.1 unitTariff overhead ω 0 0 bits false).1 :=
  OptimizedRowWork.workload_value _ _ _ _ _ _ _ _

example (x : Fin 3) (s : ℕ) (ys : List (Fin 3)) :
    CoinPaths.law (TableProducer.prefixEvent (chain.prepareNormalized (Equiv.refl _)) x s ys)=
      CoinPaths.law (TableProducer.prefixEvent (chain.prepare (Equiv.refl _)) x s ys) := by
  rw [Table.normalized_prefix_mass,TableProducer.prefix_mass]

example (x : Fin 3) (s : ℕ) :
    ProbabilityProgress.AlmostSureProductive CoinPaths.law
      (TableProducer.step (chain.prepareNormalized (Equiv.refl _)))
      (fun _ => TableProducer.start (chain.prepareNormalized (Equiv.refl _)) x s) :=
  Table.normalized_productive _ _ _ _

example (s : ℕ) (a : Fin 3) (ys : List (Fin 3)) :
    CoinPaths.law (InitializedProducer.jointEvent normalized (chain.prepareNormalized (Equiv.refl _)) s a ys)=
      mass (sparse.entry () a)*mass (RowChain.pathMass chain a ys) :=
  Table.normalized_joint _ _ _ _ _ _

example (n s : ℕ) (ys : List Bool) :
    CoinPaths.law (InitializedProducer.blockEvent
      ((InitializedProducer.targetInitial FiniteMHExamples.asymmetric).prepareNormalized finTwoEquiv ())
      (FiniteMHExamples.asymmetric.transition.prepareNormalized finTwoEquiv) n s ys)=
    CoinPaths.law (InitializedProducer.blockEvent
      ((InitializedProducer.targetInitial FiniteMHExamples.asymmetric).prepare finTwoEquiv ())
      (FiniteMHExamples.asymmetric.transition.prepare finTwoEquiv) n s ys) := by
  rw [FiniteMH.normalized_stationary_blocks,InitializedProducer.mh_stationary_blocks]

/-- The existing stopped-cursor theorem applies to the new row without a new
independence assumption. The continuation is started at the returned cursor. -/
example (s : ℕ) : CoinPaths.law (normalized.joint (fun _ => normalized) s 1 2)=
    mass (1/3)*mass (2/3) := by
  rw [PreparedRow.joint_mass,Table.prepareNormalized_returns_mass,Table.prepareNormalized_returns_mass]
  rfl
end Examples.OptimizedRows

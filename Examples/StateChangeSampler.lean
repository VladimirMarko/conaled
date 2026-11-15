import Applications.Probability.StateChangeSampler

/-! The jump chain changes the invariant distribution even for two states. -/
namespace Examples.StateChangeSampler
open Applications.Probability
open Applications.Probability.StateChangeSampler

def original : Table Bool Bool where
  entry x y := if x then (if y then 3/4 else 1/4) else 1/2
  nonneg x y := by cases x <;> cases y <;> norm_num
  sum_row x := by cases x <;> norm_num [Fintype.sum_bool]

def initial : Table Unit Bool where
  entry _ x := if x then 2/3 else 1/3
  nonneg _ x := by cases x <;> norm_num
  sum_row _ := by norm_num [Fintype.sum_bool]

theorem exit_positive (x : Bool) : 0<exit original x := by
  cases x <;> norm_num [exit,original]

theorem original_stationary (y : Bool) :
    (∑ x, initial.entry () x*original.entry x y)=initial.entry () y := by
  cases y <;> norm_num [initial,original,Fintype.sum_bool]

example : exit original false=1/2 ∧ exit original true=1/4 := by
  norm_num [exit,original]

example (x y : Bool) : (jump original exit_positive).entry x y=
    (if x=y then 0 else 1) := by
  cases x <;> cases y <;> norm_num [jump,exit,original]

example (x : Bool) : (tilted original exit_positive initial).entry () x=1/2 := by
  cases x <;> norm_num [tilted,normalizer,exit,original,initial,Fintype.sum_bool]

example (y : Bool) :
    (∑ x, (tilted original exit_positive initial).entry () x *
      (jump original exit_positive).entry x y)=
        (tilted original exit_positive initial).entry () y :=
  tilted_stationary original exit_positive initial original_stationary y

example : ¬∀ y, (∑ x, initial.entry () x*(jump original exit_positive).entry x y)=
    initial.entry () y := by
  intro h
  have hf := h false
  norm_num [initial,jump,exit,original,Fintype.sum_bool] at hf

example : exit (Table.deterministic id : Table Unit Unit) ()=0 := by
  simp [exit,Table.deterministic]

abbrev rows := original.prepare finTwoEquiv

def changeTape (i : ℕ) : Bool := decide (i=2)

/-- 00 is a self transition, then 10 changes false to true. -/
example : Progress.search (TableProducer.changes rows changeTape) 4
    (TableProducer.start rows false 0)=some ((true,TableProducer.start rows true 4),4) := by
  decide +kernel

example : ∃ t, TableProducer.start rows true 4=TableProducer.start rows true t ∧
    ChangeTrace rows changeTape false ((rows false).start 0) true t 4 := by
  apply trace_of_change
  exact Progress.search_sound (fuel := 4) (by decide +kernel)

/-- The exact retained partial row also resumes through the general trace API. -/
example : ∃ t, TableProducer.start rows true 4=TableProducer.start rows true t ∧
    ChangeTrace rows changeTape false (1,1,0) true t 3 := by
  apply trace_of_change
  exact Progress.search_sound (fuel := 3) (by decide +kernel)

example : Progress.search (TableProducer.changes rows changeTape) 3
    (TableProducer.start rows false 0)=none := by decide +kernel

example (s : ℕ) (ys : List Bool) : prefixEvent rows false s (false::ys)=∅ :=
  prefix_same rows false s ys

open MeasureTheory
open scoped ENNReal

/-- The original machine changes forever almost surely, with checked exits. -/
example (x : Bool) (s : ℕ) :
    ProbabilityProgress.AlmostSureProductive CoinPaths.law (TableProducer.changes rows)
      (fun _ => TableProducer.start rows x s) :=
  almostSureProductive original exit_positive rows (original.prepare_returns_mass finTwoEquiv)
    finTwoEquiv x s

/-- Complete ordered observations alternate; self changes have probability zero. -/
example (s : ℕ) : CoinPaths.law (prefixEvent rows false s [true,false,true])=1 := by
  rw [prefix_mass original exit_positive rows (original.prepare_returns_mass finTwoEquiv)]
  norm_num [RowChain.pathMass,jump,exit,original,mass]

example (s : ℕ) : CoinPaths.law (prefixEvent rows false s [true,true])=0 := by
  rw [prefix_mass original exit_positive rows (original.prepare_returns_mass finTwoEquiv)]
  norm_num [RowChain.pathMass,jump,exit,original,mass]

/-- The actual tilted initial draw is followed at its returned cursor by the
filtered chain. Every shifted pair has the alternating stationary law. -/
example (n s : ℕ) : CoinPaths.law
    (initializedBlock ((tilted original exit_positive initial).prepare finTwoEquiv ())
      rows n s [false,true])=(1/2 : ℝ≥0∞) := by
  rw [initialized_stationary_blocks original exit_positive rows
    (original.prepare_returns_mass finTwoEquiv) finTwoEquiv initial original_stationary]
  norm_num [Fintype.sum_bool,tilted,normalizer,RowChain.pathMass,jump,exit,original,initial,
    mass,ENNReal.ofReal_div_of_pos]
  rw [show (6 : ℝ≥0∞)=3*2 by norm_num,ENNReal.mul_inv,div_eq_mul_inv,inv_inv,
    mul_right_comm,ENNReal.inv_mul_cancel (by norm_num : (3 : ℝ≥0∞)≠0) (by simp),one_mul] <;> norm_num

/-- Freshness applies to arbitrary measurable future observations at the actual
change cursor, including all earlier suppressed rows. -/
example (s : ℕ) (B : Set CoinPaths.Tape) (hB : MeasurableSet B) :
    CoinPaths.law (changeThen rows false s true B)=CoinPaths.law B := by
  rw [change_stopped_mass original exit_positive rows (original.prepare_returns_mass finTwoEquiv)
    false true s B hB]
  norm_num [jump,exit,original,mass]

abbrev singletonRows := (Table.deterministic id : Table Unit Unit).prepare
  (Equiv.ofUnique (Fin 1) Unit)

example : ¬∀ x,0<exit (Table.deterministic id : Table Unit Unit) x := by
  intro h
  have hh := h ()
  simp [exit,Table.deterministic] at hh

example (ω : CoinPaths.Tape) : ¬Progress.Productive (TableProducer.changes singletonRows ω)
    (TableProducer.start singletonRows () 0) := TableProducer.changes_not_productive _ _ _

/-- An accepted MH self-proposal remains invisible to change-only observation;
its unchanged state does not identify rejection. -/
example : FiniteMHExamples.asymmetric.acceptance true true=1 ∧
    FiniteMHExamples.asymmetric.proposal.entry true true=1/2 ∧
    FiniteMHExamples.asymmetric.rejection true=1/6 := by
  constructor
  · norm_num [FiniteMH.acceptance,FiniteMHExamples.asymmetric]
  constructor
  · norm_num [FiniteMHExamples.asymmetric]
  · exact FiniteMHExamples.asymmetric_rejection

end Examples.StateChangeSampler

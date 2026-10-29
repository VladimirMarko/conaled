import Applications.FRP.FiniteDelay
import Applications.Interaction.EvidenceBounds
import Applications.Progress.OccurrenceCursor
import Applications.Probability.FiniteKernel

/-! Checked applications and failed variants for the two-client preservation
experiment. Mathematical cell/probe observations are not allocation measurements. -/
namespace Examples.PreservationBounds
open Progress Progress.Feedback
open FRPSpec FRPSpec.Frontier FRPSpec.Frontier.Trace
open SquareKit.PreservationBounds

example : run FiniteDelay.machine.mealy FiniteDelay.machine.initial [true,false,true] =
    ([false,true,false],true) := by rw [FiniteDelay.correct]; decide

example : run (seq FiniteDelay.machine FiniteDelay.machine).mealy
    (FiniteDelay.machine.initial,FiniteDelay.machine.initial) [true,false,true] =
    ([false,false,true],(true,false)) := by
  rw [FiniteDelay.two_delays,FiniteDelay.correct]
  decide

def sources : Inputs Nat Bool := fun _ => Frontier.initial 2
def commands : List (Engine.Command Nat Bool) :=
  [.register 2,.source .left ⟨3,[(2,[true])]⟩,.source .right ⟨3,[]⟩,.process]

example : (Pipeline.run FiniteDelay.consumer
    (Pipeline.init sources FiniteDelay.consumer) commands).2 =
    [(none,none),(none,none),(none,none),(some (2,[true]),some false)] := by decide

example : (Pipeline.run FiniteDelay.redundantConsumer
    (Pipeline.init sources FiniteDelay.redundantConsumer) commands).2 =
    [(none,none),(none,none),(none,none),(some (2,[true]),some false)] := by
  rw [← (FiniteDelay.pipeline_related sources commands).1]
  decide

example : ∃ B, ∀ cs : List (Engine.Command Nat Bool),
    FiniteDelay.redundantCells (Pipeline.run FiniteDelay.redundantConsumer
      (Pipeline.init sources FiniteDelay.redundantConsumer) cs).1.consumer ≤ B :=
  ⟨2,FiniteDelay.pipeline_cells sources⟩

/-- Direct author task, kept alongside the shared route. The constant-cell
case is simpler directly; transport is useful when a relation is already needed. -/
theorem direct_delay_bound (cs : List (Engine.Command Nat Bool)) :
    FiniteDelay.redundantCells (Pipeline.run FiniteDelay.redundantConsumer
      (Pipeline.init sources FiniteDelay.redundantConsumer) cs).1.consumer ≤ 2 := le_rfl

theorem direct_evidence_bound :
    ∀ t ∈ Interaction.Evidence.encodedReachable, t.1 ≤ 1 := by
  rintro t ⟨s,hs,rfl⟩
  exact (Interaction.Evidence.reachable_effects s hs).le

example : ∃ s', FiniteDelay.machine.step (true,false) = (false,s') :=
  FiniteDelay.next_output false true

/-- Equal semantic output and related state also give covered final states;
coverage itself does not assert the nonemptiness of arbitrary behavior sets. -/
example : SquareKit.RelationTransport.requirement (fun (_ : Unit) (_ : Bool) => False)
    (∅ : Set Bool) () ∧
    ¬ Interaction.Refines (fun (_ : Unit) (_ : Bool) => False) Set.univ {true} := by
  refine ⟨fun _ h => h.elim,?_⟩
  intro h
  obtain ⟨_,_,bad⟩ := h (show true ∈ ({true} : Set Bool) from rfl)
  exact bad

/-- Two independently live two-cell stores need four cells. This is addition
of retained holdings, even though an independently justified scratch peak could
use max. The shared theorem exposes the operation instead of choosing it. -/
example (s t : Bool × Bool) :
    FiniteDelay.redundantCells s + FiniteDelay.redundantCells t ≤ 2 * (1+1) :=
  combine Nat.add Nat.add (fun n => 2*n)
    (fun ha hb => Nat.add_le_add ha hb) (fun a b => by simp [Nat.mul_add])
    (Nat.le_refl 2) (Nat.le_refl 2)

example (a b : Nat) : max (2*a) (2*b) ≤ 2 * max a b :=
  combine max max (fun n => 2*n) (fun ha hb => max_le_max ha hb)
    (fun a b => max_le (Nat.mul_le_mul_left 2 (le_max_left a b))
      (Nat.mul_le_mul_left 2 (le_max_right a b))) le_rfl le_rfl

/-- Monotonicity alone does not preserve additive composition: translating
each component through n+1 pays its overhead twice. -/
example : Monotone (fun n : Nat => n+1) ∧
    ¬ (∀ a b : Nat, (a+1)+(b+1) ≤ (a+b)+1) := by
  refine ⟨fun _ _ h => Nat.add_le_add_right h 1,?_⟩
  intro h
  have := h 0 0
  omega

/-- An explicit evaluation phase retains both stores and the intermediate Bool.
This abstract live-cell model discharges the otherwise missing wiring buffer;
it makes no statement about the Lean runtime's temporary allocations. -/
def liveCells (frame : ((Bool × Bool) × (Bool × Bool)) × Option Bool) : Nat :=
  FiniteDelay.redundantCells frame.1.1 + FiniteDelay.redundantCells frame.1.2 +
    (if frame.2.isSome then 1 else 0)

def middle (x : Bool) (s t : Bool × Bool) :=
  let first := FiniteDelay.redundant.step (x,s)
  ((first.2,t),some first.1)

example (x : Bool) (s t : Bool × Bool) : liveCells (middle x s t) = 5 := rfl
example (frame : ((Bool × Bool) × (Bool × Bool)) × Option Bool) : liveCells frame ≤ 5 := by
  simp only [liveCells,FiniteDelay.redundantCells]
  split <;> omega

/-- Relational representation changes retain an actual intermediate witness. -/
example : Interaction.Refines
    (Relation.Comp Interaction.Evidence.Encoding
      (fun (s : Interaction.Evidence.Encoded) (t : Option Interaction.Evidence.Encoded) =>
        some s = t)) Interaction.Evidence.reachable
    (some '' Interaction.Evidence.encodedReachable) :=
  Interaction.Evidence.encoding_coverage.trans (by
    rintro t ⟨s,hs,rfl⟩
    exact ⟨s,hs,rfl⟩)

example (s : Interaction.Evidence.State) (_t : Interaction.Evidence.Encoded) (z : Nat)
    (h : Relation.Comp Interaction.Evidence.Encoding
      (fun (t : Interaction.Evidence.Encoded) z => z = t.1+1) s z) : z ≤ s.effects+1 :=
  comparison_comp Interaction.Evidence.State.effects Prod.fst id id (fun n => n+1)
    (fun _ _ h => Nat.add_le_add_right h 1)
    (fun _ _ h => by cases h; exact le_rfl)
    (fun _ _ h => h.le) s z h

example : (∀ n, (Interaction.Evidence.encode (Interaction.Evidence.interrupted n)).1 ≤ 1) ∧
    ¬ ∃ n, (Interaction.Evidence.interrupted n).acknowledged = true :=
  Interaction.Evidence.safe_without_progress

/-- Every finite queue has finite length, while one enqueue per unserviced tick
rules out a workload-independent bound over all prefixes. -/
example : (∀ n, ∃ B, (List.replicate n false).length ≤ B) ∧
    ¬ ∃ B, ∀ n, (List.replicate n false).length ≤ B := by
  constructor
  · intro n; exact ⟨n,by simp⟩
  · rintro ⟨B,h⟩
    have := h (B+1)
    simp only [List.length_replicate] at this
    omega

/-- Forgetting silent positions preserves completed values but changes next. -/
def sparse : List (Option Bool) := [some false,none,some true]
example : sparse.filterMap id = [false,true] ∧
    sparse[1]? = some none ∧ (sparse.filterMap id)[1]? = some true := by decide

/-- Batch observation cannot recover order or occurrence count. -/
example : ([false,true] : List Bool).any id = [true,false].any id ∧
    ([false,true] : List Bool) ≠ [true,false] ∧
    ([true] : List Bool).any id = [true,true].any id := by decide

example := Interaction.Evidence.coarse_loses_publication

open Applications.Probability

def fairTable : Table Unit Bool where
  entry _ _ := 1/2
  nonneg _ _ := by norm_num
  sum_row _ := by norm_num [Fintype.sum_bool]

def biasedTable : Table Unit Bool where
  entry _ b := if b then 1/3 else 2/3
  nonneg _ b := by cases b <;> norm_num
  sum_row _ := by norm_num [Fintype.sum_bool]

/-- Same support is too weak for probability interpretation, even with the
same finite outcome type and total mass one. -/
theorem same_support : ∀ b, (0 < fairTable.entry () b) ↔ (0 < biasedTable.entry () b) := by
  intro b
  cases b <;> norm_num [fairTable,biasedTable]

theorem different_law : fairTable.kernel ≠ biasedTable.kernel := by
  intro h
  have he := congrArg (fun k : ProbabilityTheory.Kernel Unit Bool => k () {true}) h
  rw [Table.kernel_singleton,Table.kernel_singleton] at he
  norm_num [fairTable,biasedTable,mass] at he

open Progress.Feedback.Occurrence

def duplicateHistory : List Bool := [true,true]
def firstOccurrence : Cursor duplicateHistory := ⟨0,by decide⟩
def secondOccurrence : Cursor duplicateHistory := ⟨1,by decide⟩

/-- Both dependent witnesses select the same payload; no payload-only inverse
can recover both occurrences. Native indexed transport is still available. -/
theorem erasure_no_inverse : ¬ ∃ f : Bool → Cursor duplicateHistory,
    f duplicateHistory[firstOccurrence.val] = firstOccurrence ∧
    f duplicateHistory[secondOccurrence.val] = secondOccurrence := by
  rintro ⟨f,h₁,h₂⟩
  have h : firstOccurrence = secondOccurrence := h₁.symm.trans h₂
  have := congrArg Fin.val h
  contradiction

example (a : Stream Bool) (n : Nat) :
    (state (forward duplicateHistory) a n)[(forwardCursor duplicateHistory firstOccurrence a n).val] =
      duplicateHistory[firstOccurrence.val] := selected_value _ _ _ _

end Examples.PreservationBounds

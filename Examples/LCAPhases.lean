import Applications.Sequences.LCA.StrategySelection
import Applications.Sequences.LCA.MachineCapacity
import Applications.Sequences.LCA.PackedBackend
import Examples.LCABackend

set_option autoImplicit false
set_option warningAsError true

namespace Examples.LCAPhases
open Resources.Prepared Sequences.LCA TreeReduction Backend BackendBounds
open LCABackend

-- Startup builds all shared and per-input tables. The immutable service then
-- answers any number of online queries; it never needs the future query list.
example : Feasible (realtime 4) (lcaProfile 4) branchedSource := realtime_feasible branchedSource

example (qs : List (Query 4)) :
    (queries (lcaOps 4) prepared qs).1 = qs.map (sourceLCA branchedSource) :=
  queries_meaning (lca_laws 4) branchedSource prepared ((lca_laws 4).prepare branchedSource) qs

example (qs : List (Query 4)) : (queries (lcaOps 4) prepared qs).2 ≤ qs.length*62 :=
  queries_bound (lca_bounds 4) branchedSource prepared ((lca_laws 4).prepare branchedSource) qs

example : (queries (lcaOps 4) prepared
    [(⟨2,by decide⟩,⟨3,by decide⟩),(⟨1,by decide⟩,⟨2,by decide⟩),
     (⟨2,by decide⟩,⟨3,by decide⟩)]).1 = [0,1,0] := by decide

-- Changing the static tree requires preparation again. The explicit validity
-- relation rejects a same-size tree's old representation (see LCABackend's
-- checked stale-state counterexample); no maintenance operation is promised.
example (input : Input 17) (q : Nat × Nat) (c : StrategySelection.Strategy)
    (h : StrategySelection.choose
      {startup := none, deadline := 57, maintenance := 0, capacity := 612, peak := 8704} input = some c) :
    ((StrategySelection.realize 17 c).answer ((StrategySelection.realize 17 c).prepare input).1 q).2 ≤ 57 :=
  StrategySelection.chosen_deadline h q

def singletonInput : Input 1 :=
  ((TreeReduction.reduction 1).convert ⟨.singleton,rfl⟩).1.2

theorem singletonMachine : Machine singletonInput 16 512 where
  words := by constructor <;> decide
  preparation := preparationPeak_le singletonInput
  query := (BackendBounds.bounds 1).queryPeak singletonInput _ (prepare_valid singletonInput)

example : ¬ Machine singletonInput 16 1 := by
  intro h
  have hp := h.preparation
  have hw : Workspace.words (Workspace.selectedRun (sourceM singletonInput) 1) = 15 := by
    rw [Workspace.selectedRun_words]
    rfl
  simp only [preparationPeak, Catalog.inputWords, Vector.size_toArray, hw] at hp
  omega

-- The retained reservation certified by the profile is exactly the flattened
-- finite-word representation's length, including its reserved minima gap.
example : (PackedBackend.realize singletonInput (machine_arena singletonMachine)).flatten.toArray.size =
    retainedWords ((ops 1).prepare singletonInput).1 := by
  rw [PackedBackend.flattened_size, retainedWords_eq]

end Examples.LCAPhases

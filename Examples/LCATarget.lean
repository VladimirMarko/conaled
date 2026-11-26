import Applications.Sequences.LCA.TargetSelection
import Examples.LCABackend

set_option autoImplicit false
set_option warningAsError true

namespace Examples.LCATarget
open Resources.Prepared Sequences.LCA TreeReduction
open LCABackend

theorem tree_machine : TargetBackend.Config (tourSize 4) 14 := by constructor <;> decide

def singletonSource : Source 1 := ⟨.singleton,rfl⟩
theorem singleton_machine : TargetBackend.Config (tourSize 1) 12 := by constructor <;> decide

example : ((TargetBackend.lcaOps singleton_machine).answer
    ((TargetBackend.lcaOps singleton_machine).prepare singletonSource).1 (0,0)).1 = 0 := by
  rw [(TargetBackend.lca_reusable singleton_machine singletonSource _).1]
  decide

def singletonInput : Input 1 := ((reduction 1).convert singletonSource).1.2

theorem singleton_rmq_machine : TargetBackend.Config 1 12 := by constructor <;> decide

def singletonArena := (TargetPreparation.prepare singletonInput singleton_rmq_machine).1

-- Regression for the reviewed placement mismatch: these words are read from
-- the executed installation, at the compact query addresses.
example : (WordMachine.load singletonArena 2 0).1.val = 3 := by
  unfold singletonArena
  rw [TargetPreparation.prepare_value singletonInput singleton_rmq_machine]
  exact WordLoads.load_sharedDescriptor _ _ ⟨0,by decide⟩

example : (WordMachine.load singletonArena 3 0).1.val = 4 := by
  unfold singletonArena
  rw [TargetPreparation.prepare_value singletonInput singleton_rmq_machine]
  exact WordLoads.load_sharedRowDescriptor _ _ ⟨0,by decide⟩ ⟨0,by decide⟩

example : (WordMachine.load singletonArena 4 0).1.val = 0 := by
  unfold singletonArena
  rw [TargetPreparation.prepare_value singletonInput singleton_rmq_machine]
  have h := WordLoads.load_sharedPayload singletonInput
    (BackendBounds.machine_arena (TargetPreparation.machine singletonInput singleton_rmq_machine))
    ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
  rw [PackedBackend.prepared_shared] at h
  exact h

def prepared := ((TargetBackend.lcaOps tree_machine).prepare branchedSource).1

-- The actual preparation includes compact installation. Online behavior still
-- agrees with independent tree ancestry for every future finite-node query.
example (q : Query 4) :
    ((TargetBackend.lcaOps tree_machine).answer prepared q).1 = sourceLCA branchedSource q ∧
      ((TargetBackend.lcaOps tree_machine).answer prepared q).2 ≤ 62 :=
  TargetBackend.lca_reusable tree_machine branchedSource q

example : ((TargetBackend.lcaOps tree_machine).answer prepared (⟨1,by decide⟩,⟨2,by decide⟩)).1 = 1 := by
  unfold prepared
  rw [(TargetBackend.lca_reusable tree_machine branchedSource _).1]
  decide

example (qs : List (Query 4)) :
    (queries (TargetBackend.lcaOps tree_machine) prepared qs).1 = qs.map (sourceLCA branchedSource) :=
  queries_meaning (TargetBackend.lca_laws tree_machine) branchedSource prepared
    ((TargetBackend.lca_laws tree_machine).prepare branchedSource) qs

example : (queries (TargetBackend.lcaOps tree_machine) prepared
    [(⟨2,by decide⟩,⟨3,by decide⟩),(⟨1,by decide⟩,⟨2,by decide⟩),(⟨2,by decide⟩,⟨3,by decide⟩)]).1 = [0,1,0] := by
  rw [queries_meaning (TargetBackend.lca_laws tree_machine) branchedSource prepared
    ((TargetBackend.lca_laws tree_machine).prepare branchedSource)]
  decide

theorem deep_machine : TargetBackend.Config 17 16 := by constructor <;> decide

def changedInput : Input 17 :=
  ((TreeReduction.reduction 9).convert ⟨.attach (chain 7) .singleton,rfl⟩).1.2

example : ¬ TargetBackend.Valid deep_machine changedInput
    ((TargetBackend.ops deep_machine).prepare deepInput).1 := by
  apply TargetBackend.stale_rejected deep_machine deepInput changedInput (7,8)
  decide

example : ((TargetBackend.ops deep_machine).answer
    ((TargetBackend.ops deep_machine).prepare deepInput).1 (15,16)).1 = 16 := by
  rw [(TargetBackend.reusable deep_machine deepInput _).1]
  decide

example : ((TargetBackend.storage deep_machine).retained
    ((TargetBackend.ops deep_machine).prepare deepInput).1) = 512*17 := by
  simp [TargetBackend.storage]

example : ¬ TargetBackend.Config 17 14 := by
  intro h
  have hh := h.addresses
  norm_num at hh

example : Feasible (TargetBackend.realtime 17) (TargetBackend.profile 17) deepInput :=
  TargetBackend.realtime_feasible deepInput

example : ¬ Feasible {TargetBackend.realtime 17 with startup := some 0}
    (TargetBackend.profile 17) deepInput := by decide

end Examples.LCATarget

import Applications.Sequences.LCA.Catalog
import Examples.LCATree

set_option autoImplicit false
set_option warningAsError true

namespace Examples.LCABackend
open Resources.Prepared Sequences.LCA TreeReduction Backend

def branchedSource : Source 4 := ⟨LCATree.branched,rfl⟩
def prepared := ((lcaOps 4).prepare branchedSource).1

-- The executable composed backend handles siblings, ancestors, and reversed
-- vertex order. Its universal law uses independently defined tree ancestry.
example : ((lcaOps 4).answer prepared (⟨2,by decide⟩,⟨3,by decide⟩)).1 = 0 := by decide
example : ((lcaOps 4).answer prepared (⟨1,by decide⟩,⟨2,by decide⟩)).1 = 1 := by decide
example : ((lcaOps 4).answer prepared (⟨2,by decide⟩,⟨1,by decide⟩)).1 = 1 := by decide
example (q : Query 4) : ((lcaOps 4).answer prepared q).1 = sourceLCA branchedSource q :=
  agreement (lca_laws 4) branchedSource q
example (q : Query 4) : ((lcaOps 4).answer prepared q).2 ≤ 62 := lca_answer_cost prepared q

def chain : Nat → Tree
  | 0 => .singleton
  | k+1 => .attach .singleton (chain k)
theorem chain_size (k : Nat) : (chain k).size = k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [chain, Tree.size, ih]; omega

def deepSource : Source 9 := ⟨chain 8,chain_size 8⟩
def deepInput : Input 17 := ((TreeReduction.reduction 9).convert deepSource).1.2
def deepPrepared := ((ops 17).prepare deepInput).1

-- Two-cell blocks, nine blocks, and a short final block exercise shape
-- sharing, a macro middle range, duplicate minima, and upward padding.
example : blockSize 17 = 2 := by decide
example : PreparationBounds.blocks 17 = 9 := by decide
example : (sourceM deepInput 17).1 = 1 := by decide
example : (sourceM deepInput 17).2 = 8 := by decide
example : ((ops 17).answer deepPrepared (3,13)).1 = 3 := by decide
example : ((ops 17).answer deepPrepared (15,16)).1 = 16 := by decide
example : ((ops 17).answer deepPrepared (16,15)).1 = 0 := by decide
example : ((ops 17).answer deepPrepared (0,17)).1 = 0 := by decide
example : ((ops 17).answer deepPrepared (0,17)).2 = 3 := by decide
example (q : Nat × Nat) : ((ops 17).answer deepPrepared q).1 = spec deepInput q :=
  agreement (laws 17) deepInput q

-- Distinct static trees cannot share an arbitrary prepared state merely
-- because their sizes match.
example : ¬ Valid deepInput ((ops 17).prepare
    ((TreeReduction.reduction 9).convert ⟨.attach (chain 7) .singleton, rfl⟩).1.2).1 := by
  intro h
  have he := congrArg (fun r : State 17 => r.micro.depths[8]) h
  revert he
  decide

set_option maxRecDepth 4096 in
example : (Catalog.directAnswer deepInput (0,16)).1 = 0 := by decide
set_option maxRecDepth 4096 in
example : (Catalog.directAnswer deepInput (0,16)).2 = 173 := by decide
example (q : Nat × Nat) :
    (Catalog.directAnswer deepInput q).1 = ((ops 17).answer deepPrepared q).1 := by
  exact (agreement (Catalog.direct_laws 17) deepInput q).trans
    (agreement (laws 17) deepInput q).symm

def immediateStartup : Requirements where
  startup := some 0
  deadline := 183
  maintenance := 0
  capacity := 34
  peak := 46

example : Feasible immediateStartup (Catalog.directProfile 17) deepInput := by decide
example : ¬ Feasible {immediateStartup with deadline := 57}
    (Catalog.directProfile 17) deepInput := by decide
example : ¬ Feasible {immediateStartup with peak := 34}
    (Catalog.directProfile 17) deepInput := by decide

end Examples.LCABackend

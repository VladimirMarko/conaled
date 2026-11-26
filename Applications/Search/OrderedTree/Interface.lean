import Applications.Search.AbstractSet
import Applications.Search.OrderedTree.Candidate

/-!
# Ordered-tree realizations of the abstract set laws

Baseline and candidate/abort operators implement the same finite set content.
Their comparison measures and allocated-cell models remain separate contracts.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedTree
universe u
variable {α : Type u} [LinearOrder α]

def baselineOps : AbstractSet.Ops α (BinaryTree α) where
  empty := .nil
  insert := insert
  member := member

def candidateOps : AbstractSet.Ops α (BinaryTree α) where
  empty := .nil
  insert := insertCandidate
  member := memberCandidate

theorem baseline_laws : AbstractSet.Laws (baselineOps : AbstractSet.Ops α (BinaryTree α))
    (fun t x => Contains x t) Ordered where
  empty_valid := ordered_nil
  empty _ := id
  insert_valid x _ h := ordered_insert h x
  insert x t _ z := contains_insert x z t
  member x _ h := member_correct h x

theorem candidate_laws : AbstractSet.Laws (candidateOps : AbstractSet.Ops α (BinaryTree α))
    (fun t x => Contains x t) Ordered where
  empty_valid := ordered_nil
  empty _ := id
  insert_valid x _ h := (insertCandidate_correct h x).1
  insert x _ h z := (insertCandidate_correct h x).2.1 z
  member x _ h := memberCandidate_correct h x

end Search.OrderedTree

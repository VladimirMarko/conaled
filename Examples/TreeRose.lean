import Applications.Trees.Rose

/-! A mirror example that changes both the root's child order and a descendant's
child order. The universal involution theorem is consumed on this nested tree.
-/
set_option autoImplicit false
set_option warningAsError true

namespace TreeRoseExamples
open Trees

def sample : Rose Nat :=
  .node 9
    [.node 3 [.node 1 [], .node 2 []],
      .node 7 [.node 6 [.node 5 []]], .node 8 []]

theorem sample_mirror :
    Rose.mirror sample =
      .node 9 [.node 8 [], .node 7 [.node 6 [.node 5 []]],
        .node 3 [.node 2 [], .node 1 []]] := by
  simp [sample]

theorem sample_mirror_mirror : Rose.mirror (Rose.mirror sample) = sample :=
  Rose.mirror_mirror sample

/-- Equal labels do not collapse separate child occurrences. -/
def repeated : Rose Nat := .node 5 [.node 5 [], .node 5 []]

theorem repeated_mirror : Rose.mirror repeated = .node 5 [.node 5 [], .node 5 []] := by
  simp [repeated]

theorem repeated_mirror_mirror : Rose.mirror (Rose.mirror repeated) = repeated :=
  Rose.mirror_mirror repeated

end TreeRoseExamples

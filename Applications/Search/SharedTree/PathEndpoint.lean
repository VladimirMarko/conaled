import Applications.Search.SharedTree.Path

/-!
# Continuing a path below its endpoint

An equality of endpoint observations extends to every further path in the
same heap. This includes failure after traversing beyond an empty root.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.SharedTree
variable {α : Type}

theorem follow_append (heap : Durability.Heap (Cell α))
    (path suffix : List Branch) (root : Root) :
    follow heap (path ++ suffix) root =
      (follow heap path root).bind (follow heap suffix) := by
  induction path generalizing root with
  | nil => rfl
  | cons direction path ih =>
      simp only [List.cons_append, follow, ih, Option.bind_assoc]

theorem follow_descendants {heap : Durability.Heap (Cell α)}
    {path : List Branch} {oldRoot newRoot : Root}
    (endpoint : follow heap path newRoot = follow heap path oldRoot)
    (suffix : List Branch) :
    follow heap (path ++ suffix) newRoot = follow heap (path ++ suffix) oldRoot := by
  rw [follow_append, follow_append, endpoint]

end Search.SharedTree

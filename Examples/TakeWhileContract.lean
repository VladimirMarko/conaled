import Applications.Resources.ListFusion

/-! Independent native measured-pair fixtures, frozen before the #469 theorem layer.
These run existing executors; the importing examples connect them to general laws. -/

namespace Resources.TakeWhileContract

example : ListFusion.takeWhile 1 1 1 id (List.replicate 5 false) = ([], 2) := by decide
example : ListFusion.takeWhile 1 1 1 id (List.replicate 5 true) =
    (List.replicate 5 true, 16) := by decide

example : bind (ListFusion.takeWhile 1 1 1 (fun n : Nat => n < 3) [1, 2, 9, 4])
    (ListExecution.foldr 1 List.cons []) = ([1, 2], 13) := by decide
example : bind (ListFusion.takeWhile 1 1 1 (fun n : Nat => n < 3) [1, 2])
    (ListExecution.foldr 1 List.cons []) = ([1, 2], 12) := by decide
example : bind (ListFusion.takeWhile 1 1 1 (fun n : Nat => n < 3) [])
    (ListExecution.foldr 1 List.cons []) = ([], 2) := by decide
example : bind (ListFusion.takeWhile 1 1 1 (fun n : Nat => n < 3) [9, 1, 2])
    (ListExecution.foldr 1 List.cons []) = ([], 3) := by decide

end Resources.TakeWhileContract

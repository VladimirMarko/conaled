import Applications.Sequences.OrderedSummary

/-! Ordinary clients of ordered summaries. No internal-language model is imported. -/
namespace Examples.OrderedSummary
open Sequences.OrderedSummary

def left : List (Nat × Bool) := [(3,true), (3,true)]
def right : List (Nat × Bool) := [(5,false)]

example : listValid diagnosticMeasure (appendCache List.append
    (cache id diagnosticMeasure left) (cache id diagnosticMeasure right)) :=
  list_append _ (cache_valid _ _ _ trivial) (cache_valid _ _ _ trivial)

example : dlistValid diagnosticMeasure (appendCache (· ++ ·)
    (cache Batteries.DList.toList diagnosticMeasure (Batteries.DList.ofList left))
    (cache Batteries.DList.toList diagnosticMeasure (Batteries.DList.ofList right))) :=
  dlist_append _ (cache_valid _ _ _ trivial) (cache_valid _ _ _ trivial)

example : listValid diagnosticMeasure ([], 1) := list_empty _
example : dlistValid diagnosticMeasure (Batteries.DList.empty, 1) := dlist_empty _

/-- The cache observer uses its relational square after actual append preservation. -/
example : (summarySquare (fun (_ : List (Nat × Bool)) => True) id diagnosticMeasure).impl
    (appendCache List.append (cache id diagnosticMeasure left)
      (cache id diagnosticMeasure right)) =
      (Multiplicative.ofAdd 3, FreeMonoid.ofList [true,true,false]) := by
  have h := list_append diagnosticMeasure
    (cache_valid (fun _ => True) id diagnosticMeasure (r := left) trivial)
    (cache_valid (fun _ => True) id diagnosticMeasure (r := right) trivial)
  have obs := (summarySquare (fun (_ : List (Nat × Bool)) => True) id diagnosticMeasure).preserves
    (show (representation (fun (_ : List (Nat × Bool)) => True) id diagnosticMeasure).Rel
      (appendCache List.append (cache id diagnosticMeasure left)
        (cache id diagnosticMeasure right)) (left ++ right) from ⟨h.1, rfl, h.2⟩)
  exact obs.trans (diagnostic_value (left ++ right))

example : summary diagnosticMeasure
    (Batteries.DList.toList ((left ++ right).foldl Batteries.DList.push .empty)) =
      (left ++ right).foldl (fun m a => m * diagnosticMeasure a) 1 := dlist_batch _ _

example : summary diagnosticMeasure
    ((left ++ right).foldl (fun r a => r ++ [a]) []) =
      (left ++ right).foldl (fun m a => m * diagnosticMeasure a) 1 := list_batch _ _

example : summary lengthMeasure [false,true,true] = Multiplicative.ofAdd 3 := summary_length _

example : ¬ listValid diagnosticMeasure
    ([(3,true)], (Multiplicative.ofAdd 1, FreeMonoid.ofList [false])) := by
  intro h
  have bad := h.2
  change (Multiplicative.ofAdd 1, FreeMonoid.ofList [false]) = diagnostic [(3,true)] at bad
  rw [diagnostic_value] at bad
  exact Bool.noConfusion (congrArg (fun p : Diagnostic => p.2.toList.head!) bad)

example : diagnostic [(3,true),(5,false)] ≠ diagnostic [(5,false),(3,true)] := by
  rw [diagnostic_value, diagnostic_value]
  intro h
  exact Bool.noConfusion (congrArg (fun p : Diagnostic => p.2.toList.head!) h)

example : summary lengthMeasure [false] = summary lengthMeasure [true] ∧
    ([false] : List Bool) ≠ [true] := by simp [lengthMeasure]

example (s : Sequences.Symmetric.SymList Bool) (h : Sequences.Symmetric.Inv s) :
    ((Sequences.Symmetric.prefixLengths (α := Bool)).impl s).down =
      List.range ((summary lengthMeasure (Sequences.Symmetric.fromSL s)).toAdd + 1) :=
  symmetric_prefix_summary s h

example : Batteries.DList.toList
    ((left ++ right).foldl Batteries.DList.push .empty) = [(3,true),(3,true),(5,false)] :=
  dlist_batch_decode _

example : (left ++ right).foldl (fun r a => r ++ [a]) [] = [(3,true),(3,true),(5,false)] :=
  list_batch_decode _

end Examples.OrderedSummary

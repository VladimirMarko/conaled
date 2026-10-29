import Applications.Sequences.OrderedSummary
namespace AuthorA.DirectA
open Sequences.OrderedSummary
variable {A M : Type} [Monoid M]
theorem decode_acc (xs : List A) (r : Batteries.DList A) :
    (xs.foldl Batteries.DList.push r).toList = r.toList ++ xs := by
  induction xs generalizing r with
  | nil => simp
  | cons a xs ih =>
    simpa [List.foldl_cons, Batteries.DList.toList_push, List.append_assoc] using
      ih (r.push a)
theorem decode (xs : List A) :
    (xs.foldl Batteries.DList.push .empty).toList = xs := by
  simpa using decode_acc xs .empty
theorem summary_acc (measure : A → M) (xs : List A) (r : Batteries.DList A) :
    summary measure (xs.foldl Batteries.DList.push r).toList =
      xs.foldl (fun m a => m * measure a) (summary measure r.toList) := by
  induction xs generalizing r with
  | nil => rfl
  | cons a xs ih =>
    simpa [List.foldl_cons, Batteries.DList.toList_push] using ih (r.push a)
theorem ordered (measure : A → M) (xs : List A) :
    summary measure (xs.foldl Batteries.DList.push .empty).toList =
      xs.foldl (fun m a => m * measure a) 1 := by
  simpa using summary_acc measure xs .empty
example : (([] : List Bool).foldl Batteries.DList.push .empty).toList = [] := decode []
example : ([true,false].foldl Batteries.DList.push .empty).toList = [true,false] := decode _
example : summary FreeMonoid.of (([] : List Bool).foldl Batteries.DList.push .empty).toList = 1 := ordered _ _
example : summary FreeMonoid.of ([true,false].foldl Batteries.DList.push .empty).toList =
    FreeMonoid.ofList [true,false] := by rw [ordered]; rfl
example : ([true,false] : List Bool).length = [false,true].length ∧
    ([true,false] : List Bool) ≠ [false,true] := by decide
example : summary FreeMonoid.of ([true,false].foldl Batteries.DList.push .empty).toList ≠
    summary FreeMonoid.of ([false,true].foldl Batteries.DList.push .empty).toList := by
  rw [ordered, ordered]
  intro h
  exact Bool.noConfusion (congrArg (fun w : FreeMonoid Bool => w.toList.head!) h)
end AuthorA.DirectA

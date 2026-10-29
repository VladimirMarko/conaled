import Applications.Sequences.OrderedSummary
namespace AuthorA.SharedA
open Sequences.OrderedSummary
variable {A M : Type} [Monoid M]
theorem decode (xs : List A) :
    (xs.foldl Batteries.DList.push .empty).toList = xs := dlist_batch_decode xs
theorem ordered (measure : A → M) (xs : List A) :
    summary measure (xs.foldl Batteries.DList.push .empty).toList =
      xs.foldl (fun m a => m * measure a) 1 := dlist_batch measure xs
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
end AuthorA.SharedA

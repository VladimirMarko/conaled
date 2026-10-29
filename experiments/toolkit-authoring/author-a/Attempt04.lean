import Applications.Sequences.OrderedSummary
namespace AuthorA.DirectB
open Sequences.OrderedSummary
variable {A M : Type} [Monoid M]
def decode (r : List A) : List A := r.reverse
def push (r : List A) (a : A) : List A := a :: r
def append (x y : List A) : List A := y ++ x
def valid (measure : A → M) (c : List A × M) : Prop :=
  c.2 = summary measure (decode c.1)
def appendC (x y : List A × M) : List A × M := (append x.1 y.1, x.2 * y.2)
theorem empty (measure : A → M) : valid measure ([], 1) := by
  simp [valid, decode]
theorem append_valid (measure : A → M) (x y : List A × M)
    (hx : valid measure x) (hy : valid measure y) : valid measure (appendC x y) := by
  change x.2 * y.2 = summary measure ((y.1 ++ x.1).reverse)
  rw [List.reverse_append, summary_append]
  exact congrArg₂ (· * ·) hx hy
theorem decode_acc (xs r : List A) : decode (xs.foldl push r) = decode r ++ xs := by
  induction xs generalizing r with
  | nil => simp
  | cons a xs ih =>
    simpa [List.foldl_cons, decode, push, List.reverse_cons, List.append_assoc] using
      ih (push r a)
theorem batch (xs : List A) : decode (xs.foldl push []) = xs := by
  simpa [decode] using decode_acc xs []
theorem summary_acc (measure : A → M) (xs r : List A) :
    summary measure (decode (xs.foldl push r)) =
      xs.foldl (fun m a => m * measure a) (summary measure (decode r)) := by
  induction xs generalizing r with
  | nil => rfl
  | cons a xs ih =>
    simpa [List.foldl_cons, decode, push, List.reverse_cons] using ih (push r a)
theorem ordered (measure : A → M) (xs : List A) :
    summary measure (decode (xs.foldl push [])) = xs.foldl (fun m a => m * measure a) 1 := by
  simpa [decode] using summary_acc measure xs []
example : decode (([] : List Bool).foldl push []) = [] := batch []
example : decode ([true,false].foldl push []) = [true,false] := batch _
example : summary FreeMonoid.of (decode (([] : List Bool).foldl push [])) = 1 := ordered _ _
example : summary FreeMonoid.of (decode ([true,false].foldl push [])) =
    FreeMonoid.ofList [true,false] := by rw [ordered]; rfl
example : valid (FreeMonoid.of : Bool → FreeMonoid Bool) ([], 1) := empty _
example : valid FreeMonoid.of
    (appendC ([true], FreeMonoid.of true) ([false], FreeMonoid.of false)) := by
  apply append_valid
  · simp [valid, decode]
  · simp [valid, decode]
example : ¬ valid FreeMonoid.of ([false,true], FreeMonoid.ofList [false,true]) := by
  intro h
  change FreeMonoid.ofList [false,true] = summary FreeMonoid.of [true,false] at h
  change FreeMonoid.ofList [false,true] = FreeMonoid.ofList [true,false] at h
  exact Bool.noConfusion (congrArg (fun w : FreeMonoid Bool => w.toList.head!) h)
example : ([true,false] : List Bool).length = [false,true].length ∧
    ([true,false] : List Bool) ≠ [false,true] := by decide
example : summary FreeMonoid.of (decode ([true,false].foldl push [])) ≠
    summary FreeMonoid.of (decode ([false,true].foldl push [])) := by
  rw [ordered, ordered]
  intro h
  exact Bool.noConfusion (congrArg (fun w : FreeMonoid Bool => w.toList.head!) h)
end AuthorA.DirectB

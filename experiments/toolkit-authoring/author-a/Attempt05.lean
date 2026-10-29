import Applications.Sequences.OrderedSummary
namespace AuthorA.SharedB
open Sequences.OrderedSummary
variable {A M : Type} [Monoid M]
def decode (r : List A) : List A := r.reverse
def push (r : List A) (a : A) : List A := a :: r
def append (x y : List A) : List A := y ++ x
def valid (measure : A → M) (c : List A × M) : Prop :=
  c.2 = summary measure (decode c.1)
def appendC (x y : List A × M) : List A × M := (append x.1 y.1, x.2 * y.2)
theorem empty_law : decode ([] : List A) = [] := rfl
theorem push_law (r : List A) (a : A) : decode (push r a) = decode r ++ [a] := by
  simp [decode, push]
theorem append_law (x y : List A) : decode (append x y) = decode x ++ decode y := by
  simp [decode, append]
theorem valid_iff (measure : A → M) (c : List A × M) :
    valid measure c ↔ Valid (fun (_ : List A) => True) decode measure c := by
  simp [valid, Valid]
theorem empty (measure : A → M) : valid measure ([], 1) :=
  (valid_iff measure _).mpr (empty_valid _ _ _ _ trivial empty_law)
theorem append_valid (measure : A → M) (x y : List A × M)
    (hx : valid measure x) (hy : valid measure y) : valid measure (appendC x y) := by
  apply (valid_iff measure _).mpr
  exact Sequences.OrderedSummary.append_valid _ _ _ append
    (fun _ _ _ _ => trivial) (fun x y _ _ => append_law x y)
    ((valid_iff measure x).mp hx) ((valid_iff measure y).mp hy)
theorem batch (xs : List A) : decode (xs.foldl push []) = xs := by
  simpa [empty_law] using batch_decode decode (fun _ => True) push [] trivial
    (fun _ _ _ => trivial) (fun r a _ => push_law r a) xs
theorem ordered (measure : A → M) (xs : List A) :
    summary measure (decode (xs.foldl push [])) = xs.foldl (fun m a => m * measure a) 1 := by
  simpa [empty_law] using batch_summary decode (fun _ => True) measure push [] trivial
    (fun _ _ _ => trivial) (fun r a _ => push_law r a) xs
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
end AuthorA.SharedB

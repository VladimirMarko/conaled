import Applications.Sequences.OrderedSummary
namespace TrialB
open Sequences.OrderedSummary
universe u v
variable {A : Type u} {M : Type v} [Monoid M]
def decode (r : List A) := r.reverse
def push (r : List A) (a : A) := a :: r
def append (x y : List A) := y ++ x
def valid (measure : A → M) (c : List A × M) := c.2 = summary measure (decode c.1)
def appendC (x y : List A × M) : List A × M := (append x.1 y.1, x.2 * y.2)
namespace BShared
 theorem empty (measure : A → M) : valid measure ([], 1) := by
  exact (empty_valid (fun _ => True) decode measure [] trivial rfl).2
 theorem append_valid' (measure : A → M) {x y : List A × M}
    (hx : valid measure x) (hy : valid measure y) : valid measure (appendC x y) := by
  have h := append_valid (fun _ => True) decode measure append
    (fun _ _ _ _ => trivial)
    (fun x y _ _ => by simp [decode, append, List.reverse_append])
    (x := x) (y := y) ⟨trivial, hx⟩ ⟨trivial, hy⟩
  exact h.2
 theorem batch_full (xs : List A) : decode (xs.foldl push []) = xs := by
  simpa [decode] using batch_decode decode (fun _ => True) push [] trivial
    (fun _ _ _ => trivial) (fun r a _ => by simp [decode, push]) xs
 theorem batch_ordered (measure : A → M) (xs : List A) :
    summary measure (decode (xs.foldl push [])) = xs.foldl (fun m a => m * measure a) 1 := by
  simpa [decode] using batch_summary decode (fun _ => True) measure push [] trivial
    (fun _ _ _ => trivial) (fun r a _ => by simp [decode, push]) xs
 example : decode (([] : List Bool).foldl push []) = [] := batch_full _
 example : decode ([true, false].foldl push []) = [true, false] := batch_full _
 example : summary FreeMonoid.of (decode (([] : List Bool).foldl push [])) =
    (1 : FreeMonoid Bool) := batch_ordered _ _
 example : summary FreeMonoid.of (decode ([true, false].foldl push [])) =
    FreeMonoid.ofList [true, false] := by
  rw [batch_ordered]; rfl
 example : valid FreeMonoid.of (([] : List Bool), (1 : FreeMonoid Bool)) := empty _
 example : valid FreeMonoid.of (appendC ([true], FreeMonoid.of true) ([false], FreeMonoid.of false)) := by
  apply append_valid' <;> simp [valid, decode]
 example : ¬ valid FreeMonoid.of ([true], FreeMonoid.of false) := by
  intro h
  have h' : FreeMonoid.of false = FreeMonoid.of true := h
  have h'' := congrArg FreeMonoid.toList h'
  contradiction
 example : ([true,false] : List Bool).length = [false,true].length ∧
    ([true,false] : List Bool) ≠ [false,true] := by decide
 example : summary FreeMonoid.of [true,false] ≠ summary FreeMonoid.of [false,true] := by
  change FreeMonoid.ofList [true,false] ≠ FreeMonoid.ofList [false,true]
  intro h
  have := congrArg FreeMonoid.toList h
  contradiction
end BShared
namespace BDirect
 theorem empty (measure : A → M) : valid measure ([], 1) := by
  simp [valid, decode]
 theorem append_valid' (measure : A → M) {x y : List A × M}
    (hx : valid measure x) (hy : valid measure y) : valid measure (appendC x y) := by
  change x.2 * y.2 = summary measure (decode (append x.1 y.1))
  simp only [decode, append, List.reverse_append, summary_append]
  exact congrArg₂ (· * ·) hx hy
 theorem batch_full_seed (xs : List A) (r : List A) :
    decode (xs.foldl push r) = decode r ++ xs := by
  induction xs generalizing r with
  | nil => simp
  | cons a xs ih =>
    simpa [List.foldl_cons, push, decode, List.append_assoc] using ih (push r a)
 theorem batch_full (xs : List A) : decode (xs.foldl push []) = xs := by
  simpa [decode] using batch_full_seed xs []
 theorem batch_ordered_seed (measure : A → M) (xs : List A) (r : List A) :
    summary measure (decode (xs.foldl push r)) =
      xs.foldl (fun m a => m * measure a) (summary measure (decode r)) := by
  induction xs generalizing r with
  | nil => rfl
  | cons a xs ih =>
    simpa [List.foldl_cons, push, decode, summary_append] using ih (push r a)
 theorem batch_ordered (measure : A → M) (xs : List A) :
    summary measure (decode (xs.foldl push [])) = xs.foldl (fun m a => m * measure a) 1 := by
  simpa [decode] using batch_ordered_seed measure xs []
 example : decode (([] : List Bool).foldl push []) = [] := batch_full _
 example : decode ([true, false].foldl push []) = [true, false] := batch_full _
 example : summary FreeMonoid.of (decode (([] : List Bool).foldl push [])) =
    (1 : FreeMonoid Bool) := batch_ordered _ _
 example : summary FreeMonoid.of (decode ([true, false].foldl push [])) =
    FreeMonoid.ofList [true, false] := by
  rw [batch_ordered]; rfl
 example : valid FreeMonoid.of (([] : List Bool), (1 : FreeMonoid Bool)) := empty _
 example : valid FreeMonoid.of (appendC ([true], FreeMonoid.of true) ([false], FreeMonoid.of false)) := by
  apply append_valid' <;> simp [valid, decode]
 example : ¬ valid FreeMonoid.of ([true], FreeMonoid.of false) := by
  intro h
  have h' : FreeMonoid.of false = FreeMonoid.of true := h
  have h'' := congrArg FreeMonoid.toList h'
  contradiction
 example : ([true,false] : List Bool).length = [false,true].length ∧
    ([true,false] : List Bool) ≠ [false,true] := by decide
 example : summary FreeMonoid.of [true,false] ≠ summary FreeMonoid.of [false,true] := by
  change FreeMonoid.ofList [true,false] ≠ FreeMonoid.ofList [false,true]
  intro h
  have := congrArg FreeMonoid.toList h
  contradiction
end BDirect
namespace AShared
 theorem batch_full (xs : List A) :
    Batteries.DList.toList (xs.foldl Batteries.DList.push .empty) = xs :=
  dlist_batch_decode xs
 theorem batch_ordered (measure : A → M) (xs : List A) :
    summary measure (Batteries.DList.toList (xs.foldl Batteries.DList.push .empty)) =
      xs.foldl (fun m a => m * measure a) 1 := dlist_batch measure xs
 example : Batteries.DList.toList (([] : List Bool).foldl Batteries.DList.push .empty) = [] :=
  batch_full _
 example : Batteries.DList.toList ([true,false].foldl Batteries.DList.push .empty) = [true,false] :=
  batch_full _
 example : summary FreeMonoid.of
    (Batteries.DList.toList (([] : List Bool).foldl Batteries.DList.push .empty)) =
      (1 : FreeMonoid Bool) := batch_ordered _ _
 example : summary FreeMonoid.of
    (Batteries.DList.toList ([true,false].foldl Batteries.DList.push .empty)) =
      FreeMonoid.ofList [true,false] := by
  rw [batch_ordered]; rfl
 example : ([true,false] : List Bool).length = [false,true].length ∧
    ([true,false] : List Bool) ≠ [false,true] := by decide
 example : summary FreeMonoid.of [true,false] ≠ summary FreeMonoid.of [false,true] := by
  change FreeMonoid.ofList [true,false] ≠ FreeMonoid.ofList [false,true]
  intro h
  have := congrArg FreeMonoid.toList h
  contradiction
end AShared
end TrialB

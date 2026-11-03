import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.TypeTags.Basic
import Batteries.Data.DList.Lemmas
import SquareKit.Relations
import SquareKit.ListFusion
import Applications.Sequences.Symmetric.Observation

/-! Ordered summaries and optional caches (#185). Ordinary callers supply only
operations and their observation laws. These are semantic results, with no
allocation, materialization-time or bounded-storage claim. -/
namespace Sequences.OrderedSummary
universe u v w
variable {A : Type u} {M : Type v} [Monoid M]

/-- The free-monoid extension retains multiplication order. -/
def summary (measure : A → M) (xs : List A) : M :=
  FreeMonoid.lift measure (FreeMonoid.ofList xs)

@[simp] theorem summary_nil (measure : A → M) : summary measure [] = 1 :=
  (FreeMonoid.lift measure).map_one

@[simp] theorem summary_append (measure : A → M) (xs ys : List A) :
    summary measure (xs ++ ys) = summary measure xs * summary measure ys :=
  (FreeMonoid.lift measure).map_mul _ _

@[simp] theorem summary_singleton (measure : A → M) (a : A) :
    summary measure [a] = measure a := FreeMonoid.lift_eval_of _ _

/-- Representation validity and agreement with the optional cache are separate. -/
def Valid {R : Type w} (Inv : R → Prop) (decode : R → List A)
    (measure : A → M) (c : R × M) : Prop :=
  Inv c.1 ∧ c.2 = summary measure (decode c.1)

def cache {R : Type w} (decode : R → List A) (measure : A → M) (r : R) : R × M :=
  (r, summary measure (decode r))

theorem cache_valid {R : Type w} (Inv : R → Prop) (decode : R → List A)
    (measure : A → M) {r : R} (h : Inv r) : Valid Inv decode measure (cache decode measure r) :=
  ⟨h, rfl⟩

def appendCache {R : Type w} (append : R → R → R) (x y : R × M) : R × M :=
  (append x.1 y.1, x.2 * y.2)

theorem empty_valid {R : Type w} (Inv : R → Prop) (decode : R → List A)
    (measure : A → M) (empty : R) (valid : Inv empty) (observes : decode empty = []) :
    Valid Inv decode measure (empty, 1) := by
  exact ⟨valid, by simp [observes]⟩

/-- Only valid inputs need satisfy the representation's append laws. -/
theorem append_valid {R : Type w} (Inv : R → Prop) (decode : R → List A)
    (measure : A → M) (append : R → R → R)
    (closed : ∀ x y, Inv x → Inv y → Inv (append x y))
    (observes : ∀ x y, Inv x → Inv y → decode (append x y) = decode x ++ decode y)
    {x y : R × M} (hx : Valid Inv decode measure x) (hy : Valid Inv decode measure y) :
    Valid Inv decode measure (appendCache append x y) := by
  refine ⟨closed _ _ hx.1 hy.1, ?_⟩
  change x.2 * y.2 = summary measure (decode (append x.1 y.1))
  rw [observes _ _ hx.1 hy.1, summary_append, hx.2, hy.2]

/-- Observe full sequences before applying a possibly lossy summary. -/
def representation {A M R : Type u} [Monoid M] (Inv : R → Prop)
    (decode : R → List A) (measure : A → M) : Relational.RelRep where
  R := R × M
  S := List A
  Rel c xs := Inv c.1 ∧ decode c.1 = xs ∧ c.2 = summary measure xs

def summarySquare {A M R : Type u} [Monoid M] (Inv : R → Prop)
    (decode : R → List A) (measure : A → M) :
    Relational.RelSquare (representation Inv decode measure) ⟨M, M, Eq⟩ where
  impl := Prod.snd
  spec := summary measure
  preserves h := h.2.2

/-- Batch clients reuse reachable fusion, without learning a container class. -/
theorem batch_summary {R : Type w} (decode : R → List A) (Inv : R → Prop)
    (measure : A → M) (push : R → A → R) (seed : R) (initial : Inv seed)
    (closed : ∀ r a, Inv r → Inv (push r a))
    (observes : ∀ r a, Inv r → decode (push r a) = decode r ++ [a])
    (xs : List A) :
    summary measure (decode (xs.foldl push seed)) =
      xs.foldl (fun m a => m * measure a) (summary measure (decode seed)) := by
  apply SquareKit.ListFusion.foldl_reachable push (fun m a => m * measure a)
    (fun r => summary measure (decode r)) Inv seed initial closed
  intro r a hr
  simp [observes r a hr]

/-- Full sequence fusion is independent of the chosen summary observation. -/
theorem batch_decode {R : Type w} (decode : R → List A) (Inv : R → Prop)
    (push : R → A → R) (seed : R) (initial : Inv seed)
    (closed : ∀ r a, Inv r → Inv (push r a))
    (observes : ∀ r a, Inv r → decode (push r a) = decode r ++ [a])
    (xs : List A) : decode (xs.foldl push seed) = decode seed ++ xs := by
  have fusion := SquareKit.ListFusion.foldl_reachable push
    (fun ys a => ys ++ [a]) decode Inv seed initial closed observes xs
  rw [fusion]
  clear fusion
  generalize decode seed = ys
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih => simpa [List.foldl_cons, List.append_assoc] using ih (ys ++ [a])

theorem list_batch_decode (xs : List A) : xs.foldl (fun r a => r ++ [a]) [] = xs := by
  simpa using batch_decode id (fun _ => True) (fun r a => r ++ [a]) [] trivial
    (fun _ _ _ => trivial) (fun _ _ _ => rfl) xs

theorem dlist_batch_decode (xs : List A) :
    Batteries.DList.toList (xs.foldl Batteries.DList.push .empty) = xs := by
  simpa [Batteries.DList.toList_empty] using
    batch_decode Batteries.DList.toList (fun _ => True) Batteries.DList.push .empty trivial
      (fun _ _ _ => trivial) (fun r a _ => Batteries.DList.toList_push a r) xs

abbrev listValid (measure : A → M) := Valid (fun (_ : List A) => True) id measure
abbrev dlistValid (measure : A → M) :=
  Valid (fun (_ : Batteries.DList A) => True) Batteries.DList.toList measure

theorem list_empty (measure : A → M) : listValid measure ([], 1) :=
  empty_valid _ _ _ _ trivial rfl

theorem list_append (measure : A → M) {x y : List A × M}
    (hx : listValid measure x) (hy : listValid measure y) :
    listValid measure (appendCache List.append x y) :=
  append_valid _ _ _ _ (fun _ _ _ _ => trivial) (fun _ _ _ _ => rfl) hx hy

theorem dlist_empty (measure : A → M) :
    dlistValid measure (Batteries.DList.empty, 1) :=
  empty_valid _ _ _ _ trivial Batteries.DList.toList_empty

theorem dlist_append (measure : A → M) {x y : Batteries.DList A × M}
    (hx : dlistValid measure x) (hy : dlistValid measure y) :
    dlistValid measure (appendCache (· ++ ·) x y) :=
  append_valid _ _ _ _ (fun _ _ _ _ => trivial)
    (fun _ _ _ _ => Batteries.DList.toList_append _ _) hx hy

theorem list_batch (measure : A → M) (xs : List A) :
    summary measure (xs.foldl (fun r a => r ++ [a]) []) =
      xs.foldl (fun m a => m * measure a) 1 := by
  simpa using batch_summary id (fun _ => True) measure (fun r a => r ++ [a]) []
    trivial (fun _ _ _ => trivial) (fun _ _ _ => rfl) xs

theorem dlist_batch (measure : A → M) (xs : List A) :
    summary measure (Batteries.DList.toList (xs.foldl Batteries.DList.push .empty)) =
      xs.foldl (fun m a => m * measure a) 1 := by
  simpa [Batteries.DList.toList_empty] using
    batch_summary Batteries.DList.toList (fun _ => True) measure Batteries.DList.push
      .empty trivial (fun _ _ _ => trivial) (fun r a _ => Batteries.DList.toList_push a r) xs

/-- Additive length is represented by the existing multiplicative wrapper. -/
def lengthMeasure (_ : A) : Multiplicative Nat := Multiplicative.ofAdd 1

@[simp] theorem summary_length (xs : List A) :
    summary lengthMeasure xs = Multiplicative.ofAdd xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change summary lengthMeasure ([a] ++ xs) = _
    rw [summary_append, summary_singleton, ih]
    change 1 + xs.length = (a :: xs).length
    simp [Nat.add_comm]

/-- Compose the existing prefix observation with the shared length summary. -/
theorem symmetric_prefix_summary (s : Symmetric.SymList A) (h : Symmetric.Inv s) :
    ((Symmetric.prefixLengths (α := A)).impl s).down =
      List.range ((summary lengthMeasure (Symmetric.fromSL s)).toAdd + 1) := by
  rw [summary_length]
  simpa [Symmetric.length_fromSL] using Symmetric.prefixLengths_correct s h

/-- The diagnostic summary keeps both length and the ordered word of labels. -/
abbrev Diagnostic := Multiplicative Nat × FreeMonoid Bool

def diagnosticMeasure (a : Nat × Bool) : Diagnostic :=
  (Multiplicative.ofAdd 1, FreeMonoid.of a.2)

def diagnostic (xs : List (Nat × Bool)) : Diagnostic := summary diagnosticMeasure xs

@[simp] theorem diagnostic_value (xs : List (Nat × Bool)) :
    diagnostic xs = (Multiplicative.ofAdd xs.length, FreeMonoid.ofList (xs.map Prod.snd)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change summary diagnosticMeasure ([a] ++ xs) = _
    rw [summary_append, summary_singleton]
    change diagnosticMeasure a * diagnostic xs = _
    rw [ih]
    apply Prod.ext
    · change 1 + xs.length = (a :: xs).length
      simp [Nat.add_comm]
    · rfl

end Sequences.OrderedSummary

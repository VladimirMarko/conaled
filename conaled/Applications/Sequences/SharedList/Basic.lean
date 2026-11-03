import Applications.Durability.Storage
import Applications.Resources.Measured

/-!
# Immutable list cells and retained roots

A model of fresh allocation and sharing for the PFDS reconstruction. The heap
extension algebra is reused from `Durability`, but no durable-write capability
is assumed here. Addresses, reads and allocation are abstract operations; these
theorems do not establish Lean allocator behavior or machine running time.

The observation relation requires backwards-pointing live chains. Unrelated
cells need not form lists. Validity, roots, list values and allocation counts
remain distinct.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Sequences.SharedList

abbrev Root := Option Nat

variable {α : Type}

/-- All occupied addresses are strictly below the allocation frontier. -/
structure Store (α : Type) where
  heap : Durability.Heap (α × Root)
  next : Nat
  vacant : ∀ i, next ≤ i → heap i = none

def empty : Store α := ⟨fun _ => none, 0, fun _ _ => rfl⟩

def Below : Root → Nat → Prop
  | none, _ => True
  | some a, n => a < n

theorem Below.mono {r : Root} {a b : Nat} (h : Below r a) (ab : a ≤ b) :
    Below r b := by
  cases r with
  | none => trivial
  | some r => exact Nat.lt_of_lt_of_le h ab

/-- Finite list observation, including the local order on cell addresses. -/
inductive Represents (heap : Durability.Heap (α × Root)) : Root → List α → Prop
  | nil : Represents heap none []
  | cons {a : Nat} {x : α} {r : Root} {xs : List α} :
      heap a = some (x, r) → Below r a → Represents heap r xs →
      Represents heap (some a) (x :: xs)

theorem Represents.mono {a b : Durability.Heap (α × Root)}
    (extension : Durability.Extends a b) {r : Root} {xs : List α}
    (h : Represents a r xs) : Represents b r xs := by
  induction h with
  | nil => exact .nil
  | cons lookup below _ ih => exact .cons (extension _ _ lookup) below ih

theorem Represents.unique {heap : Durability.Heap (α × Root)}
    {r : Root} {xs ys : List α} (h : Represents heap r xs)
    (k : Represents heap r ys) : xs = ys := by
  induction h generalizing ys with
  | nil => cases k; rfl
  | @cons a x r xs lookup below tail ih =>
      cases k with
      | @cons _ y q ys lookup' _ tail' =>
          have eq : (x, r) = (y, q) := Option.some.inj (lookup.symm.trans lookup')
          cases eq
          exact congrArg (List.cons x) (ih tail')

theorem Represents.below_next {s : Store α} {r : Root} {xs : List α}
    (h : Represents s.heap r xs) : Below r s.next := by
  cases h with
  | nil => trivial
  | @cons a x r xs lookup _ _ =>
      change a < s.next
      by_contra hn
      have vacant := s.vacant a (by omega)
      rw [vacant] at lookup
      contradiction

theorem Represents.length_le {heap : Durability.Heap (α × Root)}
    {r : Root} {xs : List α} (h : Represents heap r xs) {n : Nat}
    (below : Below r n) : xs.length ≤ n := by
  induction h generalizing n with
  | nil => simp
  | @cons a x r xs _ tailBelow _ ih =>
      have ht := ih tailBelow
      change a < n at below
      simp only [List.length_cons]
      omega

theorem Represents.length_le_next {s : Store α} {r : Root} {xs : List α}
    (h : Represents s.heap r xs) : xs.length ≤ s.next :=
  h.length_le h.below_next

/-- One fresh cell; the caller supplies any validity law for its tail. -/
def allocate (s : Store α) (x : α) (r : Root) : Store α × Root :=
  (⟨Durability.put s.heap s.next (x, r), s.next + 1, by
    intro i hi
    have ne : i ≠ s.next := by omega
    simp [Durability.put, ne, s.vacant i (by omega)]⟩, some s.next)

@[simp] theorem allocate_next (s : Store α) (x : α) (r : Root) :
    (allocate s x r).1.next = s.next + 1 := rfl

@[simp] theorem allocate_root (s : Store α) (x : α) (r : Root) :
    (allocate s x r).2 = some s.next := rfl

@[simp] theorem allocate_lookup (s : Store α) (x : α) (r : Root) :
    (allocate s x r).1.heap s.next = some (x, r) := by
  simp [allocate, Durability.put]

theorem allocate_extends (s : Store α) (x : α) (r : Root) :
    Durability.Extends s.heap (allocate s x r).1.heap :=
  Durability.extends_put s.heap s.next (x, r) (s.vacant _ (Nat.le_refl _))

/-- Every old version survives, including roots not used by this allocation. -/
theorem allocate_retains (s : Store α) (x : α) (r old : Root) (xs : List α)
    (h : Represents s.heap old xs) :
    Represents (allocate s x r).1.heap old xs :=
  h.mono (allocate_extends s x r)

theorem allocate_represents {s : Store α} {r : Root} {xs : List α}
    (h : Represents s.heap r xs) (x : α) :
    Represents (allocate s x r).1.heap (allocate s x r).2 (x :: xs) :=
  .cons (allocate_lookup s x r) h.below_next (h.mono (allocate_extends s x r))

def read (s : Store α) (r : Root) : Option (α × Root) := r.bind s.heap

def head (s : Store α) (r : Root) : Option α := (read s r).map Prod.fst

/-- `none` is an empty/invalid operation; `some none` is a valid empty tail. -/
def tail (s : Store α) (r : Root) : Option Root := (read s r).map Prod.snd

theorem head_correct {s : Store α} {r : Root} {xs : List α}
    (h : Represents s.heap r xs) : head s r = xs.head? := by
  cases h with
  | nil => rfl
  | cons lookup _ _ => simp [head, read, lookup]

theorem tail_cons {s : Store α} {r : Root} {x : α} {xs : List α}
    (h : Represents s.heap r (x :: xs)) :
    ∃ q, tail s r = some q ∧ Represents s.heap q xs := by
  cases h with
  | @cons a _ q _ lookup _ rest =>
      exact ⟨q, by simp [tail, read, lookup], rest⟩

@[simp] theorem tail_empty (s : Store α) : tail s none = none := rfl

/-- Follow exactly `n` links; exhaustion before `n` is an explicit failure. -/
def advance : Nat → Store α → Root → Option Root
  | 0, _, r => some r
  | n + 1, s, r => (read s r).bind fun c => advance n s c.2

theorem advance_step {s : Store α} {a : Nat} {x : α} {r : Root}
    (lookup : s.heap a = some (x, r)) (n : Nat) :
    advance (n + 1) s (some a) = advance n s r := by
  simp [advance, read, lookup]

theorem advance_prefix {s : Store α} {r : Root} {xs : List α}
    (h : Represents s.heap r xs) {n : Nat} (inside : n ≤ xs.length) :
    ∃ q, advance n s r = some q ∧ Represents s.heap q (xs.drop n) := by
  induction n generalizing r xs with
  | zero => exact ⟨r, rfl, by simpa using h⟩
  | succ n ih =>
      cases h with
      | nil => simp at inside
      | cons lookup _ rest =>
          obtain ⟨q, run, rep⟩ := ih rest (by simpa using inside)
          exact ⟨q, by rw [advance_step lookup]; exact run, by simpa using rep⟩

theorem advance_mono {s t : Store α} (extension : Durability.Extends s.heap t.heap)
    {n : Nat} {r q : Root} (h : advance n s r = some q) :
    advance n t r = some q := by
  induction n generalizing r with
  | zero => exact h
  | succ n ih =>
      cases r with
      | none => simp [advance, read] at h
      | some a =>
          cases lookup : s.heap a with
          | none => simp [advance, read, lookup] at h
          | some c =>
              have next := extension a c lookup
              simp only [advance, read, Option.bind_some, lookup] at h
              simpa [advance, read, next] using ih h

theorem advance_end {s : Store α} {r : Root} {xs : List α}
    (h : Represents s.heap r xs) : advance xs.length s r = some none := by
  induction h with
  | nil => rfl
  | cons lookup _ _ ih => simpa [advance, read, lookup] using ih

end Sequences.SharedList

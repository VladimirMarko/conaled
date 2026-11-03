import SquareKit.ListFusion
import Mathlib.Data.List.Infix

/-!
# Symmetric lists

The pair representation and half-split rebalancing follow Chapter 3, §3.1 of
*Algorithm Design with Haskell*. `Inv` states the representation invariant:
when either component is empty, the other has at most one element.

The selectors return `Option`, and deleting from the empty representation returns
the empty representation. These are explicit total extensions of the source's
undefined empty cases. The abstraction theorems apply to every valid pair,
including the empty pair. This module does not claim an amortized cost bound.

Provenance and statement review: `docs/research/adwh-symmetric-lists.md`.
-/

namespace Sequences.Symmetric

universe u
variable {α : Type u}

abbrev SymList (α : Type u) := List α × List α

def fromSL (s : SymList α) : List α := s.1 ++ s.2.reverse

def Inv (s : SymList α) : Prop :=
  (s.1 = [] → s.2.length ≤ 1) ∧ (s.2 = [] → s.1.length ≤ 1)

def single : List α → Bool
  | [_] => true
  | _ => false

def invSL : SymList α → Bool
  | ([], ys) => ys.isEmpty || single ys
  | (xs, []) => xs.isEmpty || single xs
  | (_ :: _, _ :: _) => true

theorem single_eq_true_iff (xs : List α) : single xs = true ↔ xs.length = 1 := by
  cases xs with
  | nil => simp [single]
  | cons x xs => cases xs <;> simp [single]

theorem invSL_eq_true_iff (s : SymList α) : invSL s = true ↔ Inv s := by
  rcases s with ⟨xs, ys⟩
  cases xs with
  | nil =>
    cases ys with
    | nil => simp [invSL, Inv, single]
    | cons y ys =>
      simp only [invSL, List.isEmpty_cons, Bool.false_or, single_eq_true_iff,
        Inv, List.length_cons, List.length_nil, List.cons_ne_nil, false_implies,
        and_true, true_implies]
      omega
  | cons x xs =>
    cases ys with
    | nil =>
      simp only [invSL, List.isEmpty_cons, Bool.false_or, single_eq_true_iff,
        Inv, List.length_cons, List.length_nil, List.cons_ne_nil, false_implies,
        true_and, true_implies]
      omega
    | cons y ys => simp [invSL, Inv]

def nilSL : SymList α := ([], [])

def nullSL (s : SymList α) : Bool := s.1.isEmpty && s.2.isEmpty

def singleSL (s : SymList α) : Bool :=
  (s.1.isEmpty && single s.2) || (s.2.isEmpty && single s.1)

def lengthSL (s : SymList α) : Nat := s.1.length + s.2.length

theorem inv_nilSL : Inv (nilSL : SymList α) := by simp [nilSL, Inv]

@[simp] theorem fromSL_nilSL : fromSL (nilSL : SymList α) = [] := rfl

theorem length_fromSL (s : SymList α) : (fromSL s).length = lengthSL s := by
  simp [fromSL, lengthSL]

theorem nullSL_eq_true_iff (s : SymList α) : nullSL s = true ↔ fromSL s = [] := by
  simp [nullSL, fromSL]

theorem nullSL_eq_true_iff_nilSL (s : SymList α) : nullSL s = true ↔ s = nilSL := by
  rcases s with ⟨xs, ys⟩
  simp [nullSL, nilSL]

theorem lengthSL_eq_zero_iff (s : SymList α) : lengthSL s = 0 ↔ s = nilSL := by
  rcases s with ⟨xs, ys⟩
  simp [lengthSL, nilSL, Prod.mk.injEq]

theorem singleSL_eq_true_iff (s : SymList α) :
    singleSL s = true ↔ (fromSL s).length = 1 := by
  simp only [singleSL, Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff,
    single_eq_true_iff, length_fromSL, lengthSL]
  constructor
  · rintro (⟨h, hlen⟩ | ⟨h, hlen⟩) <;> simp [h, hlen]
  · intro h
    have : s.1.length = 0 ∧ s.2.length = 1 ∨ s.2.length = 0 ∧ s.1.length = 1 := by
      omega
    simpa only [List.length_eq_zero_iff] using this

theorem reverse_eq_self_of_length_le_one (xs : List α) (h : xs.length ≤ 1) :
    xs.reverse = xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    cases xs with
    | nil => rfl
    | cons y ys => simp at h

def reverseSL (s : SymList α) : SymList α := (s.2, s.1)

theorem inv_reverseSL (s : SymList α) (h : Inv s) : Inv (reverseSL s) := ⟨h.2, h.1⟩

@[simp] theorem reverseSL_reverseSL (s : SymList α) : reverseSL (reverseSL s) = s := rfl

theorem fromSL_reverseSL (s : SymList α) : fromSL (reverseSL s) = (fromSL s).reverse := by
  simp [fromSL, reverseSL]

def consSL (x : α) : SymList α → SymList α
  | (xs, []) => ([x], xs)
  | (xs, y :: ys) => (x :: xs, y :: ys)

def snocSL (x : α) : SymList α → SymList α
  | ([], ys) => (ys, [x])
  | (y :: ys, zs) => (y :: ys, x :: zs)

theorem inv_consSL (x : α) (s : SymList α) : Inv (consSL x s) := by
  rcases s with ⟨xs, ys⟩
  cases xs <;> cases ys <;> simp [consSL, Inv]

theorem inv_snocSL (x : α) (s : SymList α) : Inv (snocSL x s) := by
  rcases s with ⟨xs, ys⟩
  cases xs <;> cases ys <;> simp [snocSL, Inv]

theorem fromSL_consSL (x : α) (s : SymList α) (h : Inv s) :
    fromSL (consSL x s) = x :: fromSL s := by
  rcases s with ⟨xs, ys⟩
  cases ys with
  | nil =>
    have hr := reverse_eq_self_of_length_le_one xs (h.2 rfl)
    simp [consSL, fromSL, hr]
  | cons y ys => rfl

theorem fromSL_snocSL (x : α) (s : SymList α) (h : Inv s) :
    fromSL (snocSL x s) = fromSL s ++ [x] := by
  rcases s with ⟨xs, ys⟩
  cases xs with
  | nil =>
    have hr := reverse_eq_self_of_length_le_one ys (h.1 rfl)
    simp [snocSL, fromSL, hr]
  | cons y xs => simp [snocSL, fromSL, List.append_assoc]

def headSL : SymList α → Option α
  | ([], ys) => ys.head?
  | (x :: _, _) => some x

def lastSL : SymList α → Option α
  | (xs, []) => xs.head?
  | (_, y :: _) => some y

theorem headSL_eq_head (s : SymList α) (h : Inv s) : headSL s = (fromSL s).head? := by
  rcases s with ⟨xs, ys⟩
  cases xs with
  | nil =>
    have hr := reverse_eq_self_of_length_le_one ys (h.1 rfl)
    simp [headSL, fromSL, hr]
  | cons x xs => rfl

theorem lastSL_eq_headSL_reverseSL (s : SymList α) : lastSL s = headSL (reverseSL s) := by
  rcases s with ⟨xs, ys⟩
  cases ys <;> rfl

theorem lastSL_eq_getLast (s : SymList α) (h : Inv s) : lastSL s = (fromSL s).getLast? := by
  rw [lastSL_eq_headSL_reverseSL, headSL_eq_head _ (inv_reverseSL _ h), fromSL_reverseSL]
  exact List.head?_reverse

/-- The exact take/drop half split used by the source's singleton-rear case. -/
def splitSL (xs : List α) : SymList α :=
  (xs.take (xs.length / 2), (xs.drop (xs.length / 2)).reverse)

theorem fromSL_splitSL (xs : List α) : fromSL (splitSL xs) = xs := by
  simp only [fromSL, splitSL, List.reverse_reverse]
  exact List.take_append_drop _ xs

theorem inv_splitSL (xs : List α) : Inv (splitSL xs) := by
  have hdiv := Nat.div_le_self xs.length 2
  constructor
  · intro h
    have hh := congrArg List.length h
    simp only [splitSL, List.length_take, List.length_nil] at hh
    simp only [splitSL, List.length_reverse, List.length_drop]
    omega
  · intro h
    have hh := congrArg List.length h
    simp only [splitSL, List.length_reverse, List.length_drop, List.length_nil] at hh
    simp only [splitSL, List.length_take]
    omega

def tailSL : SymList α → SymList α
  | ([], _) => nilSL
  | ([_], ys) => reverseSL (splitSL ys)
  | (_ :: x :: xs, ys) => (x :: xs, ys)

theorem inv_tailSL (s : SymList α) (h : Inv s) : Inv (tailSL s) := by
  rcases s with ⟨xs, ys⟩
  cases xs with
  | nil => exact inv_nilSL
  | cons x xs =>
    cases xs with
    | nil => exact inv_reverseSL _ (inv_splitSL ys)
    | cons y xs =>
      constructor
      · intro hn; cases hn
      · intro hy
        have hh := h.2 hy
        simp at hh

theorem fromSL_tailSL (s : SymList α) (h : Inv s) :
    fromSL (tailSL s) = (fromSL s).tail := by
  rcases s with ⟨xs, ys⟩
  cases xs with
  | nil =>
    have hy := h.1 rfl
    cases ys with
    | nil => rfl
    | cons y ys =>
      cases ys with
      | nil => rfl
      | cons z ys => simp at hy
  | cons x xs =>
    cases xs with
    | nil =>
      change fromSL (reverseSL (splitSL ys)) = ys.reverse
      rw [fromSL_reverseSL, fromSL_splitSL]
    | cons y xs => rfl

/-- Duality gives exactly the source's three cases for `initSL`. -/
def initSL (s : SymList α) : SymList α := reverseSL (tailSL (reverseSL s))

@[simp] theorem initSL_empty_back (xs : List α) : initSL (xs, []) = nilSL := rfl

@[simp] theorem initSL_singleton_back (xs : List α) (y : α) :
    initSL (xs, [y]) = splitSL xs := rfl

@[simp] theorem initSL_long_back (xs ys : List α) (y z : α) :
    initSL (xs, y :: z :: ys) = (xs, z :: ys) := rfl

theorem inv_initSL (s : SymList α) (h : Inv s) : Inv (initSL s) :=
  inv_reverseSL _ (inv_tailSL _ (inv_reverseSL _ h))

theorem fromSL_initSL (s : SymList α) (h : Inv s) :
    fromSL (initSL s) = (fromSL s).dropLast := by
  rw [initSL, fromSL_reverseSL, fromSL_tailSL _ (inv_reverseSL _ h), fromSL_reverseSL]
  simp

theorem lengthSL_reverseSL (s : SymList α) : lengthSL (reverseSL s) = lengthSL s := by
  simp [lengthSL, reverseSL, Nat.add_comm]

theorem lengthSL_splitSL (xs : List α) : lengthSL (splitSL xs) = xs.length := by
  rw [← length_fromSL, fromSL_splitSL]

/-- Strict descent holds even for malformed pairs; abstraction correctness uses `Inv`. -/
theorem tailSL_length_lt (s : SymList α) (h : s ≠ nilSL) :
    lengthSL (tailSL s) < lengthSL s := by
  rcases s with ⟨xs, ys⟩
  cases xs with
  | nil =>
    cases ys with
    | nil => exact False.elim (h rfl)
    | cons y ys => simp [tailSL, nilSL, lengthSL]
  | cons x xs =>
    cases xs with
    | nil =>
      change lengthSL (reverseSL (splitSL ys)) < 1 + ys.length
      rw [lengthSL_reverseSL, lengthSL_splitSL]
      omega
    | cons y xs => simp [tailSL, lengthSL, Nat.add_assoc]

theorem initSL_length_lt (s : SymList α) (h : s ≠ nilSL) :
    lengthSL (initSL s) < lengthSL s := by
  have hr : reverseSL s ≠ nilSL := by
    intro he
    apply h
    have hh := congrArg reverseSL he
    exact (reverseSL_reverseSL s).symm.trans hh
  rw [initSL, lengthSL_reverseSL, ← lengthSL_reverseSL s]
  exact tailSL_length_lt _ hr

theorem headSL_eq_none_iff (s : SymList α) : headSL s = none ↔ s = nilSL := by
  rcases s with ⟨xs, ys⟩
  cases xs <;> simp [headSL, nilSL]

theorem fromSL_eq_cons (s : SymList α) (h : Inv s) {x : α}
    (hh : headSL s = some x) : fromSL s = x :: fromSL (tailSL s) := by
  rw [headSL_eq_head s h] at hh
  obtain ⟨ys, hy⟩ := List.head?_eq_some_iff.mp hh
  rw [fromSL_tailSL s h, hy]
  rfl

/-- The guarded recursive source algorithm, with a proved decreasing length. -/
def dropWhileSL (p : α → Bool) (s : SymList α) : SymList α :=
  match _hh : headSL s with
  | none => nilSL
  | some x => if p x then dropWhileSL p (tailSL s) else s
termination_by lengthSL s
decreasing_by
  apply tailSL_length_lt
  intro he
  subst s
  simp [headSL, nilSL] at _hh

theorem inv_dropWhileSL (p : α → Bool) (s : SymList α) (h : Inv s) :
    Inv (dropWhileSL p s) := by
  induction s using (measure lengthSL).wf.induction with
  | h s ih =>
    rw [dropWhileSL]
    split
    · exact inv_nilSL
    · rename_i x hx
      split
      · apply ih _ (tailSL_length_lt s (by
          intro he
          subst s
          simp [headSL, nilSL] at hx)) (inv_tailSL s h)
      · exact h

theorem fromSL_dropWhileSL (p : α → Bool) (s : SymList α) (h : Inv s) :
    fromSL (dropWhileSL p s) = (fromSL s).dropWhile p := by
  induction s using (measure lengthSL).wf.induction with
  | h s ih =>
    rw [dropWhileSL]
    split
    · rename_i hn
      have he := (headSL_eq_none_iff s).mp hn
      subst s
      rfl
    · rename_i x hx
      have hne : s ≠ nilSL := by
        intro he
        subst s
        simp [headSL, nilSL] at hx
      split
      · rename_i hp
        rw [ih _ (tailSL_length_lt s hne) (inv_tailSL s h), fromSL_eq_cons s h hx]
        exact (List.dropWhile_cons_of_pos hp).symm
      · rename_i hp
        rw [fromSL_eq_cons s h hx, List.dropWhile_cons_of_neg hp]

def toSL (xs : List α) : SymList α := xs.foldr consSL nilSL

theorem inv_toSL (xs : List α) : Inv (toSL xs) := by
  cases xs with
  | nil => exact inv_nilSL
  | cons x xs => exact inv_consSL x (toSL xs)

theorem fromSL_toSL (xs : List α) : fromSL (toSL xs) = xs := by
  simpa [toSL] using SquareKit.ListFusion.foldr_reachable consSL List.cons
    fromSL Inv nilSL inv_nilSL (fun x s _ => inv_consSL x s) fromSL_consSL xs

end Sequences.Symmetric

import Applications.Bracketing.Basic

set_option autoImplicit false
set_option warningAsError true

namespace RandomAccess
universe u
variable {α : Type u}

inductive Tree (α : Type u) where
  | leaf : α → Tree α
  | node : Nat → Tree α → Tree α → Tree α
deriving Repr, DecidableEq

def size : Tree α → Nat
  | .leaf _ => 1
  | .node n _ _ => n

def node (l r : Tree α) : Tree α := .node (size l + size r) l r

def fromT : Tree α → List α
  | .leaf x => [x]
  | .node _ l r => fromT l ++ fromT r

/-- Forget per-node caches into the shared ordered binary tree. -/
def erase : Tree α → Bracketing.Tree α
  | .leaf x => .leaf x
  | .node _ l r => .fork (erase l) (erase r)

theorem fromT_eq_fringe (t : Tree α) : fromT t = Bracketing.fringeSpec (erase t) := by
  induction t with
  | leaf x => rfl
  | node n l r ihl ihr => simp [fromT, erase, Bracketing.fringeSpec, ihl, ihr]

theorem fromT_ne_nil (t : Tree α) : fromT t ≠ [] := by
  rw [fromT_eq_fringe]
  exact Bracketing.fringeSpec_ne_nil _

inductive Perfect : Nat → Tree α → Prop where
  | leaf (x : α) : Perfect 0 (.leaf x)
  | node (rank : Nat) (l r : Tree α) (hl : Perfect rank l) (hr : Perfect rank r) :
      Perfect (rank + 1) (.node (2 ^ (rank + 1)) l r)

theorem size_eq_pow {rank : Nat} {t : Tree α} (h : Perfect rank t) : size t = 2 ^ rank := by
  cases h <;> simp [size]

theorem fromT_length {rank : Nat} {t : Tree α} (h : Perfect rank t) :
    (fromT t).length = 2 ^ rank := by
  induction h with
  | leaf x => rfl
  | node rank l r hl hr ihl ihr =>
    simp only [fromT, List.length_append, ihl, ihr, Nat.pow_succ]
    omega

theorem fromT_length_eq_size {rank : Nat} {t : Tree α} (h : Perfect rank t) :
    (fromT t).length = size t := (fromT_length h).trans (size_eq_pow h).symm

theorem perfect_node {rank : Nat} {l r : Tree α}
    (hl : Perfect rank l) (hr : Perfect rank r) : Perfect (rank + 1) (node l r) := by
  have hs : size l + size r = 2 ^ (rank + 1) := by
    rw [size_eq_pow hl, size_eq_pow hr, Nat.pow_succ]
    omega
  simpa only [node, hs] using Perfect.node rank l r hl hr

inductive Digit (α : Type u) where
  | zero : Digit α
  | one : Tree α → Digit α
deriving Repr, DecidableEq

abbrev RAList (α : Type u) := List (Digit α)

def nilRA : RAList α := []

def nullRA (ds : RAList α) : Bool := ds.isEmpty

def fromRA : RAList α → List α
  | [] => []
  | .zero :: ds => fromRA ds
  | .one t :: ds => fromT t ++ fromRA ds

/-- A valid suffix starts at the indicated binary rank. -/
inductive Valid : Nat → RAList α → Prop where
  | nil (rank : Nat) : Valid rank []
  | zero {rank : Nat} {ds : RAList α} (hne : ds ≠ []) (h : Valid (rank + 1) ds) :
      Valid rank (.zero :: ds)
  | one {rank : Nat} {t : Tree α} {ds : RAList α}
      (ht : Perfect rank t) (h : Valid (rank + 1) ds) : Valid rank (.one t :: ds)

abbrev Inv (ds : RAList α) : Prop := Valid 0 ds

def checkSizes (rank : Nat) : RAList α → Bool
  | [] => true
  | .zero :: ds => checkSizes (rank + 1) ds
  | .one t :: ds => decide (size t = 2 ^ rank) && checkSizes (rank + 1) ds

/-- The source's shallow size test, expressed with a finite rank recursion. -/
def invRA (ds : RAList α) : Bool := checkSizes 0 ds

theorem valid_checkSizes {rank : Nat} {ds : RAList α} (h : Valid rank ds) :
    checkSizes rank ds = true := by
  induction h with
  | nil rank => rfl
  | zero hne h ih => exact ih
  | one ht h ih => simp [checkSizes, size_eq_pow ht, ih]

theorem invRA_of_Inv {ds : RAList α} (h : Inv ds) : invRA ds = true := valid_checkSizes h

theorem fromRA_ne_nil {rank : Nat} {ds : RAList α}
    (h : Valid rank ds) (hne : ds ≠ []) : fromRA ds ≠ [] := by
  induction h with
  | nil rank => exact False.elim (hne rfl)
  | zero htail h ih => exact ih htail
  | @one rank t ds ht h ih =>
    intro he
    exact fromT_ne_nil t (List.append_eq_nil_iff.mp he).1

theorem nullRA_refinement {ds : RAList α} (h : Inv ds) :
    nullRA ds = true ↔ fromRA ds = [] := by
  constructor
  · intro hn
    have he := List.isEmpty_iff.mp hn
    subst ds
    rfl
  · intro he
    by_cases hn : ds = []
    · subst ds; rfl
    · exact False.elim (fromRA_ne_nil h hn he)

def consT (t : Tree α) : RAList α → RAList α
  | [] => [.one t]
  | .zero :: ds => .one t :: ds
  | .one u :: ds => .zero :: consT (node t u) ds

def consRA (x : α) (ds : RAList α) : RAList α := consT (.leaf x) ds

theorem consT_ne_nil (t : Tree α) (ds : RAList α) : consT t ds ≠ [] := by
  cases ds with
  | nil => simp [consT]
  | cons d ds => cases d <;> simp [consT]

theorem fromRA_consT (t : Tree α) (ds : RAList α) :
    fromRA (consT t ds) = fromT t ++ fromRA ds := by
  induction ds generalizing t with
  | nil => rfl
  | cons d ds ih =>
    cases d with
    | zero => rfl
    | one u => simpa only [consT, fromRA, node, fromT, List.append_assoc] using ih (node t u)

theorem valid_consT {rank : Nat} {ds : RAList α} (h : Valid rank ds)
    (t : Tree α) (ht : Perfect rank t) : Valid rank (consT t ds) := by
  induction h generalizing t with
  | nil rank => exact Valid.one ht (Valid.nil _)
  | zero hne h ih => exact Valid.one ht h
  | @one rank u ds hu h ih =>
    exact Valid.zero (consT_ne_nil _ _) (ih _ (perfect_node ht hu))

theorem fromRA_consRA (x : α) (ds : RAList α) :
    fromRA (consRA x ds) = x :: fromRA ds := by
  simpa only [consRA, fromT, List.singleton_append] using fromRA_consT (.leaf x) ds

theorem inv_consRA (x : α) {ds : RAList α} (h : Inv ds) : Inv (consRA x ds) :=
  valid_consT h (.leaf x) (Perfect.leaf x)

def toRA (xs : List α) : RAList α := xs.foldr consRA nilRA

theorem inv_toRA (xs : List α) : Inv (toRA xs) := by
  induction xs with
  | nil => exact Valid.nil _
  | cons x xs ih => exact inv_consRA x ih

theorem fromRA_toRA (xs : List α) : fromRA (toRA xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change fromRA (consRA x (toRA xs)) = x :: xs
    rw [fromRA_consRA, ih]


end RandomAccess

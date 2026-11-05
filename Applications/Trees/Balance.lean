import Applications.Trees.Observations
import Mathlib.Data.List.TakeDrop

/-! Sequential prefix balancing from FDSA Chapter 4.
The left recursion returns the suffix supplying the root and right recursion.
The safe core returns `none` precisely for an undersized input. No default
label, comparison, or inhabited-label assumption is required. `take` and `drop`
occur only in the specification, not in the implementation.

The total source-facing wrappers use the empty tree on failure. Their prefix
laws retain the exact successful-input premise. Shape and logarithmic-height
theorems are separate from the order-and-size contracts in this module.
Provenance: `docs/research/fdsa-reconstruction-map.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.Balance
universe u
variable {α : Type u}

/-- Consume exactly the requested prefix, returning its tree and untouched suffix. -/
def bal (n : Nat) (xs : List α) : Option (BinaryTree α × List α) :=
  match n with
  | 0 => some (.nil, xs)
  | k + 1 =>
      match bal ((k + 1) / 2) xs with
      | none => none
      | some (_, []) => none
      | some (l, a :: ys) =>
          match bal (k - (k + 1) / 2) ys with
          | none => none
          | some (r, zs) => some (.node a l r, zs)
termination_by n
decreasing_by all_goals omega

@[simp] theorem bal_zero (xs : List α) : bal 0 xs = some (.nil, xs) := by
  rw [bal]

theorem bal_succ (k : Nat) (xs : List α) :
    bal (k + 1) xs =
      match bal ((k + 1) / 2) xs with
      | none => none
      | some (_, []) => none
      | some (l, a :: ys) =>
          match bal (k - (k + 1) / 2) ys with
          | none => none
          | some (r, zs) => some (.node a l r, zs) := by
  rw [bal]

/-- Every successful execution preserves all occurrences and has the requested size. -/
theorem bal_spec {n : Nat} {xs zs : List α} {t : BinaryTree α}
    (h : bal n xs = some (t, zs)) : xs = inorder t ++ zs ∧ t.numNodes = n := by
  induction n using Nat.strong_induction_on generalizing xs t zs with
  | h n ih =>
      cases n with
      | zero =>
          simp only [bal_zero, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          simp
      | succ k =>
          cases hl : bal ((k + 1) / 2) xs with
          | none => simp only [bal_succ, hl] at h
          | some p =>
              rcases p with ⟨l, ys⟩
              cases ys with
              | nil => simp only [bal_succ, hl] at h
              | cons a ys =>
                  cases hr : bal (k - (k + 1) / 2) ys with
                  | none => simp only [bal_succ, hl, hr] at h
                  | some q =>
                      rcases q with ⟨r, ws⟩
                      simp only [bal_succ, hl, hr, Option.some.injEq, Prod.mk.injEq] at h
                      rcases h with ⟨rfl, rfl⟩
                      have hleft := ih ((k + 1) / 2) (by omega)
                        (xs := xs) (t := l) (zs := a :: ys) hl
                      have hright := ih (k - (k + 1) / 2) (by omega)
                        (xs := ys) (t := r) (zs := ws) hr
                      constructor
                      · rw [hleft.1, hright.1, inorder_node]
                        simp only [List.append_assoc, List.cons_append]
                      · simp only [BinaryTree.numNodes, hleft.2, hright.2]
                        omega

/-- Sufficient input is the complete domain condition; labels need no inhabitant. -/
theorem bal_exists {n : Nat} {xs : List α} (h : n ≤ xs.length) :
    ∃ t zs, bal n xs = some (t, zs) := by
  induction n using Nat.strong_induction_on generalizing xs with
  | h n ih =>
      cases n with
      | zero => exact ⟨.nil, xs, bal_zero xs⟩
      | succ k =>
          have hleftDomain : (k + 1) / 2 ≤ xs.length := by omega
          obtain ⟨l, ys, hl⟩ := ih ((k + 1) / 2) (by omega) hleftDomain
          have hleft := bal_spec hl
          have hlength : xs.length = (k + 1) / 2 + ys.length := by
            rw [hleft.1, List.length_append, inorder_length, hleft.2]
          cases ys with
          | nil =>
              simp only [List.length_nil] at hlength
              omega
          | cons a ys =>
              simp only [List.length_cons] at hlength
              have hrightDomain : k - (k + 1) / 2 ≤ ys.length := by omega
              obtain ⟨r, zs, hr⟩ :=
                ih (k - (k + 1) / 2) (by omega) hrightDomain
              exact ⟨.node a l r, zs, by simp only [bal_succ, hl, hr]⟩

theorem bal_succeeds_iff (n : Nat) (xs : List α) :
    (∃ t zs, bal n xs = some (t, zs)) ↔ n ≤ xs.length := by
  constructor
  · rintro ⟨t, zs, h⟩
    have hs := bal_spec h
    have hlength := congrArg List.length hs.1
    simp only [List.length_append, inorder_length, hs.2] at hlength
    omega
  · exact bal_exists

theorem bal_eq_none_iff (n : Nat) (xs : List α) :
    bal n xs = none ↔ xs.length < n := by
  constructor
  · intro h
    by_contra hshort
    have hle : n ≤ xs.length := Nat.le_of_not_gt hshort
    obtain ⟨t, zs, hs⟩ := bal_exists hle
    rw [h] at hs
    contradiction
  · intro h
    cases he : bal n xs with
    | none => rfl
    | some p =>
        rcases p with ⟨t, zs⟩
        have hle := (bal_succeeds_iff n xs).mp ⟨t, zs, he⟩
        omega

theorem bal_inorder {n : Nat} {xs zs : List α} {t : BinaryTree α}
    (h : bal n xs = some (t, zs)) : inorder t = xs.take n := by
  obtain ⟨hx, hn⟩ := bal_spec h
  have hlength : (inorder t).length = n := (inorder_length t).trans hn
  rw [hx]
  exact (List.take_left' hlength).symm

theorem bal_suffix {n : Nat} {xs zs : List α} {t : BinaryTree α}
    (h : bal n xs = some (t, zs)) : zs = xs.drop n := by
  obtain ⟨hx, hn⟩ := bal_spec h
  have hlength : (inorder t).length = n := (inorder_length t).trans hn
  rw [hx]
  exact (List.drop_left' hlength).symm

theorem bal_suffix_length {n : Nat} {xs zs : List α} {t : BinaryTree α}
    (h : bal n xs = some (t, zs)) : zs.length = xs.length - n := by
  rw [bal_suffix h, List.length_drop]

/-- Source wrapper, with an explicit empty-tree fallback outside the core domain. -/
def balList (n : Nat) (xs : List α) : BinaryTree α :=
  match bal n xs with
  | none => .nil
  | some (t, _) => t

def balanceList (xs : List α) : BinaryTree α := balList xs.length xs

def balTree (n : Nat) (t : BinaryTree α) : BinaryTree α := balList n (inorder t)

def balanceTree (t : BinaryTree α) : BinaryTree α := balTree t.numNodes t

theorem balList_of_some {n : Nat} {xs zs : List α} {t : BinaryTree α}
    (h : bal n xs = some (t, zs)) : balList n xs = t := by
  simp only [balList, h]

theorem balList_of_none {n : Nat} {xs : List α}
    (h : bal n xs = none) : balList n xs = .nil := by
  simp only [balList, h]

theorem inorder_balList {n : Nat} {xs : List α} (h : n ≤ xs.length) :
    inorder (balList n xs) = xs.take n := by
  obtain ⟨t, zs, hs⟩ := bal_exists h
  rw [balList_of_some hs]
  exact bal_inorder hs

theorem inorder_balanceList (xs : List α) : inorder (balanceList xs) = xs := by
  simpa only [balanceList, List.take_length] using
    (inorder_balList (n := xs.length) (xs := xs) (Nat.le_refl xs.length))

theorem inorder_balTree {n : Nat} (t : BinaryTree α) (h : n ≤ t.numNodes) :
    inorder (balTree n t) = (inorder t).take n := by
  exact inorder_balList (by simpa only [inorder_length] using h)

theorem inorder_balanceTree (t : BinaryTree α) :
    inorder (balanceTree t) = inorder t := by
  unfold balanceTree
  rw [inorder_balTree t (Nat.le_refl _), ← inorder_length t, List.take_length]

theorem numNodes_balList {n : Nat} {xs : List α} (h : n ≤ xs.length) :
    (balList n xs).numNodes = n := by
  obtain ⟨t, zs, hs⟩ := bal_exists h
  rw [balList_of_some hs]
  exact (bal_spec hs).2

theorem numNodes_balanceList (xs : List α) :
    (balanceList xs).numNodes = xs.length :=
  numNodes_balList (Nat.le_refl xs.length)

theorem numNodes_balTree {n : Nat} (t : BinaryTree α) (h : n ≤ t.numNodes) :
    (balTree n t).numNodes = n :=
  numNodes_balList (by simpa only [inorder_length] using h)

theorem numNodes_balanceTree (t : BinaryTree α) :
    (balanceTree t).numNodes = t.numNodes :=
  numNodes_balTree t (Nat.le_refl t.numNodes)

/-- A client can consume any whole prefix while retaining the exact suffix. -/
theorem bal_prefix (prefix suffix : List α) :
    ∃ t, bal prefix.length (prefix ++ suffix) = some (t, suffix) ∧
      inorder t = prefix ∧ t.numNodes = prefix.length := by
  have hdomain : prefix.length ≤ (prefix ++ suffix).length := by
    simp only [List.length_append]
    omega
  obtain ⟨t, zs, h⟩ := bal_exists hdomain
  have hz := bal_suffix h
  rw [List.drop_left] at hz
  have hi := bal_inorder h
  rw [List.take_left] at hi
  subst zs
  exact ⟨t, h, hi, (bal_spec h).2⟩

end Trees.Balance

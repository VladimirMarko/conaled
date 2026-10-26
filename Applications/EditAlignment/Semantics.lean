import Applications.Optimization.SelectionTies

/-! Ordered alignment semantics and fixed-price choice through shared first minima. -/
set_option autoImplicit false
set_option warningAsError true

namespace EditAlignment
universe u
variable {α : Type u}

inductive Op (α : Type u) where
  | copy : α → Op α
  | replace : α → α → Op α
  | delete : α → Op α
  | insert : α → Op α
  deriving DecidableEq

abbrev Script (α : Type u) := List (Op α)

/-- Independent ordered alignment semantics; replacement permits equal symbols. -/
inductive Aligns : Script α → List α → List α → Prop where
  | nil : Aligns [] [] []
  | copy (x : α) {es : Script α} {xs ys : List α} :
      Aligns es xs ys → Aligns (.copy x :: es) (x :: xs) (x :: ys)
  | replace (x y : α) {es : Script α} {xs ys : List α} :
      Aligns es xs ys → Aligns (.replace x y :: es) (x :: xs) (y :: ys)
  | delete (x : α) {es : Script α} {xs ys : List α} :
      Aligns es xs ys → Aligns (.delete x :: es) (x :: xs) ys
  | insert (y : α) {es : Script α} {xs ys : List α} :
      Aligns es xs ys → Aligns (.insert y :: es) xs (y :: ys)

def reconstructStep (op : Op α) (p : List α × List α) : List α × List α :=
  match op with
  | .copy x => (x :: p.1, x :: p.2)
  | .replace x y => (x :: p.1, y :: p.2)
  | .delete x => (x :: p.1, p.2)
  | .insert y => (p.1, y :: p.2)

def reconstruct (es : Script α) : List α × List α := es.foldr reconstructStep ([], [])

theorem Aligns.reconstruct {es : Script α} {xs ys : List α} (h : Aligns es xs ys) :
    reconstruct es = (xs, ys) := by
  induction h <;>
    simp_all [EditAlignment.reconstruct, reconstructStep]

theorem aligns_reconstruct (es : Script α) : Aligns es (reconstruct es).1 (reconstruct es).2 := by
  induction es with
  | nil => exact .nil
  | cons op es ih =>
    cases op with
    | copy x => exact .copy x ih
    | replace x y => exact .replace x y ih
    | delete x => exact .delete x ih
    | insert y => exact .insert y ih

theorem aligns_iff_reconstruct (es : Script α) (xs ys : List α) :
    Aligns es xs ys ↔ reconstruct es = (xs, ys) := by
  constructor
  · exact Aligns.reconstruct
  · intro h
    simpa [h] using aligns_reconstruct es

def ecost : Op α → Nat
  | .copy _ => 0
  | .replace _ _ => 3
  | .delete _ => 2
  | .insert _ => 2

def costE (es : Script α) : Nat := (es.map ecost).sum

theorem costE_cons (op : Op α) (es : Script α) : costE (op :: es) = ecost op + costE es := by
  simp [costE]

theorem prepend_cost_monotone (op : Op α) (as bs : Script α) (h : costE as ≤ costE bs) :
    costE (op :: as) ≤ costE (op :: bs) := by
  simp only [costE_cons]
  exact Nat.add_le_add_left h _

/-- An independent global specification, with no algorithm or enumerator in it. -/
def MinimumEdit (es : Script α) (xs ys : List α) : Prop :=
  Aligns es xs ys ∧ ∀ other, Aligns other xs ys → costE es ≤ costE other

def pick [DecidableEq α] (x y : α) : Op α := if x = y then .copy x else .replace x y

theorem aligns_pick [DecidableEq α] (x y : α) {es : Script α} {xs ys : List α}
    (h : Aligns es xs ys) : Aligns (pick x y :: es) (x :: xs) (y :: ys) := by
  by_cases he : x = y
  · subst y; simpa [pick] using Aligns.copy x h
  · simpa [pick, he] using Aligns.replace x y h

theorem ecost_pick_le_three [DecidableEq α] (x y : α) : ecost (pick x y) ≤ 3 := by
  unfold pick
  split <;> simp [ecost]

/-- `smaller costE`, the source's left-biased two-candidate selection. -/
def best (as bs : Script α) : Script α :=
  (Optimization.Thinning.argmin costE [as, bs]).getD as

theorem best_eq (as bs : Script α) :
    best as bs = if costE as ≤ costE bs then as else bs := by
  simp [best, Optimization.Thinning.argmin]

theorem best_firstMinimum (as bs : Script α) :
    Optimization.FirstMinimum costE [as, bs] (best as bs) := by
  apply Optimization.argmin_firstMinimum
  simp only [Optimization.Thinning.argmin]
  rw [best_eq]


theorem best_tie_left (as bs : Script α) (h : costE as = costE bs) : best as bs = as := by
  simp [best_eq, h]

theorem best_minimizer (as bs : Script α) :
    best as bs ∈ Optimization.minimizers {es | es ∈ [as, bs]} costE := by
  apply Optimization.Thinning.argmin_correct
  simp only [Optimization.Thinning.argmin]
  rw [best_eq]

theorem costE_best_le_left (as bs : Script α) : costE (best as bs) ≤ costE as :=
  (best_minimizer as bs).2 (by simp)

theorem costE_best_le_right (as bs : Script α) : costE (best as bs) ≤ costE bs :=
  (best_minimizer as bs).2 (by simp)

theorem aligns_best {as bs : Script α} {xs ys : List α}
    (ha : Aligns as xs ys) (hb : Aligns bs xs ys) : Aligns (best as bs) xs ys := by
  have hm : best as bs = as ∨ best as bs = bs := by
    simpa using (best_minimizer as bs).1
  rcases hm with h | h <;> rw [h] <;> assumption

theorem aligns_deletes (xs : List α) : Aligns (xs.map Op.delete) xs [] := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .delete x ih

theorem aligns_inserts (ys : List α) : Aligns (ys.map Op.insert) [] ys := by
  induction ys with
  | nil => exact .nil
  | cons y ys ih => exact .insert y ih


end EditAlignment

import SquareKit.ListFusion
import Batteries.Data.DList.Lemmas
import Mathlib.Data.List.Zip

/-! Checked finite source observations use the ordinary List interfaces.
Small partial/signed adapters stay in this client, rather than forming a second
basic-list library. None of these equalities equates demand or operation cost.
See `docs/research/adwh-finite-lists.md`. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.FiniteListInterfaces

universe u v
variable {α : Type u} {β : Type v}

/-- The source label order is index first, including an arbitrary offset. -/
theorem labels_offset (offset : Nat) (xs : List α) :
    (xs.zipIdx offset).map Prod.swap = (List.range' offset xs.length).zip xs := by
  rw [List.zipIdx_eq_zip_range', List.zip_swap]

theorem labels_zero (xs : List α) :
    (xs.zipIdx).map Prod.swap = (List.range xs.length).zip xs := by
  simpa only [List.range_eq_range'] using labels_offset 0 xs

/-- Reconstruct a cons through standard optional head and total residual tail. -/
theorem uncons_observation (xs ys : List α) (x : α) :
    xs.head?.map (fun a => (a, xs.tail)) = some (x, ys) ↔ xs = x :: ys := by
  cases xs <;> simp

/-- A scoped singleton observer rejects both empty and multiple-element input. -/
def singleton? (xs : List α) : Option α :=
  if xs.length = 1 then xs.head? else none

theorem singleton_observation (xs : List α) (x : α) :
    singleton? xs = some x ↔ xs = [x] := by
  cases xs with
  | nil => simp [singleton?]
  | cons y ys => cases ys <;> simp [singleton?]

/-- Preserve the source's empty-input failure instead of silently using []. -/
def init? (xs : List α) : Option (List α) :=
  if xs.isEmpty then none else some xs.dropLast

theorem init_observation (xs : List α) :
    init? xs = if xs = [] then none else some xs.dropLast := by
  cases xs <;> rfl

/-- Signed indexing rejects negative indices before conversion to Nat. -/
def indexSigned (xs : List α) (n : Int) : Option α :=
  if 0 ≤ n then xs[n.toNat]? else none

theorem indexSigned_nat (xs : List α) (n : Nat) :
    indexSigned xs n = xs[n]? := by simp [indexSigned]

theorem indexSigned_negative (xs : List α) (n : Int) (h : n < 0) :
    indexSigned xs n = none := by simp [indexSigned, Int.not_le.mpr h]

theorem nonpositive_counts (xs : List α) (n : Int) (h : n ≤ 0) :
    (xs.take n.toNat, xs.drop n.toNat) = ([], xs) := by
  simp [Int.toNat_eq_zero.mpr h]

theorem natural_counts (xs : List α) (n : Nat) :
    (xs.take (n : Int).toNat, xs.drop (n : Int).toNat) = (xs.take n, xs.drop n) := by
  simp

theorem head_fold (xs : List α) :
    xs.foldr (fun x _ => some x) none = xs.head? := by
  cases xs <;> rfl

theorem takeWhile_fold (p : α → Bool) (xs : List α) :
    xs.foldr (fun x ys => if p x then x :: ys else []) [] = xs.takeWhile p := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp_all

/-- Maximal among initial segments, rather than arbitrary subsequences. -/
theorem takeWhile_maximal (p : α → Bool) (xs ys : List α)
    (hpre : ys <+: xs) (all : ∀ x ∈ ys, p x = true) : ys <+: xs.takeWhile p := by
  rcases hpre with ⟨zs, rfl⟩
  rw [List.takeWhile_append_of_pos all]
  exact ⟨zs.takeWhile p, rfl⟩

/-- Reordering total Boolean tests preserves finite values only. -/
theorem filter_fusion_value (p q : α → Bool) (xs : List α) :
    (xs.filter q).filter p = xs.filter (fun x => q x && p x) := by
  simp only [List.filter_filter, Bool.and_comm]

/-- Use exactly associativity and both identity laws, without commutativity. -/
theorem associative_folds (op : α → α → α) (e : α)
    (assoc : ∀ a b c, op (op a b) c = op a (op b c))
    (left : ∀ a, op e a = a) (right : ∀ a, op a e = a) (xs : List α) :
    xs.foldl op e = xs.foldr op e := by
  let : Std.Associative op := ⟨assoc⟩
  let : Std.LawfulIdentity op e := { left_id := left, right_id := right }
  exact List.foldr_eq_foldl.symm

/-- The accumulator form needs only a right identity. -/
theorem associative_accumulator (op : α → α → α) (e : α)
    (assoc : ∀ a b c, op (op a b) c = op a (op b c))
    (right : ∀ a, op a e = a) (xs : List α) (seed : α) :
    xs.foldl op seed = op seed (xs.foldr op e) := by
  let : Std.Associative op := ⟨assoc⟩
  let : Std.LawfulRightIdentity op e := { right_id := right }
  exact List.foldl_eq_apply_foldr

/-- Actual block append using the existing certified difference-list type. -/
def dlistBlocks (blocks : List (List α)) : Batteries.DList α :=
  blocks.foldl (fun d xs => d ++ Batteries.DList.ofList xs) .empty

theorem dlistBlocks_apply (blocks : List (List α)) (tail : List α) :
    (dlistBlocks blocks).apply tail = blocks.flatten ++ tail := by
  have hom := List.foldl_hom (fun d : Batteries.DList α => d.apply)
    (g₁ := fun d xs => d ++ Batteries.DList.ofList xs)
    (g₂ := fun f xs => fun ys => f (xs ++ ys))
    (l := blocks) (init := Batteries.DList.empty)
    (by intro d xs; cases d; rfl)
  change (blocks.foldl (fun d xs => d ++ Batteries.DList.ofList xs)
    Batteries.DList.empty).apply tail = _
  rw [← hom]
  exact SquareKit.ListFusion.foldl_append_functions id blocks tail

theorem dlistBlocks_toList (blocks : List (List α)) :
    Batteries.DList.toList (dlistBlocks blocks) = blocks.flatten := by
  have h := dlistBlocks_apply blocks []
  cases hd : dlistBlocks blocks with
  | mk app invariant =>
    rw [Batteries.DList.toList_mk]
    simpa only [hd, List.append_nil] using h

/-- The source function accumulator and actual DList have the same observation
for every tail and every observer, including a different result type. -/
theorem dlistBlocks_observer (observe : List α → β)
    (blocks : List (List α)) (tail : List α) :
    (blocks.foldl (fun f xs => fun ys => f (xs ++ ys)) observe) tail =
      observe ((dlistBlocks blocks).apply tail) := by
  rw [SquareKit.ListFusion.foldl_append_functions, dlistBlocks_apply]

theorem offset_labels :
    (([7, 7, 2] : List Nat).zipIdx 4).map Prod.swap = [(4, 7), (5, 7), (6, 2)] := by
  rw [labels_offset]
  rfl

theorem selector_boundaries :
    ([] : List Nat).tail? = none ∧ [7].tail? = some [] ∧
      init? ([] : List Nat) = none ∧ init? [7] = some [] ∧
      singleton? [7] = some 7 ∧ singleton? [7, 8] = none := by
  decide

theorem signed_boundaries :
    indexSigned ([7, 8] : List Nat) (-1) = none ∧
      indexSigned [7, 8] 0 = some 7 ∧ indexSigned [7, 8] 2 = none ∧
      (([7, 8] : List Nat).take (-1 : Int).toNat,
        ([7, 8] : List Nat).drop (-1 : Int).toNat) = ([], [7, 8]) := by
  refine ⟨indexSigned_negative _ _ (by decide), ?_, ?_, nonpositive_counts _ _ (by decide)⟩
  · exact indexSigned_nat _ 0
  · exact indexSigned_nat _ 2

theorem extrema_and_zip_boundaries :
    ([] : List Nat).max? = none ∧ ([] : List Nat).min? = none ∧
      ([5, 1, 3] : List Nat).max? = some 5 ∧
      ([5, 1, 3] : List Nat).min? = some 1 ∧
      List.zipWith Prod.mk ([1, 2, 3] : List Nat) [true, false] =
        [(1, true), (2, false)] := by decide

/-- Word concatenation demonstrates that the monoid need not commute. -/
theorem ordered_fold (blocks : List (List α)) :
    blocks.foldl (· ++ ·) [] = blocks.foldr (· ++ ·) [] :=
  associative_folds List.append [] List.append_assoc List.nil_append List.append_nil blocks

private def observation (xs : List Nat) : Nat × Option Nat := (xs.length, xs.getLast?)

theorem function_observation :
    (([[1, 2], [], [3]] : List (List Nat)).foldl
      (fun f xs => fun ys => f (xs ++ ys)) observation) [9, 8] = (5, some 8) := by
  rw [SquareKit.ListFusion.foldl_append_functions]
  rfl

theorem actual_dlist_observation :
    observation ((dlistBlocks [[1, 2], [], [3]]).apply [9, 8]) = (5, some 8) := by
  rw [← dlistBlocks_observer observation [[1, 2], [], [3]] [9, 8]]
  exact function_observation

theorem dlist_order_and_empty_blocks :
    (dlistBlocks ([[], [1, 1], [], [2, 1]] : List (List Nat))).apply [9] =
      [1, 1, 2, 1, 9] := by
  rw [dlistBlocks_apply]
  rfl

end Examples.FiniteListInterfaces

import Applications.EditAlignment.Recursive
import Applications.DynamicProgramming.SuffixRow

/-! Actual uncached row folds, refined at every source suffix. -/
set_option autoImplicit false
set_option warningAsError true

namespace EditAlignment
universe u
variable {α : Type u}

theorem lastD_cons_of_ne_nil {β : Type*} (fallback x : β) (xs : List β) (h : xs ≠ []) :
    (x :: xs).getLastD fallback = xs.getLastD fallback := by
  cases xs with
  | nil => contradiction
  | cons y ys => rfl

/-- Literal source row step with Replace, Delete, Insert tie order. -/
def rowStep [DecidableEq α] (y : α) (entry : α × Script α × Script α)
    (row : List (Script α)) : List (Script α) :=
  if entry.1 = y then (.copy entry.1 :: entry.2.2) :: row
  else best (.replace entry.1 y :: entry.2.2)
    (best (.delete entry.1 :: row.headD []) (.insert y :: entry.2.1)) :: row

def firstrow (xs : List α) : List (Script α) := (xs.map Op.delete).tails

def nextrow [DecidableEq α] (xs : List α) (y : α)
    (row : List (Script α)) : List (Script α) :=
  (xs.zip (row.zip row.tail)).foldr (rowStep y) [.insert y :: row.getLastD []]

/-- Recursive presentation of the source fold, including its row boundary. -/
def nextrowRec [DecidableEq α] (xs : List α) (y : α)
    (row : List (Script α)) : List (Script α) :=
  match xs, row with
  | x :: xs, es1 :: es2 :: rest =>
      let next := nextrowRec xs y (es2 :: rest)
      (if x = y then .copy x :: es2
       else best (.replace x y :: es2)
         (best (.delete x :: next.headD []) (.insert y :: es1))) :: next
  | _, _ => [.insert y :: row.getLastD []]

theorem nextrow_eq_rec [DecidableEq α] (xs : List α) (y : α)
    (row : List (Script α)) : nextrow xs y row = nextrowRec xs y row := by
  induction xs generalizing row with
  | nil => rfl
  | cons x xs ih =>
    cases row with
    | nil => rfl
    | cons es1 row =>
      cases row with
      | nil => rfl
      | cons es2 rest =>
        simp only [nextrow, List.tail_cons, List.zip_cons_cons, List.foldr_cons]
        change rowStep y (x, es1, es2) (nextrow xs y (es2 :: rest)) = _
        rw [ih]
        by_cases h : x = y <;> simp [rowStep, nextrowRec, h]

theorem nextrowRec_ne_nil [DecidableEq α] (xs : List α) (y : α)
    (row : List (Script α)) : nextrowRec xs y row ≠ [] := by
  cases xs with
  | nil => simp [nextrowRec]
  | cons x xs =>
    cases row with
    | nil => simp [nextrowRec]
    | cons es row => cases row <;> simp [nextrowRec]

theorem nextrow_ne_nil [DecidableEq α] (xs : List α) (y : α)
    (row : List (Script α)) : nextrow xs y row ≠ [] := by
  rw [nextrow_eq_rec]
  exact nextrowRec_ne_nil xs y row

/-- Reference row indexed by all source suffixes. -/
def modelRow [DecidableEq α] (xs ys : List α) : List (Script α) :=
  xs.tails.map (fun suffix => mce suffix ys)

theorem modelRow_cons [DecidableEq α] (x : α) (xs ys : List α) :
    modelRow (x :: xs) ys = mce (x :: xs) ys :: modelRow xs ys := by
  simp [modelRow]

theorem modelRow_ne_nil [DecidableEq α] (xs ys : List α) : modelRow xs ys ≠ [] :=
  DynamicProgramming.suffixRow_ne_nil _ _

theorem modelRow_length [DecidableEq α] (xs ys : List α) :
    (modelRow xs ys).length = xs.length + 1 :=
  DynamicProgramming.suffixRow_length _ _

theorem modelRow_head [DecidableEq α] (xs ys : List α) :
    (modelRow xs ys).headD [] = mce xs ys :=
  DynamicProgramming.suffixRow_head _ _ _

theorem modelRow_last [DecidableEq α] (xs ys : List α) :
    (modelRow xs ys).getLastD [] = ys.map Op.insert := by
  simpa only [modelRow, mce_nil_left] using
    DynamicProgramming.suffixRow_last (fun suffix => mce suffix ys) xs []

theorem firstrow_eq_model [DecidableEq α] (xs : List α) :
    firstrow xs = modelRow xs [] := by
  induction xs with
  | nil => simp [modelRow, mce_nil_left, firstrow]
  | cons x xs ih =>
    simp only [firstrow, List.map_cons, List.tails_cons]
    change (.delete x :: xs.map Op.delete) :: firstrow xs =
      mce (x :: xs) [] :: modelRow xs []
    rw [ih, mce_nil_right]
    rfl

theorem nextrowRec_eq_model [DecidableEq α] (xs : List α) (y : α) (ys : List α) :
    nextrowRec xs y (modelRow xs ys) = modelRow xs (y :: ys) := by
  induction xs with
  | nil => simp [modelRow, mce_nil_left, nextrowRec]
  | cons x xs ih =>
    have hh := modelRow_head xs ys
    cases he : modelRow xs ys with
    | nil => exact False.elim (modelRow_ne_nil xs ys he)
    | cons es2 rest =>
      have hc : es2 = mce xs ys := by simpa [he] using hh
      rw [he] at ih
      simp only [modelRow_cons]
      rw [he, nextrowRec, ih, hc, modelRow_head]
      by_cases h : x = y
      · subst y
        simp [mce_equal_heads]
      · simp [mce, pick, h]

theorem nextrow_eq_model [DecidableEq α] (xs : List α) (y : α) (ys : List α) :
    nextrow xs y (modelRow xs ys) = modelRow xs (y :: ys) := by
  rw [nextrow_eq_rec, nextrowRec_eq_model]

def editTable [DecidableEq α] (xs ys : List α) : List (Script α) :=
  ys.foldr (nextrow xs) (firstrow xs)

theorem editTable_eq_model [DecidableEq α] (xs ys : List α) :
    editTable xs ys = modelRow xs ys := by
  induction ys with
  | nil => exact firstrow_eq_model xs
  | cons y ys ih =>
    change nextrow xs y (editTable xs ys) = _
    rw [ih, nextrow_eq_model]

theorem editTable_length [DecidableEq α] (xs ys : List α) :
    (editTable xs ys).length = xs.length + 1 := by
  rw [editTable_eq_model, modelRow_length]

theorem editTable_ne_nil [DecidableEq α] (xs ys : List α) : editTable xs ys ≠ [] := by
  rw [editTable_eq_model]
  exact modelRow_ne_nil xs ys

theorem modelRow_entry [DecidableEq α] (xs ys : List α) (i : Nat) (h : i ≤ xs.length) :
    (modelRow xs ys)[i]? = some (mce (xs.drop i) ys) :=
  DynamicProgramming.suffixRow_entry _ _ _ h

theorem editTable_entry [DecidableEq α] (xs ys : List α) (i : Nat) (h : i ≤ xs.length) :
    (editTable xs ys)[i]? = some (mce (xs.drop i) ys) := by
  rw [editTable_eq_model, modelRow_entry xs ys i h]

def mce2 [DecidableEq α] (xs ys : List α) : Script α := (editTable xs ys).headD []

theorem mce2_eq_mce [DecidableEq α] (xs ys : List α) : mce2 xs ys = mce xs ys := by
  rw [mce2, editTable_eq_model, modelRow_head]

theorem mce2_aligns [DecidableEq α] (xs ys : List α) : Aligns (mce2 xs ys) xs ys := by
  rw [mce2_eq_mce]
  exact mce_aligns xs ys

theorem mce2_reconstruct [DecidableEq α] (xs ys : List α) :
    reconstruct (mce2 xs ys) = (xs, ys) := (mce2_aligns xs ys).reconstruct

theorem mce2_optimal [DecidableEq α] (xs ys : List α) (es : Script α)
    (h : reconstruct es = (xs, ys)) : costE (mce2 xs ys) ≤ costE es := by
  rw [mce2_eq_mce]
  exact mce_optimal xs ys es h

theorem mce2_spec [DecidableEq α] (xs ys : List α) : MinimumEdit (mce2 xs ys) xs ys := by
  rw [mce2_eq_mce]
  exact mce_spec xs ys


end EditAlignment

import Applications.EditAlignment.Rows

/-! Cached rows preserve score validity and the source insert/replace/delete policy. -/
set_option autoImplicit false
set_option warningAsError true

namespace EditAlignment
universe u
variable {α : Type u}

theorem costE_best_eq_min (es fs : Script α) :
    costE (best es fs) = min (costE es) (costE fs) := by
  by_cases h : costE es ≤ costE fs
  · simp [best_eq, h]
  · simp [best_eq, h, Nat.min_eq_right (by omega : costE fs ≤ costE es)]

/-- Reference recurrence with the cached source's exact I/R/D tie policy.
This reference is used in proofs, not to compute the cached table. -/
def mceIRD [DecidableEq α] : List α → List α → Script α
  | xs, [] => xs.map Op.delete
  | [], ys => ys.map Op.insert
  | x :: xs, y :: ys =>
      if x = y then .copy x :: mceIRD xs ys
      else best (.insert y :: mceIRD (x :: xs) ys)
        (best (.replace x y :: mceIRD xs ys) (.delete x :: mceIRD xs (y :: ys)))
termination_by xs ys => xs.length + ys.length
decreasing_by all_goals simp only [List.length_cons]; omega

theorem mceIRD_nil_right [DecidableEq α] (xs : List α) :
    mceIRD xs [] = xs.map Op.delete := by simp [mceIRD]

theorem mceIRD_nil_left [DecidableEq α] (ys : List α) :
    mceIRD [] ys = ys.map Op.insert := by cases ys <;> simp [mceIRD]

theorem mceIRD_aligns [DecidableEq α] (xs ys : List α) : Aligns (mceIRD xs ys) xs ys := by
  induction xs generalizing ys with
  | nil => rw [mceIRD_nil_left]; exact aligns_inserts ys
  | cons x xs ihx =>
    induction ys with
    | nil => rw [mceIRD_nil_right]; exact aligns_deletes _
    | cons y ys ihy =>
      rw [mceIRD]
      by_cases h : x = y
      · subst y
        simpa using Aligns.copy x (ihx ys)
      · rw [ite_eq_right h]
        exact aligns_best (.insert y ihy)
          (aligns_best (.replace x y (ihx ys)) (.delete x (ihx (y :: ys))))

/-- Equal optimal value, while retaining the different witness tie policy. -/
theorem mceIRD_cost_eq_mce [DecidableEq α] (xs ys : List α) :
    costE (mceIRD xs ys) = costE (mce xs ys) := by
  induction xs generalizing ys with
  | nil => rw [mceIRD_nil_left, mce_nil_left]
  | cons x xs ihx =>
    induction ys with
    | nil => rw [mceIRD_nil_right, mce_nil_right]
    | cons y ys ihy =>
      by_cases h : x = y
      · subst y
        rw [mceIRD, ite_eq_left rfl, mce_equal_heads]
        simp only [costE_cons, ecost, Nat.zero_add]
        exact ihx ys
      · rw [mceIRD, ite_eq_right h, mce]
        simp only [pick, ite_eq_right h, costE_best_eq_min, costE_cons, ecost]
        rw [ihx ys, ihx (y :: ys), ihy]
        omega

theorem mceIRD_optimal_of_aligns [DecidableEq α] {es : Script α} {xs ys : List α}
    (h : Aligns es xs ys) : costE (mceIRD xs ys) ≤ costE es := by
  rw [mceIRD_cost_eq_mce]
  exact mce_optimal_of_aligns h

theorem mceIRD_spec [DecidableEq α] (xs ys : List α) : MinimumEdit (mceIRD xs ys) xs ys :=
  ⟨mceIRD_aligns xs ys, fun _ h => mceIRD_optimal_of_aligns h⟩

/-- Actual source Pair = (Nat,[Op]). -/
abbrev Pair (α : Type u) := Nat × Script α

def CacheValid (p : Pair α) : Prop := p.1 = costE p.2

/-- Specification encoding of a valid cache, not used by the cached implementation. -/
def cache (es : Script α) : Pair α := (costE es, es)

theorem cache_valid (es : Script α) : CacheValid (cache es) := rfl

/-- Source `cons op (k,es) = (ecost op+k,op:es)`. -/
def cachedCons (op : Op α) (p : Pair α) : Pair α := (ecost op + p.1, op :: p.2)

theorem cachedCons_cache (op : Op α) (es : Script α) :
    cachedCons op (cache es) = cache (op :: es) := by
  simp [cachedCons, cache, costE_cons]

theorem cachedCons_valid (op : Op α) (p : Pair α) (h : CacheValid p) :
    CacheValid (cachedCons op p) := by
  simpa [CacheValid, cachedCons, costE_cons] using congrArg (ecost op + ·) h

/-- Source smaller fst; the first cached pair is retained on equal scores. -/
def cachedBest (p q : Pair α) : Pair α :=
  (Optimization.Thinning.argmin Prod.fst [p, q]).getD p

theorem cachedBest_eq (p q : Pair α) :
    cachedBest p q = if p.1 ≤ q.1 then p else q := by
  simp [cachedBest, Optimization.Thinning.argmin]


theorem cachedBest_tie_left (p q : Pair α) (h : p.1 = q.1) : cachedBest p q = p := by
  simp [cachedBest_eq, h]

theorem cachedBest_cache (es fs : Script α) :
    cachedBest (cache es) (cache fs) = cache (best es fs) := by
  by_cases h : costE es ≤ costE fs <;> simp [cachedBest_eq, cache, best_eq, h]

theorem cachedBest_valid (p q : Pair α) (hp : CacheValid p) (hq : CacheValid q) :
    CacheValid (cachedBest p q) := by
  rw [cachedBest_eq]
  split <;> assumption

/-- Actual source firstrow3, constructed by a right fold of cached deletions. -/
def firstrow3 (xs : List α) : List (Pair α) :=
  xs.foldr (fun x row => cachedCons (.delete x) (row.headD (0, [])) :: row) [(0, [])]

/-- Literal nextrow3 cell: Copy shortcut or Insert/Replace/Delete right-fold minimum. -/
def rowStep3 [DecidableEq α] (y : α) (entry : α × Pair α × Pair α)
    (row : List (Pair α)) : List (Pair α) :=
  if entry.1 = y then cachedCons (.copy entry.1) entry.2.2 :: row
  else cachedBest (cachedCons (.insert y) entry.2.1)
    (cachedBest (cachedCons (.replace entry.1 y) entry.2.2)
      (cachedCons (.delete entry.1) (row.headD (0, [])))) :: row

def nextrow3 [DecidableEq α] (xs : List α) (y : α) (row : List (Pair α)) : List (Pair α) :=
  (xs.zip (row.zip row.tail)).foldr (rowStep3 y) [cachedCons (.insert y) (row.getLastD (0, []))]

/-- Structural presentation for proving the literal source fold invariant. -/
def nextrow3Rec [DecidableEq α] (xs : List α) (y : α) (row : List (Pair α)) : List (Pair α) :=
  match xs, row with
  | x :: xs, es1 :: es2 :: rest =>
      let next := nextrow3Rec xs y (es2 :: rest)
      (if x = y then cachedCons (.copy x) es2
       else cachedBest (cachedCons (.insert y) es1)
         (cachedBest (cachedCons (.replace x y) es2)
           (cachedCons (.delete x) (next.headD (0, []))))) :: next
  | _, _ => [cachedCons (.insert y) (row.getLastD (0, []))]

theorem nextrow3_eq_rec [DecidableEq α] (xs : List α) (y : α) (row : List (Pair α)) :
    nextrow3 xs y row = nextrow3Rec xs y row := by
  induction xs generalizing row with
  | nil => rfl
  | cons x xs ih =>
    cases row with
    | nil => rfl
    | cons es1 row =>
      cases row with
      | nil => rfl
      | cons es2 rest =>
        simp only [nextrow3, List.tail_cons, List.zip_cons_cons, List.foldr_cons]
        change rowStep3 y (x, es1, es2) (nextrow3 xs y (es2 :: rest)) = _
        rw [ih]
        by_cases h : x = y <;> simp [rowStep3, nextrow3Rec, h]

theorem nextrow3Rec_ne_nil [DecidableEq α] (xs : List α) (y : α) (row : List (Pair α)) :
    nextrow3Rec xs y row ≠ [] := by
  cases xs with
  | nil => simp [nextrow3Rec]
  | cons x xs =>
    cases row with
    | nil => simp [nextrow3Rec]
    | cons es row => cases row <;> simp [nextrow3Rec]

/-- Exact suffix-row specification, with the source I/R/D witness cached at every entry. -/
def modelRow3 [DecidableEq α] (xs ys : List α) : List (Pair α) :=
  xs.tails.map (fun suffix => cache (mceIRD suffix ys))

theorem modelRow3_cons [DecidableEq α] (x : α) (xs ys : List α) :
    modelRow3 (x :: xs) ys = cache (mceIRD (x :: xs) ys) :: modelRow3 xs ys := by
  simp [modelRow3]

theorem modelRow3_ne_nil [DecidableEq α] (xs ys : List α) : modelRow3 xs ys ≠ [] :=
  DynamicProgramming.suffixRow_ne_nil _ _

theorem modelRow3_length [DecidableEq α] (xs ys : List α) :
    (modelRow3 xs ys).length = xs.length + 1 :=
  DynamicProgramming.suffixRow_length _ _

theorem modelRow3_head [DecidableEq α] (xs ys : List α) :
    (modelRow3 xs ys).headD (0, []) = cache (mceIRD xs ys) :=
  DynamicProgramming.suffixRow_head _ _ _

theorem modelRow3_last [DecidableEq α] (xs ys : List α) :
    (modelRow3 xs ys).getLastD (0, []) = cache (ys.map Op.insert) := by
  simpa only [modelRow3, mceIRD_nil_left] using
    DynamicProgramming.suffixRow_last (fun suffix => cache (mceIRD suffix ys)) xs (0, [])

theorem modelRow3_valid [DecidableEq α] (xs ys : List α) :
    ∀ p ∈ modelRow3 xs ys, CacheValid p := by
  intro p hp
  obtain ⟨suffix, _, rfl⟩ := List.mem_map.mp hp
  exact cache_valid _

theorem firstrow3_eq_model [DecidableEq α] (xs : List α) : firstrow3 xs = modelRow3 xs [] := by
  induction xs with
  | nil => simp [modelRow3, mceIRD_nil_left, firstrow3, cache, cachedCons, ecost, costE]
  | cons x xs ih =>
    change cachedCons (.delete x) ((firstrow3 xs).headD (0, [])) :: firstrow3 xs =
      cache (mceIRD (x :: xs) []) :: modelRow3 xs []
    rw [ih, modelRow3_head, cachedCons_cache]
    simp [mceIRD_nil_right]

theorem nextrow3Rec_eq_model [DecidableEq α] (xs : List α) (y : α) (ys : List α) :
    nextrow3Rec xs y (modelRow3 xs ys) = modelRow3 xs (y :: ys) := by
  induction xs with
  | nil => simp [modelRow3, mceIRD_nil_left, nextrow3Rec, cachedCons_cache]
  | cons x xs ih =>
    have hh := modelRow3_head xs ys
    cases he : modelRow3 xs ys with
    | nil => exact False.elim (modelRow3_ne_nil xs ys he)
    | cons es2 rest =>
      have hc : es2 = cache (mceIRD xs ys) := by simpa [he] using hh
      rw [he] at ih
      simp only [modelRow3_cons]
      rw [he, nextrow3Rec, ih, hc, modelRow3_head]
      by_cases h : x = y <;> simp [mceIRD, h, cachedCons_cache, cachedBest_cache]

theorem nextrow3_eq_model [DecidableEq α] (xs : List α) (y : α) (ys : List α) :
    nextrow3 xs y (modelRow3 xs ys) = modelRow3 xs (y :: ys) := by
  rw [nextrow3_eq_rec, nextrow3Rec_eq_model]

def editTable3 [DecidableEq α] (xs ys : List α) : List (Pair α) :=
  ys.foldr (nextrow3 xs) (firstrow3 xs)

theorem editTable3_eq_model [DecidableEq α] (xs ys : List α) :
    editTable3 xs ys = modelRow3 xs ys := by
  induction ys with
  | nil => exact firstrow3_eq_model xs
  | cons y ys ih =>
    change nextrow3 xs y (editTable3 xs ys) = _
    rw [ih, nextrow3_eq_model]

theorem editTable3_length [DecidableEq α] (xs ys : List α) :
    (editTable3 xs ys).length = xs.length + 1 := by
  rw [editTable3_eq_model, modelRow3_length]

theorem editTable3_ne_nil [DecidableEq α] (xs ys : List α) : editTable3 xs ys ≠ [] := by
  rw [editTable3_eq_model]
  exact modelRow3_ne_nil xs ys

theorem editTable3_cache_valid [DecidableEq α] (xs ys : List α) :
    ∀ p ∈ editTable3 xs ys, CacheValid p := by
  rw [editTable3_eq_model]
  exact modelRow3_valid xs ys

theorem modelRow3_entry [DecidableEq α] (xs ys : List α) (i : Nat) (h : i ≤ xs.length) :
    (modelRow3 xs ys)[i]? = some (cache (mceIRD (xs.drop i) ys)) :=
  DynamicProgramming.suffixRow_entry _ _ _ h

theorem editTable3_entry [DecidableEq α] (xs ys : List α) (i : Nat) (h : i ≤ xs.length) :
    (editTable3 xs ys)[i]? = some (cache (mceIRD (xs.drop i) ys)) := by
  rw [editTable3_eq_model, modelRow3_entry xs ys i h]

def mce3Result [DecidableEq α] (xs ys : List α) : Pair α := (editTable3 xs ys).headD (0, [])

def mce3 [DecidableEq α] (xs ys : List α) : Script α := (mce3Result xs ys).2

theorem mce3Result_eq [DecidableEq α] (xs ys : List α) :
    mce3Result xs ys = cache (mceIRD xs ys) := by
  rw [mce3Result, editTable3_eq_model, modelRow3_head]

/-- Exact witness correspondence is to the matching I/R/D recurrence. -/
theorem mce3_eq_mceIRD [DecidableEq α] (xs ys : List α) : mce3 xs ys = mceIRD xs ys := by
  rw [mce3, mce3Result_eq]
  rfl

theorem mce3_cache_correct [DecidableEq α] (xs ys : List α) :
    (mce3Result xs ys).1 = costE (mce3 xs ys) := by
  rw [mce3Result_eq, mce3_eq_mceIRD]
  rfl

theorem mce3_aligns [DecidableEq α] (xs ys : List α) : Aligns (mce3 xs ys) xs ys := by
  rw [mce3_eq_mceIRD]
  exact mceIRD_aligns xs ys

theorem mce3_reconstruct [DecidableEq α] (xs ys : List α) :
    reconstruct (mce3 xs ys) = (xs, ys) := (mce3_aligns xs ys).reconstruct

theorem mce3_cost_eq_mce [DecidableEq α] (xs ys : List α) :
    costE (mce3 xs ys) = costE (mce xs ys) := by
  rw [mce3_eq_mceIRD, mceIRD_cost_eq_mce]

theorem mce3_cost_eq_mce2 [DecidableEq α] (xs ys : List α) :
    costE (mce3 xs ys) = costE (mce2 xs ys) := by
  rw [mce2_eq_mce, mce3_cost_eq_mce]

theorem mce3_optimal [DecidableEq α] (xs ys : List α) (es : Script α)
    (h : reconstruct es = (xs, ys)) : costE (mce3 xs ys) ≤ costE es := by
  rw [mce3_cost_eq_mce]
  exact mce_optimal xs ys es h

theorem mce3_spec [DecidableEq α] (xs ys : List α) : MinimumEdit (mce3 xs ys) xs ys := by
  rw [mce3_eq_mceIRD]
  exact mceIRD_spec xs ys


end EditAlignment

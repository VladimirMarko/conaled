import Applications.Optimization.SelectionSpec

namespace Bracketing
variable {α : Type}

inductive Tree (α : Type) where
  | leaf : α → Tree α
  | fork : Tree α → Tree α → Tree α
  deriving DecidableEq, Repr

/-- Independent ordered-fringe specification, using concatenation. -/
def fringeSpec : Tree α → List α
  | .leaf x => [x]
  | .fork l r => fringeSpec l ++ fringeSpec r

/-- The accumulator helper of the source fringe at original LINE 1360. -/
def fringeAcc : Tree α → List α → List α
  | .leaf x, xs => x :: xs
  | .fork l r, xs => fringeAcc l (fringeAcc r xs)

def fringe (t : Tree α) : List α := fringeAcc t []

theorem fringeAcc_eq (t : Tree α) (xs : List α) :
    fringeAcc t xs = fringeSpec t ++ xs := by
  induction t generalizing xs with
  | leaf x => rfl
  | fork l r ihl ihr => simp [fringeAcc, fringeSpec, ihl, ihr, List.append_assoc]

theorem fringe_eq_fringeSpec (t : Tree α) : fringe t = fringeSpec t := by
  simp [fringe, fringeAcc_eq]

/-- The source size counts leaves. It is not the number of all tree nodes. -/
def size : Tree α → Nat
  | .leaf _ => 1
  | .fork l r => size l + size r

def forkCount : Tree α → Nat
  | .leaf _ => 0
  | .fork l r => forkCount l + forkCount r + 1

theorem size_pos (t : Tree α) : 0 < size t := by
  induction t with
  | leaf x => exact Nat.zero_lt_succ 0
  | fork l r ihl ihr => simp only [size]; omega

theorem fringeSpec_length (t : Tree α) : (fringeSpec t).length = size t := by
  induction t with
  | leaf x => rfl
  | fork l r ihl ihr => simp [fringeSpec, size, ihl, ihr]

theorem fringeSpec_ne_nil (t : Tree α) : fringeSpec t ≠ [] := by
  intro h
  have hp := size_pos t
  have he := fringeSpec_length t
  simp [h] at he
  omega

theorem forkCount_add_one (t : Tree α) : forkCount t + 1 = size t := by
  induction t with
  | leaf x => rfl
  | fork l r ihl ihr => simp only [forkCount, size]; omega

/-- Ordered nonempty cuts. The empty branch is a declared totalization. -/
def splitsn : List α → List (List α × List α)
  | [] => []
  | [_] => []
  | x :: y :: xs =>
      ([x], y :: xs) :: (splitsn (y :: xs)).map (fun p => (x :: p.1, p.2))

theorem mem_splitsn_iff (ws us vs : List α) :
    (us, vs) ∈ splitsn ws ↔ us ≠ [] ∧ vs ≠ [] ∧ us ++ vs = ws := by
  induction ws generalizing us vs with
  | nil =>
    constructor
    · simp [splitsn]
    · rintro ⟨hu, _, he⟩
      exact False.elim (hu (List.append_eq_nil_iff.mp he).1)
  | cons x ws ih =>
    cases ws with
    | nil =>
      constructor
      · simp [splitsn]
      · rintro ⟨hu, hv, he⟩
        have hlu : 0 < us.length := List.length_pos_iff.mpr hu
        have hlv : 0 < vs.length := List.length_pos_iff.mpr hv
        have hl := congrArg List.length he
        simp only [List.length_append, List.length_singleton] at hl
        omega
    | cons y ws =>
      rw [splitsn, List.mem_cons, List.mem_map]
      constructor
      · intro h
        rcases h with h | ⟨⟨as, bs⟩, hm, he⟩
        · cases h
          simp
        · cases he
          obtain ⟨_, hb, hab⟩ := (ih as bs).mp hm
          exact ⟨by simp, hb, by simp [hab]⟩
      · rintro ⟨hu, hv, he⟩
        cases us with
        | nil => contradiction
        | cons u us =>
          simp only [List.cons_append, List.cons.injEq] at he
          obtain ⟨rfl, he⟩ := he
          cases us with
          | nil =>
            simp only [List.nil_append] at he
            exact Or.inl (by cases he; rfl)
          | cons a as =>
            apply Or.inr
            exact ⟨(a :: as, vs), (ih _ _).mpr ⟨by simp, hv, he⟩, rfl⟩

theorem splitsn_lengths_lt {ws us vs : List α} (h : (us, vs) ∈ splitsn ws) :
    us.length < ws.length ∧ vs.length < ws.length := by
  obtain ⟨hu, hv, he⟩ := (mem_splitsn_iff ws us vs).mp h
  have hlu : 0 < us.length := List.length_pos_iff.mpr hu
  have hlv : 0 < vs.length := List.length_pos_iff.mpr hv
  have hl := congrArg List.length he
  simp only [List.length_append] at hl
  omega

/-- Exact cut order, expressed independently by increasing cut positions. -/
theorem splitsn_eq_cuts (ws : List α) :
    splitsn ws = (List.range (ws.length - 1)).map
      (fun k => (ws.take (k + 1), ws.drop (k + 1))) := by
  induction ws with
  | nil => rfl
  | cons x ws ih =>
    cases ws with
    | nil => rfl
    | cons y ys =>
      simp only [splitsn, List.length_cons, Nat.add_sub_cancel] at ih ⊢
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, List.take_succ_cons, List.take_zero,
        List.drop_succ_cons, List.drop_zero]
      rw [ih]
      simp only [List.map_map, Function.comp_def, Nat.succ_eq_add_one]

/-- Literal source smaller: an equal score retains the left argument. -/
def sourceSmaller (score : α → Nat) (x y : α) : α :=
  if score x ≤ score y then x else y

/-- Literal foldr1 minimum, with its nonempty source domain explicit. -/
def sourceMinWith (score : α → Nat) : (xs : List α) → xs ≠ [] → α
  | [], h => False.elim (h rfl)
  | [x], _ => x
  | x :: y :: ys, _ => sourceSmaller score x (sourceMinWith score (y :: ys) (by simp))

/-- Independent first-minimum contract, retaining the first occurrence on ties. -/
abbrev FirstMinimum (score : α → Nat) (xs : List α) (a : α) : Prop :=
  Optimization.FirstMinimum score xs a

theorem FirstMinimum.mem {score : α → Nat} {xs : List α} {a : α}
    (h : FirstMinimum score xs a) : a ∈ xs := by
  obtain ⟨before, after, rfl, _, _⟩ := h
  simp

theorem FirstMinimum.le {score : α → Nat} {xs : List α} {a : α}
    (h : FirstMinimum score xs a) (b : α) (hb : b ∈ xs) : score a ≤ score b := by
  obtain ⟨before, after, rfl, hbefore, hafter⟩ := h
  simp only [List.mem_append, List.mem_cons] at hb
  rcases hb with hb | rfl | hb
  · exact Nat.le_of_lt (hbefore b hb)
  · exact Nat.le_refl _
  · exact hafter b hb

theorem sourceMinWith_singleton (score : α → Nat) (x : α) (h : [x] ≠ []) :
    sourceMinWith score [x] h = x := rfl

theorem sourceMinWith_cons_cons (score : α → Nat) (x y : α) (ys : List α)
    (h : x :: y :: ys ≠ []) :
    sourceMinWith score (x :: y :: ys) h =
      sourceSmaller score x (sourceMinWith score (y :: ys) (by simp)) := rfl

theorem sourceMinWith_first (score : α → Nat) (xs : List α) (h : xs ≠ []) :
    FirstMinimum score xs (sourceMinWith score xs h) := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil => exact ⟨[], [], rfl, by simp, by simp⟩
    | cons y ys =>
      have ht := ih (by simp)
      rw [sourceMinWith_cons_cons, sourceSmaller]
      split
      · rename_i hle
        refine ⟨[], y :: ys, rfl, by simp, ?_⟩
        intro b hb
        exact Nat.le_trans hle (ht.le b hb)
      · rename_i hnot
        obtain ⟨before, after, he, hbefore, hafter⟩ := ht
        refine ⟨x :: before, after, ?_, ?_, hafter⟩
        · exact congrArg (List.cons x) he
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · omega
        · exact hbefore b hb

theorem sourceMinWith_mem (score : α → Nat) (xs : List α) (h : xs ≠ []) :
    sourceMinWith score xs h ∈ xs := (sourceMinWith_first score xs h).mem

theorem sourceMinWith_le (score : α → Nat) (xs : List α) (h : xs ≠ [])
    (b : α) (hb : b ∈ xs) : score (sourceMinWith score xs h) ≤ score b :=
  (sourceMinWith_first score xs h).le b hb

theorem splitsn_ne_nil_of_length (ws : List α) (h : 2 ≤ ws.length) :
    splitsn ws ≠ [] := by
  cases ws with
  | nil => simp at h
  | cons x xs =>
    cases xs with
    | nil => simp at h
    | cons y ys => simp [splitsn]


end Bracketing

namespace Bracketing
variable {α β : Type}

theorem sourceMinWith_map (score : β → Nat) (p : α → β) (xs : List α)
    (hn : xs ≠ []) (hm : xs.map p ≠ []) :
    sourceMinWith score (xs.map p) hm =
      p (sourceMinWith (fun a => score (p a)) xs hn) := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      change sourceSmaller score (p x) (sourceMinWith score ((y :: ys).map p) _) =
        p (sourceSmaller (fun a => score (p a)) x (sourceMinWith (fun a => score (p a)) (y :: ys) _))
      rw [ih (by simp) (by simp)]
      unfold sourceSmaller
      split <;> rfl

theorem sourceMinWith_congr (score : α → Nat) (xs ys : List α)
    (hx : xs ≠ []) (hy : ys ≠ []) (he : xs = ys) :
    sourceMinWith score xs hx = sourceMinWith score ys hy := by
  cases he
  rfl
end Bracketing

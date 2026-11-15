import Mathlib.Data.List.SplitLengths
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Multiset.AddSub

/-!
The source chopping operation as a value adapter to List.splitLengths.

Natural ceiling division supplies the chunk count, including the source's
zero-size convention. The positive-size equation is the take/drop recursion
used in FDSA Chapter 3. This reference value definition is not an execution
cost model: a measured source realization must account for its own traversals.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Sequences.Chunks
universe u
variable {α : Type u}

/-- Consecutive chunks of size at most d, with a short final chunk retained.
At size zero the source result is empty, even for nonempty input. -/
def chop (d : Nat) (xs : List α) : List (List α) :=
  (List.replicate (xs.length ⌈/⌉ d) d).splitLengths xs

@[simp] theorem chop_zero (xs : List α) : chop 0 xs = [] := by
  simp [chop]

@[simp] theorem chop_nil (d : Nat) : chop d ([] : List α) = [] := by
  simp [chop]

@[simp] theorem length_chop (d : Nat) (xs : List α) :
    (chop d xs).length = xs.length ⌈/⌉ d := by simp [chop]

private theorem ceilDiv_sub_add_one (n d : Nat) (hn : 0 < n) (hd : 0 < d) :
    n ⌈/⌉ d = (n - d) ⌈/⌉ d + 1 := by
  have hcover : n ≤ d * (n ⌈/⌉ d) := (ceilDiv_le_iff_le_mul hd).mp le_rfl
  have hpos : 0 < n ⌈/⌉ d := by
    by_contra h
    have he : n ⌈/⌉ d = 0 := by omega
    simp only [he, Nat.mul_zero] at hcover
    omega
  apply Nat.le_antisymm
  · apply (ceilDiv_le_iff_le_mul hd).mpr
    have htail : n - d ≤ d * ((n - d) ⌈/⌉ d) :=
      (ceilDiv_le_iff_le_mul hd).mp le_rfl
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · have hmul : d * (n ⌈/⌉ d - 1) + d = d * (n ⌈/⌉ d) := by
      calc
        d * (n ⌈/⌉ d - 1) + d = d * (n ⌈/⌉ d - 1 + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
        _ = d * (n ⌈/⌉ d) := by congr 1; omega
    have htail : (n - d) ⌈/⌉ d ≤ n ⌈/⌉ d - 1 := by
      apply (ceilDiv_le_iff_le_mul hd).mpr
      omega
    omega

/-- Exact positive-size source equation, derived from the standard adapter. -/
theorem chop_eq_cons (d : Nat) (xs : List α) (hd : 0 < d) (hx : xs ≠ []) :
    chop d xs = xs.take d :: chop d (xs.drop d) := by
  have hn : 0 < xs.length := Nat.pos_of_ne_zero (fun h => hx (List.length_eq_zero_iff.mp h))
  simp only [chop, ceilDiv_sub_add_one xs.length d hn hd,
    List.replicate_succ, List.splitLengths_cons, List.length_drop]

theorem chop_eq_nil_iff (d : Nat) (xs : List α) : chop d xs = [] ↔ d = 0 ∨ xs = [] := by
  constructor
  · intro h
    by_cases hd : d = 0
    · exact Or.inl hd
    · right
      by_contra hx
      rw [chop_eq_cons d xs (Nat.pos_of_ne_zero hd) hx] at h
      simp at h
  · rintro (rfl | rfl) <;> simp

theorem drop_length_lt (d : Nat) (xs : List α) (hd : 0 < d) (hx : xs ≠ []) :
    (xs.drop d).length < xs.length := by
  have hn : 0 < xs.length := Nat.pos_of_ne_zero (fun h => hx (List.length_eq_zero_iff.mp h))
  simp only [List.length_drop]
  omega

theorem chop_mem_ne_nil (d : Nat) (xs ys : List α) (hy : ys ∈ chop d xs) : ys ≠ [] := by
  by_cases hd : d = 0
  · simp [hd] at hy
  by_cases hx : xs = []
  · simp [hx] at hy
  rw [chop_eq_cons d xs (Nat.pos_of_ne_zero hd) hx] at hy
  rcases List.mem_cons.mp hy with rfl | hy
  · intro he
    have hl := congrArg List.length he
    have hn : 0 < xs.length := Nat.pos_of_ne_zero (fun h => hx (List.length_eq_zero_iff.mp h))
    simp only [List.length_take, List.length_nil] at hl
    omega
  · exact chop_mem_ne_nil d (xs.drop d) ys hy
termination_by xs.length
decreasing_by exact drop_length_lt d xs (Nat.pos_of_ne_zero hd) hx

theorem length_mem_chop (d : Nat) (xs ys : List α) (hy : ys ∈ chop d xs) :
    ys.length ≤ d := by
  apply List.length_mem_splitLengths xs (List.replicate (xs.length ⌈/⌉ d) d) d
    (fun n hn => ?_) ys hy
  exact le_of_eq (List.mem_replicate.mp hn).2

/-- This characterizes the exact natural ceiling, rather than truncating a
natural quotient before applying a ceiling. -/
theorem length_chop_le_iff (d : Nat) (xs : List α) (hd : 0 < d) (k : Nat) :
    (chop d xs).length ≤ k ↔ xs.length ≤ d * k := by
  rw [length_chop, ceilDiv_le_iff_le_mul hd]

theorem length_chop_eq_add_pred_div (d : Nat) (xs : List α) :
    (chop d xs).length = (xs.length + d - 1) / d := by
  rw [length_chop, Nat.ceilDiv_eq_add_pred_div]

theorem length_chop_le (d : Nat) (xs : List α) : (chop d xs).length ≤ xs.length := by
  by_cases hd : d = 0
  · simp [hd]
  apply (length_chop_le_iff d xs (Nat.pos_of_ne_zero hd) xs.length).mpr
  calc
    xs.length = 1 * xs.length := by simp
    _ ≤ d * xs.length := Nat.mul_le_mul_right xs.length (by omega)

/-- The last partial chunk is retained, so flattening loses no occurrence. -/
theorem flatten_chop (d : Nat) (xs : List α) (hd : 0 < d) : (chop d xs).flatten = xs := by
  apply List.flatten_splitLengths
  have h : xs.length ≤ d * (xs.length ⌈/⌉ d) := (ceilDiv_le_iff_le_mul hd).mp le_rfl
  simpa only [List.sum_replicate_nat, Nat.mul_comm] using h

theorem countP_chop (d : Nat) (xs : List α) (hd : 0 < d) (p : α → Bool) :
    ((chop d xs).map (List.countP p)).sum = xs.countP p := by
  rw [← List.countP_flatten, flatten_chop d xs hd]

theorem sum_multiset_chop (d : Nat) (xs : List α) (hd : 0 < d) :
    ((chop d xs).map (fun ys : List α => (ys : Multiset α))).sum = (xs : Multiset α) := by
  have h (xss : List (List α)) :
      (xss.map (fun ys : List α => (ys : Multiset α))).sum = (xss.flatten : Multiset α) := by
    induction xss with
    | nil => rfl
    | cons ys xss ih =>
      simp only [List.map_cons, List.sum_cons, List.flatten_cons, ih, Multiset.coe_add]
  rw [h, flatten_chop d xs hd]

theorem mem_chop_iff (d : Nat) (xs : List α) (hd : 0 < d) (x : α) :
    (∃ ys ∈ chop d xs, x ∈ ys) ↔ x ∈ xs := by
  rw [← List.mem_flatten, flatten_chop d xs hd]

theorem mem_of_mem_chop {d : Nat} {xs ys : List α} {x : α}
    (hy : ys ∈ chop d xs) (hx : x ∈ ys) : x ∈ xs := by
  by_cases hd : d = 0
  · simp [hd] at hy
  exact (mem_chop_iff d xs (Nat.pos_of_ne_zero hd) x).mp ⟨ys, hy, hx⟩

theorem chop_eq_singleton (d : Nat) (xs : List α) (hd : 0 < d) (hx : xs ≠ [])
    (hl : xs.length ≤ d) : chop d xs = [xs] := by
  rw [chop_eq_cons d xs hd hx, List.take_of_length_le hl,
    List.drop_eq_nil_of_le hl, chop_nil]

/-- Alignment is necessary: the boundary between xs and ys is a chunk boundary
when d divides the length of xs. -/
theorem chop_append (d : Nat) (xs ys : List α) (hd : 0 < d) (ha : d ∣ xs.length) :
    chop d (xs ++ ys) = chop d xs ++ chop d ys := by
  by_cases hx : xs = []
  · simp [hx]
  have hn : 0 < xs.length := Nat.pos_of_ne_zero (fun h => hx (List.length_eq_zero_iff.mp h))
  have hdl : d ≤ xs.length := Nat.le_of_dvd hn ha
  have hxy : xs ++ ys ≠ [] := by
    intro he
    exact hx (List.append_eq_nil_iff.mp he).1
  rw [chop_eq_cons d (xs ++ ys) hd hxy, List.take_append_of_le_length hdl,
    List.drop_append_of_le_length hdl, chop_eq_cons d xs hd hx, List.cons_append]
  congr 1
  apply chop_append d (xs.drop d) ys hd
  simpa only [List.length_drop] using Nat.dvd_sub ha (Nat.dvd_refl d)
termination_by xs.length
decreasing_by exact drop_length_lt d xs hd hx

theorem chop_flatten (d : Nat) (xss : List (List α)) (hd : 0 < d)
    (hl : ∀ ys ∈ xss, ys.length = d) : chop d xss.flatten = xss := by
  induction xss with
  | nil => simp
  | cons ys xss ih =>
    have hy : ys.length = d := hl ys (by simp)
    have hn : ys ≠ [] := by
      intro he
      simp only [he, List.length_nil] at hy
      omega
    have ht : ∀ zs ∈ xss, zs.length = d := fun zs hz => hl zs (by simp [hz])
    rw [List.flatten_cons, chop_append d ys xss.flatten hd (by simp [hy]),
      chop_eq_singleton d ys hd hn (by omega), ih ht]
    rfl

theorem chop_replicate_blocks (d : Nat) (xs : List α) (n : Nat)
    (hd : 0 < d) (hl : xs.length = d) :
    chop d (List.replicate n xs).flatten = List.replicate n xs := by
  apply chop_flatten d _ hd
  intro ys hy
  have he : ys = xs := (List.mem_replicate.mp hy).2
  simpa only [he] using hl

theorem chop_replicate (d n : Nat) (a : α) (hd : 0 < d) :
    chop d (List.replicate (n * d) a) = List.replicate n (List.replicate d a) := by
  rw [← List.flatten_replicate_replicate]
  exact chop_replicate_blocks d _ n hd (by simp)

theorem chop_one (xs : List α) : chop 1 xs = xs.map (fun x => [x]) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [chop_eq_cons 1 (x :: xs) (by decide) (by simp)]
    simpa only [List.take_succ_cons, List.take_zero, List.drop_succ_cons,
      List.drop_zero, List.map_cons] using congrArg (List.cons [x]) ih

end Applications.Sequences.Chunks

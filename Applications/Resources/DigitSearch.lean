import Applications.Resources.ListFusion
import SquareKit.FiniteSums
import Mathlib.Data.List.Pi
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Pi

/-! Actual first-hit inspection and its finite-uniform decimal population. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources.DigitSearch
universe u
variable {α : Type u}

def search (p : α → Bool) : List α → Measured (Option Nat) Nat
  | [] => (none,0)
  | x :: xs => if p x then (some 0,1) else
      let r := search p xs
      (r.1.map (·+1),r.2+1)

theorem search_value (p : α → Bool) (xs : List α) : (search p xs).1 = xs.findIdx? p := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [search, List.findIdx?_cons]; split <;> simp_all

theorem first_spec (p : α → Bool) (xs : List α) (i : Nat) :
    (search p xs).1 = some i ↔ ∃ h : i < xs.length, p xs[i] = true ∧
      ∀ j (hji : j < i), p (xs[j]'(Nat.lt_trans hji h)) = false := by
  rw [search_value, List.findIdx?_eq_some_iff_getElem]
  simp only [Bool.not_eq_true]

theorem none_spec (p : α → Bool) (xs : List α) :
    (search p xs).1 = none ↔ ∀ x ∈ xs, p x = false := by
  rw [search_value, List.findIdx?_eq_none_iff]

theorem search_work (p : α → Bool) (xs : List α) :
    (search p xs).2 = match (search p xs).1 with | none => xs.length | some i => i+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [search]
    split
    · rfl
    · cases h : (search p xs).1 <;> simp_all

theorem work_le (p : α → Bool) (xs : List α) : (search p xs).2 ≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [search]; split <;> simp_all

theorem work_pos (p : α → Bool) (x : α) (xs : List α) : 1 ≤ (search p (x::xs)).2 := by
  simp only [search]; split <;> simp_all

theorem no_hit (p : α → Bool) (xs : List α) (h : ∀ x ∈ xs,p x=false) :
    search p xs = (none,xs.length) := by
  have hv := (none_spec p xs).mpr h
  have hw := search_work p xs
  rw [hv] at hw
  exact Prod.ext hv hw

theorem first_hit_suffix (p : α → Bool) (before : List α) (x : α) (after : List α)
    (hf : ∀ y ∈ before,p y=false) (ht : p x=true) :
    search p (before ++ x::after) = (some before.length,before.length+1) := by
  induction before with
  | nil => simp [search,ht]
  | cons y ys ih =>
    have hy := hf y (by simp)
    have hr := ih (fun z hz => hf z (by simp [hz]))
    simp [search,hy,hr]

theorem work_eq_takeWhile (p : α → Bool) (xs : List α) :
    (search p xs).2 = (ListFusion.takeWhile 0 0 1 (fun x => !p x) xs).2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [search,ListFusion.takeWhile,hp,ih]

def signedPosition (r : Option Nat) : Int := r.elim (-1) Int.ofNat

theorem signed_failure (p : α → Bool) (xs : List α) :
    signedPosition (search p xs).1 = -1 ↔ ∀ x ∈ xs,p x=false := by
  rw [← none_spec]
  cases (search p xs).1 <;> simp [signedPosition]

abbrev Digit := Fin 10
def large (d : Digit) : Bool := decide (5 ≤ d.val)
def digits : List Digit := List.finRange 10

theorem digits_complete (d : Digit) : d ∈ digits := List.mem_finRange d
theorem digits_nodup : digits.Nodup := List.nodup_finRange 10

/-- Decode native restricted product functions in the supplied position order. -/
private def decode {ι : Type} (l : List ι) (f : ∀ i, i ∈ l → Digit) : List Digit :=
  l.attach.map (fun i => f i.1 i.2)

private def product {ι : Type} [DecidableEq ι] (l : List ι) : List (List Digit) :=
  (List.pi l (fun _ => digits)).map (decode l)

private theorem decode_cons {ι : Type} [DecidableEq ι] (i : ι) (l : List ι)
    (hi : i ∉ l) (d : Digit) (f : ∀ j, j ∈ l → Digit) :
    decode (i::l) (List.Pi.cons i l d f) = d :: decode l f := by
  simp only [decode,List.attach_cons,List.map_cons,List.map_map,List.cons.injEq]
  constructor
  · simp [List.Pi.cons_def]
  · apply List.map_congr_left
    intro j _
    have hn : j.val ≠ i := by intro he; exact hi (he ▸ j.property)
    simp [List.Pi.cons_def,hn]

private theorem product_cons {ι : Type} [DecidableEq ι] (i : ι) (l : List ι) (hi : i ∉ l) :
    product (i::l) = digits.flatMap (fun d => (product l).map (d::·)) := by
  simp only [product,List.pi_cons,List.map_flatMap,List.map_map]
  congr 1
  funext d
  apply List.map_congr_left
  intro f _
  exact decode_cons i l hi d f

private theorem product_same_length {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    (l : List ι) (r : List κ) (hl : l.Nodup) (hr : r.Nodup) (hlen : l.length=r.length) :
    product l = product r := by
  induction l generalizing r with
  | nil => have he : r=[] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
           subst r; rfl
  | cons i l ih =>
    cases r with
    | nil => simp at hlen
    | cons j r =>
      rw [product_cons i l (List.nodup_cons.mp hl).1, product_cons j r (List.nodup_cons.mp hr).1]
      rw [ih r (List.nodup_cons.mp hl).2 (List.nodup_cons.mp hr).2 (by simpa using hlen)]

/-- Ordered native product population; construction is not charged as search work. -/
def words (n : Nat) : List (List Digit) := product (List.finRange n)

theorem words_zero : words 0 = [[]] := rfl

theorem words_succ (n : Nat) : words (n+1) = digits.flatMap (fun d => (words n).map (d::·)) := by
  unfold words
  rw [List.finRange_succ, product_cons]
  · rw [product_same_length ((List.finRange n).map Fin.succ) (List.finRange n)
      ((List.nodup_finRange n).map (Fin.succ_injective n)) (List.nodup_finRange n) (by simp)]
  · simp


theorem words_spec (n : Nat) (xs : List Digit) : xs ∈ words n ↔ xs.length = n := by
  induction n generalizing xs with
  | zero => simp [words_zero]
  | succ n ih =>
    rw [words_succ]
    simp only [List.mem_flatMap,List.mem_map]
    constructor
    · rintro ⟨d,_,ys,hy,rfl⟩
      simp [(ih ys).mp hy]
    · intro h
      cases xs with
      | nil => simp at h
      | cons d xs => exact ⟨d,digits_complete d,xs,(ih xs).mpr (by simpa using h),rfl⟩

theorem words_nodup (n : Nat) : (words n).Nodup := by
  induction n with
  | zero => simp [words_zero]
  | succ n ih =>
    rw [words_succ]
    change List.Pairwise (· ≠ ·) (digits.flatMap (fun d => (words n).map (d :: ·)))
    apply List.pairwise_flatMap.mpr
    constructor
    · intro d _
      apply List.pairwise_map.mpr
      exact ih.imp (fun {a b} h he => h (List.cons.inj he).2)
    · apply digits_nodup.imp
      intro a b hab x hx y hy he
      obtain ⟨xs,_,rfl⟩ := List.mem_map.mp hx
      obtain ⟨ys,_,rfl⟩ := List.mem_map.mp hy
      exact hab (List.cons.inj he).1

theorem words_length (n : Nat) : (words n).length = 10^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [words_succ,digits,List.length_flatMap,ih,Nat.pow_succ]; omega

/-- Same native population, exposed as total functions on all finite positions. -/
def functions (n : Nat) : List (Fin n → Digit) :=
  (List.pi (List.finRange n) (fun _ => digits)).map (fun f i => f i (List.mem_finRange i))

theorem words_functions (n : Nat) : words n = (functions n).map List.ofFn := by
  simp only [words,product,functions,List.map_map]
  apply List.map_congr_left
  intro f _
  dsimp only [Function.comp_apply]
  rw [List.ofFn_eq_map]
  exact List.attach_map_val (l := List.finRange n) (f := fun i => f i (List.mem_finRange i))

theorem functions_nodup (n : Nat) : (functions n).Nodup := by
  have h := words_nodup n
  rw [words_functions] at h
  exact h.of_map

theorem functions_complete (n : Nat) (f : Fin n → Digit) : f ∈ functions n := by
  apply List.mem_map.mpr
  refine ⟨fun i _ => f i, ?_, rfl⟩
  exact (List.mem_pi _ _).mpr (fun i _ => digits_complete (f i))

theorem functions_univ (n : Nat) : (functions n).toFinset = Finset.univ := by
  ext f
  simp [functions_complete]

def totalCost (n : Nat) : Nat := ((words n).map (fun xs => (search large xs).2)).sum

theorem totalCost_functions (n : Nat) : totalCost n =
    ∑ f : Fin n → Digit, (search large (List.ofFn f)).2 := by
  rw [totalCost,words_functions,List.map_map,← List.sum_toFinset _ (functions_nodup n),functions_univ]
  rfl

theorem sum_cons_cost (d : Digit) (xss : List (List Digit)) :
    (xss.map (fun xs => (search large (d::xs)).2)).sum =
      xss.length + if large d then 0 else (xss.map (fun xs => (search large xs).2)).sum := by
  by_cases hd : large d = true
  · simp [search,hd,List.map_const']
  · have hf : large d = false := Bool.eq_false_iff.mpr hd
    induction xss with
    | nil => simp [hf]
    | cons xs xss ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      have hs : (search large (d::xs)).2 = (search large xs).2+1 := by simp [search,hf]
      rw [hs,ih]
      simp only [hf,Bool.false_eq_true,↓reduceIte]
      omega

theorem totalCost_step (n : Nat) : totalCost (n+1) = 10^(n+1)+5*totalCost n := by
  have hd : digits = [0,1,2,3,4,5,6,7,8,9] := by decide
  simp only [totalCost,words_succ,hd,List.flatMap_cons,List.flatMap_nil,List.map_append,
    List.sum_append,List.map_map,List.append_nil,Function.comp_def]
  rw [sum_cons_cost,sum_cons_cost,sum_cons_cost,sum_cons_cost,sum_cons_cost,
    sum_cons_cost,sum_cons_cost,sum_cons_cost,sum_cons_cost,sum_cons_cost]
  norm_num [large,words_length,pow_succ]
  omega

theorem totalCost_exact (n : Nat) : totalCost n + 2*5^n = 2*10^n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [totalCost_step]; simp only [pow_succ]; nlinarith

/-- Uniform rational mean of actual inspected work, not of a supplied formula. -/
def expected (n : Nat) : ℚ := (totalCost n : ℚ) / ((words n).length : ℚ)

theorem denominator_pos (n : Nat) : 0 < ((words n).length : ℚ) := by
  rw [words_length]; positivity

theorem expected_functions (n : Nat) : expected n =
    (∑ f : Fin n → Digit, ((search large (List.ofFn f)).2 : ℚ)) /
      (Fintype.card (Fin n → Digit) : ℚ) := by
  simp [expected,totalCost_functions,words_length]

theorem expected_closed (n : Nat) : expected n = 2-2/(2:ℚ)^n := by
  have hc := congrArg (fun k : Nat => (k:ℚ)) (totalCost_exact n)
  push_cast at hc
  have hp : (10:ℚ)^n = (2:ℚ)^n*(5:ℚ)^n := by rw [← mul_pow]; norm_num
  have h2 : (2:ℚ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  have h5 : (5:ℚ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  unfold expected
  rw [words_length]
  push_cast
  rw [hp] at hc ⊢
  field_simp
  nlinarith

theorem expected_probability (n : Nat) : expected n = 2*(1-(1/2:ℚ)^n) := by
  rw [expected_closed]
  simp only [div_pow,one_pow]
  ring

theorem expected_error (n : Nat) : 2-expected n = 2/(2:ℚ)^n := by rw [expected_closed]; ring

theorem expected_lt_two (n : Nat) : expected n < 2 := by
  have h : 0 < 2/(2:ℚ)^n := by positivity
  rw [← expected_error] at h
  linarith

theorem weighted_difference (n : Nat) :
    expected n - (∑ k ∈ Finset.Ico 1 (n+1), (k:ℚ)/(2:ℚ)^k) = (n:ℚ)/(2:ℚ)^n := by
  rw [expected_closed,SquareKit.FiniteSums.half_sum_closed]
  ring

theorem weighted_le_expected (n : Nat) :
    (∑ k ∈ Finset.Ico 1 (n+1), (k:ℚ)/(2:ℚ)^k) ≤ expected n := by
  have h : 0 ≤ (n:ℚ)/(2:ℚ)^n := by positivity
  rw [← weighted_difference] at h
  linarith

theorem expected_modulus (ε : ℚ) (he : 0<ε) (n : Nat)
    (hn : 2*((⌈(2/ε:ℚ)⌉:ℤ).natAbs+1) ≤ n) :
    0 < 2-expected n ∧ 2-expected n < ε := by
  have h := (SquareKit.FiniteSums.half_sum_ceiling_modulus ε he n hn).2.1
  have hl := weighted_le_expected n
  have hu := expected_lt_two n
  constructor <;> linarith

theorem expected_tendsto : Filter.Tendsto expected Filter.atTop (nhds (2:ℚ)) := by
  apply (SquareKit.FiniteSums.tendsto_rat_iff_epsilon _ _).2
  intro ε he
  refine ⟨2*((⌈(2/ε:ℚ)⌉:ℤ).natAbs+1), ?_⟩
  intro n hn
  have h := expected_modulus ε he n hn
  constructor <;> linarith

end Resources.DigitSearch


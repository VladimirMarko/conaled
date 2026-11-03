import Applications.Resources.Potential
import Mathlib.Data.List.Iterate
import Mathlib.Logic.Function.Iterate

/-! Binary writes, independent numeric meaning, and finite source-prefix correspondence.
Provenance and statement review: `docs/research/adwh-potential-accounting.md`. -/
namespace Resources.BinaryCounter
universe u

abbrev Bits := List Bool

/-- The ordinary independent binary place-value interpretation. -/
def value : Bits → Nat
  | [] => 0
  | false :: bs => 2 * value bs
  | true :: bs => 1 + 2 * value bs

/-- Literal increment on the intended 0/1 digit domain. -/
def inc : Bits → Bits
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => false :: inc bs

theorem inc_ne_nil (bs : Bits) : inc bs ≠ [] := by
  cases bs with
  | nil => simp [inc]
  | cons b bs => cases b <;> simp [inc]

theorem value_inc (bs : Bits) : value (inc bs) = value bs + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [inc, value, ih] <;> omega

/-- Canonical binary lists are empty or end in the most significant 1. -/
def Canonical : Bits → Prop
  | [] => True
  | b :: bs => if bs = [] then b = true else Canonical bs

theorem canonical_cons_nonempty (b : Bool) (bs : Bits) (h : bs ≠ []) :
    Canonical (b :: bs) ↔ Canonical bs := by
  simp [Canonical, h]

theorem canonical_inc (bs : Bits) (h : Canonical bs) : Canonical (inc bs) := by
  induction bs with
  | nil => simp [inc, Canonical]
  | cons b bs ih =>
    cases bs with
    | nil => cases b <;> simp [inc, Canonical]
    | cons c cs =>
      have ht : Canonical (c :: cs) :=
        (canonical_cons_nonempty b (c :: cs) (by simp)).mp h
      cases b with
      | false => exact (canonical_cons_nonempty true (c :: cs) (by simp)).mpr ht
      | true =>
        exact (canonical_cons_nonempty false (inc (c :: cs)) (inc_ne_nil _)).mpr
          (ih ht)

theorem value_lt_two_pow_length (bs : Bits) : value bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [value]
  | cons b bs ih =>
    cases b <;> simp only [value, List.length_cons, Nat.pow_succ] <;> omega

/-- Number of transitions; recursion decreases `n`. -/
abbrev advance (n : Nat) (bs : Bits) : Bits := inc^[n] bs

theorem value_advance (n : Nat) (bs : Bits) :
    value (advance n bs) = value bs + n := by
  induction n generalizing bs with
  | zero => simp [advance]
  | succ n ih =>
    simp only [advance, Function.iterate_succ_apply, ih, value_inc]
    omega

theorem canonical_advance (n : Nat) (bs : Bits) (h : Canonical bs) :
    Canonical (advance n bs) := by
  induction n generalizing bs with
  | zero => exact h
  | succ n ih => exact ih (inc bs) (canonical_inc bs h)

/-- Finite observational meaning of `take n (iterate f x)`. -/
abbrev iteratePrefix {α : Type u} (f : α → α) (n : Nat) (x : α) := List.iterate f x n

/-- Source `bits`, with a natural rather than a machine-integer count. -/
def bits (n : Nat) : List Bits := iteratePrefix inc n []

theorem length_iteratePrefix {α : Type u} (f : α → α) (n : Nat) (x : α) :
    (iteratePrefix f n x).length = n := by
  exact List.length_iterate f x n

theorem length_bits (n : Nat) : (bits n).length = n :=
  length_iteratePrefix inc n []

theorem getElem?_iteratePrefix_inc (n k : Nat) (bs : Bits) :
    (iteratePrefix inc n bs)[k]? =
      if k < n then some (advance k bs) else none := by
  split
  · exact List.getElem?_iterate inc bs n k ‹_›
  · apply List.getElem?_eq_none
    simpa using Nat.le_of_not_gt ‹¬ k < n›

theorem values_iteratePrefix (n : Nat) (bs : Bits) :
    (iteratePrefix inc n bs).map value = List.range' (value bs) n := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih => simp [iteratePrefix, List.iterate, ih, value_inc, List.range'_succ]

/-- Independent output specification: the exact numeric sequence 0,...,n-1. -/
theorem bits_values (n : Nat) : (bits n).map value = List.range n := by
  simpa [bits, value, List.range_eq_range'] using values_iteratePrefix n []

theorem bits_canonical (n : Nat) (bs : Bits) (h : bs ∈ bits n) : Canonical bs := by
  obtain ⟨k, _, rfl⟩ := List.mem_iterate.mp h
  exact canonical_advance k [] trivial

/-- Encoding back to the source's digit type. -/
def encode (bs : Bits) : List Int := bs.map (fun b => if b then 1 else 0)

/-- Three source increment branches; an encountered malformed digit returns `none`.
An uninspected suffix is retained, so `sourceInc [0,2] = some [1,2]`. -/
def sourceInc : List Int → Option (List Int)
  | [] => some [1]
  | b :: bs =>
      if b = 0 then some (1 :: bs)
      else if b = 1 then (sourceInc bs).map (0 :: ·)
      else none

/-- Exact list equality after digit encoding, including the carry branch. -/
theorem sourceInc_encode (bs : Bits) : sourceInc (encode bs) = some (encode (inc bs)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | false => simp [encode, sourceInc, inc]
    | true =>
      change (sourceInc (encode bs)).map (0 :: ·) = some (0 :: encode (inc bs))
      rw [ih]
      rfl

/-- A finite prefix of the source integer-digit iteration. Only transitions
needed to observe the requested states are evaluated. -/
def sourcePrefix : Nat → List Int → Option (List (List Int))
  | 0, _ => some []
  | 1, bs => some [bs]
  | n + 2, bs => do
      let next ← sourceInc bs
      let rest ← sourcePrefix (n + 1) next
      some (bs :: rest)

/-- The whole observed output agrees exactly after encoding, in source order. -/
theorem sourcePrefix_encode (n : Nat) (bs : Bits) :
    sourcePrefix n (encode bs) = some ((iteratePrefix inc n bs).map encode) := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n => simp [sourcePrefix, sourceInc_encode, ih, iteratePrefix]

theorem source_bits_eq (n : Nat) : sourcePrefix n [] = some ((bits n).map encode) := by
  simpa [bits, encode] using sourcePrefix_encode n []

/-- Potential: the total number of one bits, including redundant high bits. -/
def ones : Bits → Nat
  | [] => 0
  | false :: bs => ones bs
  | true :: bs => 1 + ones bs

/-- Number of initial one bits, as in the book's per-increment cost argument. -/
def leadingOnes : Bits → Nat
  | [] => 0
  | false :: _ => 0
  | true :: bs => 1 + leadingOnes bs

/-- One counted write per changed digit, including extension by a final one. -/
def flipCost : Bits → Nat
  | [] => 1
  | false :: _ => 1
  | true :: bs => 1 + flipCost bs

/-- The increment program instrumented at each bit write. -/
def incWithCost : Bits → Bits × Nat
  | [] => ([true], 1)
  | false :: bs => (true :: bs, 1)
  | true :: bs =>
      let result := incWithCost bs
      (false :: result.1, 1 + result.2)

theorem incWithCost_eq (bs : Bits) : incWithCost bs = (inc bs, flipCost bs) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [incWithCost, inc, flipCost, ih]

theorem flipCost_eq_leadingOnes_add_one (bs : Bits) :
    flipCost bs = leadingOnes bs + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [flipCost, leadingOnes, ih, Nat.add_assoc]

theorem ones_le_length (bs : Bits) : ones bs ≤ bs.length := by
  induction bs with
  | nil => simp [ones]
  | cons b bs ih => cases b <;> simp [ones] <;> omega

theorem flipCost_le_length_add_one (bs : Bits) : flipCost bs ≤ bs.length + 1 := by
  induction bs with
  | nil => simp [flipCost]
  | cons b bs ih => cases b <;> simp [flipCost]; omega

/-- Exact per-increment accounting, requiring no canonicality hypothesis. -/
theorem flipCost_potential (bs : Bits) :
    flipCost bs + ones (inc bs) = 2 + ones bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [flipCost, inc, ones] at * <;> omega


/-- Count the source write charges along the actual increment trajectory. -/
def totalCost (n : Nat) (bs : Bits) : Nat :=
  budget (fun (_ : Unit) => incWithCost) (fun _ bs => flipCost bs) (List.replicate n ()) bs

/-- The shared measured executor is the only multi-step implementation. -/
def advanceWithCost (n : Nat) (bs : Bits) : Measured Bits Nat :=
  run (fun (_ : Unit) => incWithCost) (List.replicate n ()) bs

theorem totalCost_zero (bs : Bits) : totalCost 0 bs = 0 := rfl

theorem totalCost_succ (n : Nat) (bs : Bits) :
    totalCost (n + 1) bs = flipCost bs + totalCost n (inc bs) := by
  simp [totalCost, List.replicate_succ, budget, incWithCost_eq]

theorem advanceWithCost_succ (n : Nat) (bs : Bits) :
    advanceWithCost (n + 1) bs = bind (incWithCost bs) (advanceWithCost n) := rfl

theorem advanceWithCost_eq (n : Nat) (bs : Bits) :
    advanceWithCost n bs = (advance n bs, totalCost n bs) := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih =>
    simp [advanceWithCost_succ, bind, incWithCost_eq, ih, totalCost_succ,
      advance, Function.iterate_succ_apply]

theorem counter_run (n : Nat) (bs : Bits) :
    run (fun (_ : Unit) => incWithCost) (List.replicate n ()) bs = advanceWithCost n bs := rfl

theorem counter_potential (n : Nat) (bs : Bits) :
    (advanceWithCost n bs).2 + ones (advanceWithCost n bs).1 = ones bs + 2 * n := by
  have localLaw : ∀ (_ : Unit) bs,
      (incWithCost bs).2 + ones (incWithCost bs).1 = ones bs + 2 := by
    intro _ bs
    simpa [incWithCost_eq, Nat.add_comm] using flipCost_potential bs
  simpa [advanceWithCost, budget_constant] using
    run_potential_exact (fun (_ : Unit) => incWithCost) (fun _ _ => 2) ones localLaw
      (List.replicate n ()) bs

theorem totalCost_potential (n : Nat) (bs : Bits) :
    totalCost n bs + ones (advance n bs) = 2 * n + ones bs := by
  simpa [advanceWithCost_eq, Nat.add_comm] using counter_potential n bs

theorem totalCost_le (n : Nat) (bs : Bits) : totalCost n bs ≤ 2 * n + ones bs := by
  have h := totalCost_potential n bs
  omega

theorem totalCost_from_zero (n : Nat) : totalCost n [] ≤ 2 * n := by
  simpa [ones] using totalCost_le n []

theorem counter_zero_bound (n : Nat) : (advanceWithCost n []).2 ≤ 2 * n := by
  simpa [advanceWithCost_eq] using totalCost_from_zero n

def bitsTransitionCost (n : Nat) : Nat := totalCost (n - 1) []

theorem bitsTransitionCost_bound (n : Nat) : bitsTransitionCost n ≤ 2 * (n - 1) :=
  totalCost_from_zero (n - 1)

def advanceSquare (n : Nat) :=
  erasureSquare (advanceWithCost n) (advance n) (fun bs => congrArg Prod.fst (advanceWithCost_eq n bs))

def numericSquare (n : Nat) :
    Squares.Square ⟨Bits, Nat, value⟩ ⟨Measured Bits Nat, Nat, fun r => value r.1⟩ where
  impl := advanceWithCost n
  spec := (· + n)
  commutes bs := by
    change value (advanceWithCost n bs).1 = value bs + n
    rw [show (advanceWithCost n bs).1 = advance n bs from (advanceSquare n).commutes bs]; exact value_advance n bs

/-- Observe numeric meaning while retaining the measured write count. -/
def valueObservation :
    Squares.Square ⟨Measured Bits Nat, Bits, Prod.fst⟩
      ⟨Measured Nat Nat, Nat, Prod.fst⟩ where
  impl r := (value r.1, r.2)
  spec := value
  commutes _ := rfl

def observedCounter (n : Nat) := Squares.compose valueObservation (advanceSquare n)

theorem observedCounter_value (n : Nat) (bs : Bits) :
    ((observedCounter n).impl bs).1 = value bs + n :=
  ((observedCounter n).commutes bs).trans (value_advance n bs)

theorem observedCounter_writes (n : Nat) (bs : Bits) :
    ((observedCounter n).impl bs).2 = totalCost n bs :=
  congrArg Prod.snd (advanceWithCost_eq n bs)

end Resources.BinaryCounter

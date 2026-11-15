import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-! Raw search observations, independent of the control machine and its pole. -/
namespace ClassicalControl

inductive Value where
  | found (position numeral half : Nat) (odds : List Nat)
  | none (odds : List Nat)
  | odd (half : Nat)
  deriving DecidableEq, Repr

def oddNumerals (O : List Nat) : List Nat := O.map (fun h => 2*h+1)

/-- The prefix equation records every earlier numeral, in order. -/
def First (L : List Nat) : Value → Prop
  | .found j n h O => j = O.length ∧ n = 2*h ∧ ∃ rest, L = oddNumerals O ++ n :: rest
  | .none O => L = oddNumerals O
  | .odd _ => False

def Weak (L : List Nat) : Value → Prop
  | .found j n h _ => L[j]? = some n ∧ n = 2*h
  | _ => False

def prependOdd (h : Nat) : Value → Value
  | .found j n k O => .found (j+1) n k (h::O)
  | .none O => .none (h::O)
  | .odd k => .odd k

/-- Independent direct recursion, with no control operations. -/
def direct : List Nat → Value
  | [] => .none []
  | n::ns => if n % 2 = 0 then .found 0 n (n/2) []
      else prependOdd (n/2) (direct ns)

theorem parity_even (n : Nat) (h : n % 2 = 0) : n = 2*(n/2) := by omega
theorem parity_odd (n : Nat) (h : n % 2 ≠ 0) : n = 2*(n/2)+1 := by omega

theorem first_prepend {L : List Nat} {z : Value} (hz : First L z) (h : Nat) :
    First ((2*h+1)::L) (prependOdd h z) := by
  cases z with
  | found j n k O =>
    rcases hz with ⟨rfl, hn, rest, rfl⟩
    exact ⟨rfl, hn, rest, rfl⟩
  | none O => simpa [First, prependOdd, oddNumerals] using congrArg (List.cons (2*h+1)) hz
  | odd k => exact False.elim hz

theorem direct_first (L : List Nat) : First L (direct L) := by
  induction L with
  | nil => rfl
  | cons n ns ih =>
    simp only [direct]
    split_ifs with hn
    · exact ⟨rfl, parity_even n hn, ns, rfl⟩
    · conv_lhs => rw [parity_odd n hn]
      exact first_prepend ih (n/2)

theorem first_weak {L : List Nat} {j n h : Nat} {O : List Nat}
    (hz : First L (.found j n h O)) : Weak L (.found j n h O) := by
  rcases hz with ⟨rfl, hn, rest, rfl⟩
  refine ⟨?_, hn⟩
  simp [oddNumerals]

/-- Every stated index and oddness witness is recoverable from the prefix equation. -/
theorem first_indices {L : List Nat} {j n h : Nat} {O : List Nat}
    (hz : First L (.found j n h O)) :
    j < L.length ∧ L[j]? = some n ∧ n = 2*h ∧ O.length = j ∧
      ∀ i, i < j → L[i]? = (O[i]?).map (fun a => 2*a+1) := by
  rcases hz with ⟨rfl, hn, rest, rfl⟩
  refine ⟨by simp [oddNumerals], (first_weak ⟨rfl, hn, rest, rfl⟩).1,
    hn, rfl, ?_⟩
  intro i hi
  simp only [List.getElem?_append, oddNumerals, List.length_map]
  simp [hi]


theorem direct_even (h : Nat) (rest : List Nat) :
    direct (2*h::rest) = .found 0 (2*h) h [] := by
  have hd : 2*h / 2 = h := by omega
  simp [direct, hd]

theorem direct_odd (h : Nat) (rest : List Nat) :
    direct ((2*h+1)::rest) = prependOdd h (direct rest) := by
  have hd : (2*h+1) / 2 = h := by omega
  simp [direct, hd]

/-- A valid certificate uniquely determines the independent direct result. -/
theorem first_eq_direct {L : List Nat} {z : Value} (hz : First L z) : direct L = z := by
  cases z with
  | found j n h O =>
    rcases hz with ⟨rfl, rfl, rest, rfl⟩
    induction O with
    | nil => exact direct_even h rest
    | cons a O ih =>
      change direct ((2*a+1)::(oddNumerals O ++ 2*h::rest)) = _
      rw [direct_odd, ih]; rfl
  | none O =>
    change L = oddNumerals O at hz
    subst L
    induction O with
    | nil => rfl
    | cons a O ih =>
      change direct ((2*a+1)::oddNumerals O) = _
      rw [direct_odd, ih]; rfl
  | odd h => exact False.elim hz

theorem first_unique {L : List Nat} {z w : Value} (hz : First L z) (hw : First L w) : z = w :=
  (first_eq_direct hz).symm.trans (first_eq_direct hw)


/-- Executable validation of raw records; internal Odd values are rejected. -/
def checkFirst (L : List Nat) : Value → Bool
  | .found j n h O => decide (j = O.length ∧ n = 2*h ∧ (oddNumerals O ++ [n]).IsPrefix L)
  | .none O => decide (L = oddNumerals O)
  | .odd _ => false

theorem checkFirst_correct (L : List Nat) (v : Value) : checkFirst L v = true ↔ First L v := by
  cases v with
  | found j n h O =>
    simp only [checkFirst, decide_eq_true_eq, First]
    constructor
    · rintro ⟨hj, hn, rest, he⟩
      exact ⟨hj, hn, rest, by simpa only [List.append_assoc, List.singleton_append] using he.symm⟩
    · rintro ⟨hj, hn, rest, he⟩
      exact ⟨hj, hn, rest, by simpa only [List.append_assoc, List.singleton_append] using he.symm⟩
  | none O => simp [checkFirst, First]
  | odd h => simp [checkFirst, First]

/-- A successful decoder returns the entire raw observation unchanged. -/
def decode (L : List Nat) (v : Value) : Option Value :=
  if checkFirst L v then some v else none

theorem decode_correct (L : List Nat) (v : Value) : decode L v = some v ↔ First L v := by
  simp [decode, checkFirst_correct]

theorem none_indices {L : List Nat} {O : List Nat} (h : First L (.none O)) :
    O.length = L.length ∧ ∀ i, i < L.length → L[i]? = (O[i]?).map (fun a => 2*a+1) := by
  change L = oddNumerals O at h
  subst L
  simp [oddNumerals]

end ClassicalControl

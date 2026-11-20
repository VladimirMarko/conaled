import Examples.ComparisonPermutations
import Examples.InsertionSorting

/-!
# VFA decision procedures through the standard Lean interfaces

Reconstruction of VFA 2.1 `Decide.v`; source attribution and the complete
record/exercise/command correspondence are in `docs/research/vfa-decide.md`.
The original VFA license is preserved at `docs/licenses/vfa-MIT.txt`.

The independent calculations distinguish both data tags when both propositions
hold, insertion before equal keys, positional equality from permutation, and
present/absent membership. The actual decision-based sorter is connected to the
accepted insertion-sort contract and an independently implemented checker.
The two source assumptions become explicit parameters with constructive Nat
realizations. No complexity or native-performance equivalence is claimed.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.DecisionProcedures

open Examples.ComparisonPermutations

theorem three_lt_seven_bool : decide ((3 : Nat) < 7) = true := rfl

/-- Inspect the proof-carrying decision; its false Boolean contradicts the
independently calculated comparison. -/
theorem three_lt_seven_cases : (3 : Nat) < 7 := by
  have hb : (reflectedLt 3 7).decide = true := three_lt_seven_bool
  generalize hd : reflectedLt 3 7 = d at hb
  cases d with
  | isFalse h => contradiction
  | isTrue h => exact h

/-- The alternate proof consumes the true reflection field directly. -/
theorem three_lt_seven_reflection : (3 : Nat) < 7 :=
  (reflectedLt 3 7).reflects_decide

theorem reflectedLt_reverse : (reflectedLt 7 3).decide = false := rfl
theorem reflectedLt_equal (a : Nat) : (reflectedLt a a).decide = false := by
  simp

namespace ScratchPad

/-- Generic source `sumbool A B`: the two tags remain data even when both
propositions hold. This is an alias of existing types, not a new decision class. -/
abbrev ProofSum (A B : Prop) := Sum (PLift A) (PLift B)

def proofSumTag {A B : Prop} : ProofSum A B → Bool
  | .inl _ => true
  | .inr _ => false

abbrev T1 := ProofSum ((3 : Nat) < 7) ((2 : Nat) < 3)

theorem less_three_seven : (3 : Nat) < 7 := three_lt_seven_reflection
theorem greater_three_two : (2 : Nat) < 3 := by decide

def v1a : T1 := .inl ⟨less_three_seven⟩
def v1b : T1 := .inr ⟨greater_three_two⟩

theorem v1a_tag : proofSumTag v1a = true := rfl
theorem v1b_tag : proofSumTag v1b = false := rfl
theorem v1a_ne_v1b : v1a ≠ v1b := by
  intro h
  have bad := congrArg proofSumTag h
  contradiction

abbrev T2 := ProofSum ((3 : Nat) < 7) ((3 : Nat) < 2)
def v2a : T2 := .inl ⟨less_three_seven⟩

/-- The impossible right payload is eliminated; proof irrelevance then
identifies all inhabitants with the displayed left value. -/
theorem t2_eq_v2a (x : T2) : x = v2a := by
  cases x with
  | inl h => rfl
  | inr h => exact (Nat.not_lt_of_ge (by decide) h.down).elim

theorem t2_tag (x : T2) : proofSumTag x = true := by
  rw [t2_eq_v2a x]
  rfl

/-- Only the proposition/negation specialization is an ordinary decision. -/
def proofSumToDecidable {P : Prop} : ProofSum P (¬ P) → Decidable P
  | .inl h => .isTrue h.down
  | .inr h => .isFalse h.down

def decidableToProofSum {P : Prop} : Decidable P → ProofSum P (¬ P)
  | .isTrue h => .inl ⟨h⟩
  | .isFalse h => .inr ⟨h⟩

theorem decidableToProofSum_proofSumToDecidable {P : Prop}
    (s : ProofSum P (¬ P)) :
    decidableToProofSum (proofSumToDecidable s) = s := by
  cases s <;> rfl

theorem proofSumToDecidable_decidableToProofSum {P : Prop} (d : Decidable P) :
    proofSumToDecidable (decidableToProofSum d) = d := by
  cases d <;> rfl

theorem proofSumToDecidable_decide {P : Prop} (s : ProofSum P (¬ P)) :
    (proofSumToDecidable s).decide = proofSumTag s := by
  cases s <;> rfl

theorem decidableToProofSum_tag {P : Prop} (d : Decidable P) :
    proofSumTag (decidableToProofSum d) = d.decide := by
  cases d <;> rfl

abbrev T4 := ∀ a b : Nat, Decidable (a < b)

def v3 : ProofSum ((3 : Nat) < 7) (¬ (3 : Nat) < 7) :=
  .inl ⟨less_three_seven⟩

def isThreeLtSeven : Bool := proofSumTag v3
theorem isThreeLtSeven_eq_true : isThreeLtSeven = true := rfl

/-- Expression and proof-elaborated definitions use the same accepted
Boolean-to-decision adapter. Its proof field is in `Prop`. -/
def ltDecision (a b : Nat) : Decidable (a < b) := reflectedLt a b

def ltDecision' (a b : Nat) : Decidable (a < b) := by
  exact reflectedLt a b

theorem ltDecision_eq_ltDecision' (a b : Nat) :
    ltDecision a b = ltDecision' a b := rfl

theorem ltDecision_decide (a b : Nat) :
    (ltDecision a b).decide = decide (a < b) := rfl

theorem ltDecision'_decide (a b : Nat) :
    (ltDecision' a b).decide = decide (a < b) := rfl

theorem v3_decision : proofSumToDecidable v3 = ltDecision 3 7 := rfl
theorem ltDecision_true : (ltDecision 3 7).decide = true := rfl
theorem ltDecision_false : (ltDecision 7 3).decide = false := rfl
theorem ltDecision'_true : (ltDecision' 3 7).decide = true := rfl
theorem ltDecision'_false : (ltDecision' 7 3).decide = false := rfl

end ScratchPad

namespace ScratchPad2

abbrev ltDecision := ScratchPad.ltDecision

def leDecision (a b : Nat) : Decidable (a ≤ b) :=
  decidable_of_bool (decide (a ≤ b)) (leb_reflect a b)

theorem leDecision_decide (a b : Nat) :
    (leDecision a b).decide = decide (a ≤ b) := rfl

/-- In particular, the false branch supplies `¬ a ≤ b`, not `¬ a < b`. -/
theorem leDecision_true_iff (a b : Nat) :
    (leDecision a b).decide = true ↔ a ≤ b := by
  simp [leDecision_decide]

theorem leDecision_false_iff (a b : Nat) :
    (leDecision a b).decide = false ↔ ¬ a ≤ b := by
  simp [leDecision_decide]

/-- The exact source recurrence branches on the supplied constructive decision. -/
def insert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | h :: t =>
    letI : Decidable (x ≤ h) := leDecision x h
    if x ≤ h then x :: h :: t else h :: insert x t

def sort : List Nat → List Nat
  | [] => []
  | h :: t => insert h (sort t)

abbrev Sorted (xs : List Nat) : Prop := InsertionSorting.sorted xs

theorem insert_nil (a : Nat) : insert a [] = [a] := rfl

theorem insert_cons (a h : Nat) (t : List Nat) :
    insert a (h :: t) = if a ≤ h then a :: h :: t else h :: insert a t := by
  by_cases hle : a ≤ h
  · simp only [insert, ite_eq_left hle]
  · simp only [insert, ite_eq_right hle]

theorem sort_nil : sort [] = [] := rfl
theorem sort_cons (a : Nat) (xs : List Nat) : sort (a :: xs) = insert a (sort xs) := rfl

/-- The bridge covers every input, without a sortedness precondition. -/
theorem insert_eq_source (a : Nat) (xs : List Nat) :
    insert a xs = InsertionSorting.insert a xs := by
  induction xs with
  | nil => rfl
  | cons h t ih => rw [insert_cons, InsertionSorting.insert_cons, ih]

theorem sort_eq_source (xs : List Nat) : sort xs = InsertionSorting.sort xs := by
  induction xs with
  | nil => rfl
  | cons h t ih => rw [sort_cons, InsertionSorting.sort_cons, insert_eq_source, ih]

theorem sorted_nil : Sorted [] := InsertionSorting.sorted_nil
theorem sorted_singleton (a : Nat) : Sorted [a] := InsertionSorting.sorted_1 a

theorem sorted_cons_iff (a b : Nat) (xs : List Nat) :
    Sorted (a :: b :: xs) ↔ a ≤ b ∧ Sorted (b :: xs) :=
  List.isChain_cons_cons

theorem insert_of_le (a h : Nat) (t : List Nat) (hle : a ≤ h) :
    insert a (h :: t) = a :: h :: t := by rw [insert_cons, ite_eq_left hle]

theorem insert_of_not_le (a h : Nat) (t : List Nat) (hn : ¬ a ≤ h) :
    insert a (h :: t) = h :: insert a t := by rw [insert_cons, ite_eq_right hn]

theorem insert_sorted (a : Nat) (xs : List Nat) (hs : Sorted xs) :
    Sorted (insert a xs) := by
  rw [insert_eq_source]
  exact InsertionSorting.insert_sorted a xs hs

/-- Positive branch evidence builds the source adjacent-cons constructor. -/
theorem insert_sorted_true_branch (a h : Nat) (t : List Nat)
    (hle : a ≤ h) (hs : Sorted (h :: t)) : Sorted (a :: h :: t) :=
  InsertionSorting.sorted_cons a h t hle hs

/-- Negative branch evidence selects the recursive output in the reused
insertion-preservation theorem. The tested relation remains non-strict. -/
theorem insert_sorted_false_branch (a h : Nat) (t : List Nat)
    (hn : ¬ a ≤ h) (hs : Sorted (h :: t)) : Sorted (h :: insert a t) := by
  have correct := insert_sorted a (h :: t) hs
  rw [insert_of_not_le a h t hn] at correct
  exact correct

theorem insert_sorted_decision_cases (a h : Nat) (t : List Nat)
    (hs : Sorted (h :: t)) : Sorted (insert a (h :: t)) := by
  cases hd : leDecision a h with
  | isTrue hle =>
    rw [insert_of_le a h t hle]
    exact insert_sorted_true_branch a h t hle hs
  | isFalse hn =>
    rw [insert_of_not_le a h t hn]
    exact insert_sorted_false_branch a h t hn hs

theorem sort_sorted (xs : List Nat) : Sorted (sort xs) := by
  rw [sort_eq_source]
  exact InsertionSorting.sort_sorted xs

theorem sort_perm (xs : List Nat) : xs.Perm (sort xs) := by
  rw [sort_eq_source]
  exact InsertionSorting.sort_perm xs

theorem sort_length (xs : List Nat) : (sort xs).length = xs.length :=
  (sort_perm xs).length_eq.symm

theorem sort_calculation : sort [3, 1, 2, 1] = [1, 1, 2, 3] := rfl

theorem sort_calculation_contract :
    ([3, 1, 2, 1] : List Nat).Perm [1, 1, 2, 3] ∧ Sorted [1, 1, 2, 3] :=
  ⟨sort_perm [3, 1, 2, 1], sort_sorted [3, 1, 2, 1]⟩

theorem insert_ties_before_head : insert 2 [2, 0] = [2, 2, 0] := rfl

/-- No invalid sorted-input premise is smuggled into the operation bridge. -/
theorem unsorted_insert_boundary :
    insert 1 [2, 0] = [1, 2, 0] ∧ ¬ Sorted (insert 1 [2, 0]) := ⟨rfl, by decide⟩

/-- The source proposition-valued assumption, kept as an ordinary parameter type. -/
abbrev NatLtCases : Prop := ∀ i j : Nat, i < j ∨ ¬ i < j

/-- The source data-valued assumption, kept separate from a proof of disjunction. -/
abbrev NatLtDecision := ∀ i j : Nat, Decidable (i < j)

theorem nat_lt_cases : NatLtCases := fun i j =>
  if h : i < j then Or.inl h else Or.inr h
abbrev natLtDecision : NatLtDecision := Nat.decLt

/-- A supplied proof can be consumed in a proof without computing a data tag. -/
theorem nat_lt_cases_use (h : NatLtCases) (i j : Nat) : i < j ∨ ¬ i < j := h i j

def maxWithDecision (d : NatLtDecision) (i j : Nat) : Nat :=
  if (d i j).decide then j else i

theorem maxWithDecision_eq_max (d : NatLtDecision) (i j : Nat) :
    maxWithDecision d i j = max i j := by
  unfold maxWithDecision
  cases hd : d i j with
  | isTrue h => exact (Nat.max_eq_right (Nat.le_of_lt h)).symm
  | isFalse h => exact (Nat.max_eq_left (Nat.le_of_not_gt h)).symm

/-- This result holds for every valid supplied decision, even before its
computational implementation is supplied to a closed evaluator. -/
theorem maxWithDecision_three_seven (d : NatLtDecision) :
    maxWithDecision d 3 7 = 7 := by rw [maxWithDecision_eq_max]; rfl

theorem maxWithDecision_concrete : maxWithDecision natLtDecision 3 7 = 7 := rfl
theorem maxWithDecision_reverse : maxWithDecision natLtDecision 7 3 = 7 := rfl
theorem maxWithDecision_equal (a : Nat) : maxWithDecision natLtDecision a a = a := by
  rw [maxWithDecision_eq_max, Nat.max_self]

/-- In Lean's adapter the Boolean is separate from its opaque proof field;
the source's abandoned Rocq reduction becomes this successful computation. -/
theorem compute_with_reflected_decision : (if (ltDecision 3 7).decide then 7 else 3) = 7 := rfl

theorem compute_with_standard_decision : (if (Nat.decLt 3 7).decide then 7 else 3) = 7 := rfl

end ScratchPad2

def listNatEqDecision (xs ys : List Nat) : Decidable (xs = ys) := inferInstance
def listNatIn (i : Nat) (xs : List Nat) : Decidable (i ∈ xs) := inferInstance

theorem listNatEqDecision_correct (xs ys : List Nat) :
    (listNatEqDecision xs ys).decide = true ↔ xs = ys := by
  simp

theorem listNatIn_correct (i : Nat) (xs : List Nat) :
    (listNatIn i xs).decide = true ↔ i ∈ xs := by
  simp

theorem listNatIn_false_iff (i : Nat) (xs : List Nat) :
    (listNatIn i xs).decide = false ↔ i ∉ xs := by
  simp

theorem lists_unequal : (listNatEqDecision [1, 3, 4] [1, 4, 3]).decide = false := rfl
theorem lists_equal : (listNatEqDecision [1, 3, 4] [1, 3, 4]).decide = true := rfl

theorem permuted_but_unequal :
    ([1, 3, 4] : List Nat).Perm [1, 4, 3] ∧ ([1, 3, 4] : List Nat) ≠ [1, 4, 3] := by
  decide

theorem in_four_pi : (listNatIn 4 [3, 1, 4, 1, 5, 9, 2, 6]).decide = true := rfl
theorem four_mem_pi : 4 ∈ ([3, 1, 4, 1, 5, 9, 2, 6] : List Nat) :=
  (listNatIn_correct _ _).mp in_four_pi

theorem absent_from_pi : (listNatIn 8 [3, 1, 4, 1, 5, 9, 2, 6]).decide = false := rfl
theorem eight_notMem_pi : 8 ∉ ([3, 1, 4, 1, 5, 9, 2, 6] : List Nat) :=
  (listNatIn_false_iff _ _).mp absent_from_pi

theorem listNatIn_nil (i : Nat) : (listNatIn i []).decide = false := rfl

/-- Duplicates do not change the membership proposition; no occurrence count
or index is returned by this interface. -/
theorem listNatIn_duplicate (i h : Nat) (xs : List Nat) :
    (listNatIn i (h :: h :: xs)).decide = (listNatIn i (h :: xs)).decide := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.mem_cons, or_self_left]

theorem sort_adjacent_checked (xs : List Nat) :
    OrderCertificate.adjacent (fun a b : Nat => decide (a ≤ b))
      (ScratchPad2.sort xs) = true :=
  (OrderCertificate.adjacent_correct leb_reflect _).mpr (ScratchPad2.sort_sorted xs)

/-- The checker composition consumes the real sorting proof and retains the
length justified by occurrence-preserving permutation. -/
theorem sorted_checkedLength (xs : List Nat) :
    (OrderCertificate.checkedLengthSquare leb_reflect).impl (ScratchPad2.sort xs) =
      some xs.length := by
  have h := (OrderCertificate.checkedLength_correct leb_reflect (ScratchPad2.sort xs)).mpr
    (List.isChain_iff_pairwise.mp (ScratchPad2.sort_sorted xs))
  simpa only [ScratchPad2.sort_length] using h

theorem sort_checked_calculation :
    (OrderCertificate.checkedLengthSquare leb_reflect).impl
      (ScratchPad2.sort [3, 1, 2, 1]) = some 4 := sorted_checkedLength [3, 1, 2, 1]

theorem empty_checked :
    (OrderCertificate.checkedLengthSquare leb_reflect).impl (ScratchPad2.sort []) =
      some 0 := sorted_checkedLength []

end Examples.DecisionProcedures

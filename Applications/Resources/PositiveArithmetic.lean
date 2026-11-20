import Applications.Numerals.PositiveArithmetic
import Applications.Resources.Measured

/-!
# Measured positive arithmetic

The result of each recursive call feeds the same constructors and comparison
dispatch as the accepted source operation. Successor jointly observes constructor
visits and changed-digit writes; carry addition charges visits, including every
nested successor call. Comparison counts entered constructor-pair calls.

These are declared source tariffs. They do not measure native allocation,
numeric conversion, printing, garbage collection or elapsed time.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.PositiveArithmetic

open Numerals.PositiveKeys Numerals.PositiveArithmetic

/-- One execution, with observations `(constructor visits, changed-digit writes)`.
The terminal one writes the old low bit to zero and adds a new high one,
but enters one branch. -/
def succRun : PosNum → Measured PosNum (Nat × Nat)
  | .one => (.bit0 .one, (1, 2))
  | .bit0 p => (.bit1 p, (1, 1))
  | .bit1 p =>
      let result := succRun p
      (.bit0 result.1, (1 + result.2.1, 1 + result.2.2))

@[simp] theorem succRun_one : succRun .one = (.bit0 .one, (1, 2)) := rfl

@[simp] theorem succRun_bit0 (p : PosNum) :
    succRun (.bit0 p) = (.bit1 p, (1, 1)) := rfl

@[simp] theorem succRun_bit1 (p : PosNum) :
    succRun (.bit1 p) =
      (.bit0 (succRun p).1, (1 + (succRun p).2.1, 1 + (succRun p).2.2)) := rfl

/-- Project constructor visits from the same measured successor execution. -/
def succVisitRun (p : PosNum) : Measured PosNum Nat := reweight Prod.fst (succRun p)

/-- Project changed-digit writes from that execution, without counting allocation. -/
def succWriteRun (p : PosNum) : Measured PosNum Nat := reweight Prod.snd (succRun p)

@[simp] theorem succVisitRun_one : succVisitRun .one = (.bit0 .one, 1) := rfl

@[simp] theorem succVisitRun_bit0 (p : PosNum) :
    succVisitRun (.bit0 p) = (.bit1 p, 1) := rfl

@[simp] theorem succVisitRun_bit1 (p : PosNum) :
    succVisitRun (.bit1 p) = (.bit0 (succVisitRun p).1, 1 + (succVisitRun p).2) := rfl

@[simp] theorem succWriteRun_one : succWriteRun .one = (.bit0 .one, 2) := rfl

@[simp] theorem succWriteRun_bit0 (p : PosNum) :
    succWriteRun (.bit0 p) = (.bit1 p, 1) := rfl

@[simp] theorem succWriteRun_bit1 (p : PosNum) :
    succWriteRun (.bit1 p) = (.bit0 (succWriteRun p).1, 1 + (succWriteRun p).2) := rfl

theorem succRun_value (p : PosNum) : (succRun p).1 = PosNum.succ p := by
  induction p with
  | one => rfl
  | bit0 p => rfl
  | bit1 p ih => simp only [succRun_bit1, PosNum.succ, ih]

theorem succVisitRun_value (p : PosNum) : (succVisitRun p).1 = PosNum.succ p :=
  succRun_value p

theorem succWriteRun_value (p : PosNum) : (succWriteRun p).1 = PosNum.succ p :=
  succRun_value p

theorem succVisitRun_cost_le (p : PosNum) : (succVisitRun p).2 ≤ bitLength p := by
  induction p with
  | one => rfl
  | bit0 p => simp only [succVisitRun_bit0, bitLength_bit0]; omega
  | bit1 p ih => simp only [succVisitRun_bit1, bitLength_bit1]; omega

theorem succVisitRun_cost_le_writes (p : PosNum) :
    (succVisitRun p).2 ≤ (succWriteRun p).2 := by
  induction p with
  | one => decide
  | bit0 p => rfl
  | bit1 p ih => simp only [succVisitRun_bit1, succWriteRun_bit1]; omega

theorem succWriteRun_cost_le (p : PosNum) : (succWriteRun p).2 ≤ bitLength p + 1 := by
  induction p with
  | one => rfl
  | bit0 p => simp only [succWriteRun_bit0, bitLength_bit0]; omega
  | bit1 p ih => simp only [succWriteRun_bit1, bitLength_bit1]; omega

theorem succVisitRun_cost_log (p : PosNum) :
    (succVisitRun p).2 ≤ Nat.log 2 (numeric p) + 1 := by
  simpa only [bitLength_eq_log] using succVisitRun_cost_le p

theorem succWriteRun_cost_log (p : PosNum) :
    (succWriteRun p).2 ≤ Nat.log 2 (numeric p) + 2 := by
  simpa only [bitLength_eq_log, Nat.add_assoc] using succWriteRun_cost_le p

/-- Exactly the eighteen source branches. A terminal branch that carries into
the remaining child includes the actual measured successor of that child. -/
def addcRun : Bool → PosNum → PosNum → Measured PosNum Nat
  | false, .bit1 p, .bit1 q =>
      let result := addcRun true p q
      (.bit0 result.1, 1 + result.2)
  | false, .bit1 p, .bit0 q =>
      let result := addcRun false p q
      (.bit1 result.1, 1 + result.2)
  | false, .bit1 p, .one =>
      let result := succVisitRun p
      (.bit0 result.1, 1 + result.2)
  | false, .bit0 p, .bit1 q =>
      let result := addcRun false p q
      (.bit1 result.1, 1 + result.2)
  | false, .bit0 p, .bit0 q =>
      let result := addcRun false p q
      (.bit0 result.1, 1 + result.2)
  | false, .bit0 p, .one => (.bit1 p, 1)
  | false, .one, .bit1 q =>
      let result := succVisitRun q
      (.bit0 result.1, 1 + result.2)
  | false, .one, .bit0 q => (.bit1 q, 1)
  | false, .one, .one => (.bit0 .one, 1)
  | true, .bit1 p, .bit1 q =>
      let result := addcRun true p q
      (.bit1 result.1, 1 + result.2)
  | true, .bit1 p, .bit0 q =>
      let result := addcRun true p q
      (.bit0 result.1, 1 + result.2)
  | true, .bit1 p, .one =>
      let result := succVisitRun p
      (.bit1 result.1, 1 + result.2)
  | true, .bit0 p, .bit1 q =>
      let result := addcRun true p q
      (.bit0 result.1, 1 + result.2)
  | true, .bit0 p, .bit0 q =>
      let result := addcRun false p q
      (.bit1 result.1, 1 + result.2)
  | true, .bit0 p, .one =>
      let result := succVisitRun p
      (.bit0 result.1, 1 + result.2)
  | true, .one, .bit1 q =>
      let result := succVisitRun q
      (.bit1 result.1, 1 + result.2)
  | true, .one, .bit0 q =>
      let result := succVisitRun q
      (.bit0 result.1, 1 + result.2)
  | true, .one, .one => (.bit1 .one, 1)
termination_by structural _ p _ => p

@[simp] theorem addcRun_false_bit1_bit1 (p q : PosNum) :
    addcRun false (.bit1 p) (.bit1 q) = (.bit0 (addcRun true p q).1, 1 + (addcRun true p q).2) := rfl

@[simp] theorem addcRun_false_bit1_bit0 (p q : PosNum) :
    addcRun false (.bit1 p) (.bit0 q) = (.bit1 (addcRun false p q).1, 1 + (addcRun false p q).2) := rfl

@[simp] theorem addcRun_false_bit1_one (p : PosNum) :
    addcRun false (.bit1 p) .one = (.bit0 (succVisitRun p).1, 1 + (succVisitRun p).2) := rfl

@[simp] theorem addcRun_false_bit0_bit1 (p q : PosNum) :
    addcRun false (.bit0 p) (.bit1 q) = (.bit1 (addcRun false p q).1, 1 + (addcRun false p q).2) := rfl

@[simp] theorem addcRun_false_bit0_bit0 (p q : PosNum) :
    addcRun false (.bit0 p) (.bit0 q) = (.bit0 (addcRun false p q).1, 1 + (addcRun false p q).2) := rfl

@[simp] theorem addcRun_false_bit0_one (p : PosNum) :
    addcRun false (.bit0 p) .one = (.bit1 p, 1) := rfl

@[simp] theorem addcRun_false_one_bit1 (q : PosNum) :
    addcRun false .one (.bit1 q) = (.bit0 (succVisitRun q).1, 1 + (succVisitRun q).2) := rfl

@[simp] theorem addcRun_false_one_bit0 (q : PosNum) :
    addcRun false .one (.bit0 q) = (.bit1 q, 1) := rfl

@[simp] theorem addcRun_false_one_one : addcRun false .one .one = (.bit0 .one, 1) := rfl

@[simp] theorem addcRun_true_bit1_bit1 (p q : PosNum) :
    addcRun true (.bit1 p) (.bit1 q) = (.bit1 (addcRun true p q).1, 1 + (addcRun true p q).2) := rfl

@[simp] theorem addcRun_true_bit1_bit0 (p q : PosNum) :
    addcRun true (.bit1 p) (.bit0 q) = (.bit0 (addcRun true p q).1, 1 + (addcRun true p q).2) := rfl

@[simp] theorem addcRun_true_bit1_one (p : PosNum) :
    addcRun true (.bit1 p) .one = (.bit1 (succVisitRun p).1, 1 + (succVisitRun p).2) := rfl

@[simp] theorem addcRun_true_bit0_bit1 (p q : PosNum) :
    addcRun true (.bit0 p) (.bit1 q) = (.bit0 (addcRun true p q).1, 1 + (addcRun true p q).2) := rfl

@[simp] theorem addcRun_true_bit0_bit0 (p q : PosNum) :
    addcRun true (.bit0 p) (.bit0 q) = (.bit1 (addcRun false p q).1, 1 + (addcRun false p q).2) := rfl

@[simp] theorem addcRun_true_bit0_one (p : PosNum) :
    addcRun true (.bit0 p) .one = (.bit0 (succVisitRun p).1, 1 + (succVisitRun p).2) := rfl

@[simp] theorem addcRun_true_one_bit1 (q : PosNum) :
    addcRun true .one (.bit1 q) = (.bit1 (succVisitRun q).1, 1 + (succVisitRun q).2) := rfl

@[simp] theorem addcRun_true_one_bit0 (q : PosNum) :
    addcRun true .one (.bit0 q) = (.bit0 (succVisitRun q).1, 1 + (succVisitRun q).2) := rfl

@[simp] theorem addcRun_true_one_one : addcRun true .one .one = (.bit1 .one, 1) := rfl

theorem addcRun_value (c : Bool) (p q : PosNum) :
    (addcRun c p q).1 = Numerals.PositiveArithmetic.addc c p q := by
  induction p generalizing c q with
  | one => cases q <;> cases c <;> simp [addcRun, addc, succVisitRun_value, succ]
  | bit0 p ih => cases q <;> cases c <;> simp [addcRun, addc, succVisitRun_value, succ, ih]
  | bit1 p ih => cases q <;> cases c <;> simp [addcRun, addc, succVisitRun_value, succ, ih]

theorem addcRun_cost_le (c : Bool) (p q : PosNum) :
    (addcRun c p q).2 ≤ max (bitLength p) (bitLength q) := by
  induction p generalizing c q with
  | one =>
    cases q with
    | one => cases c <;> simp [addcRun, bitLength_one]
    | bit0 q =>
      have hs := succVisitRun_cost_le q
      cases c <;> simp only [addcRun, bitLength_one, bitLength_bit0] <;> omega
    | bit1 q =>
      have hs := succVisitRun_cost_le q
      cases c <;> simp only [addcRun, bitLength_one, bitLength_bit1] <;> omega
  | bit0 p ih =>
    cases q with
    | one =>
      have hs := succVisitRun_cost_le p
      cases c <;> simp only [addcRun, bitLength_one, bitLength_bit0] <;> omega
    | bit0 q =>
      have hf := ih false q
      have ht := ih true q
      cases c <;> simp only [addcRun, bitLength_bit0] <;> omega
    | bit1 q =>
      have hf := ih false q
      have ht := ih true q
      cases c <;> simp only [addcRun, bitLength_bit0, bitLength_bit1] <;> omega
  | bit1 p ih =>
    cases q with
    | one =>
      have hs := succVisitRun_cost_le p
      cases c <;> simp only [addcRun, bitLength_one, bitLength_bit1] <;> omega
    | bit0 q =>
      have hf := ih false q
      have ht := ih true q
      cases c <;> simp only [addcRun, bitLength_bit0, bitLength_bit1] <;> omega
    | bit1 q =>
      have hf := ih false q
      have ht := ih true q
      cases c <;> simp only [addcRun, bitLength_bit1] <;> omega

theorem addcRun_cost_le_result (c : Bool) (p q : PosNum) :
    (addcRun c p q).2 ≤ bitLength (addcRun c p q).1 := by
  rw [addcRun_value]
  exact (addcRun_cost_le c p q).trans (max_bitLength_le_addc c p q)

theorem addcRun_cost_log_result (c : Bool) (p q : PosNum) :
    (addcRun c p q).2 ≤ Nat.log 2 (numeric (addcRun c p q).1) + 1 := by
  simpa only [bitLength_eq_log] using addcRun_cost_le_result c p q

/-- Source addition starts with the measured carry-false branch. -/
def addRun (p q : PosNum) : Measured PosNum Nat := addcRun false p q

theorem addRun_value (p q : PosNum) : (addRun p q).1 = p + q :=
  (addcRun_value false p q).trans (add_eq_add p q)

theorem addRun_cost_le (p q : PosNum) :
    (addRun p q).2 ≤ max (bitLength p) (bitLength q) := addcRun_cost_le false p q

/-- Actual comparator calls, including the terminal comparison. Both mixed-bit
branches inspect the ordering returned by the measured higher-bit comparison. -/
def cmpRun : PosNum → PosNum → Measured Ordering Nat
  | .one, .one => (.eq, 1)
  | _, .one => (.gt, 1)
  | .one, _ => (.lt, 1)
  | .bit0 p, .bit0 q =>
      let result := cmpRun p q
      (result.1, 1 + result.2)
  | .bit0 p, .bit1 q =>
      let result := cmpRun p q
      ((Ordering.casesOn result.1 .lt .lt .gt : Ordering), 1 + result.2)
  | .bit1 p, .bit0 q =>
      let result := cmpRun p q
      ((Ordering.casesOn result.1 .lt .gt .gt : Ordering), 1 + result.2)
  | .bit1 p, .bit1 q =>
      let result := cmpRun p q
      (result.1, 1 + result.2)

@[simp] theorem cmpRun_one_one : cmpRun .one .one = (.eq, 1) := rfl

@[simp] theorem cmpRun_one_bit0 (q : PosNum) : cmpRun .one (.bit0 q) = (.lt, 1) := rfl

@[simp] theorem cmpRun_one_bit1 (q : PosNum) : cmpRun .one (.bit1 q) = (.lt, 1) := rfl

@[simp] theorem cmpRun_bit0_one (p : PosNum) : cmpRun (.bit0 p) .one = (.gt, 1) := rfl

@[simp] theorem cmpRun_bit1_one (p : PosNum) : cmpRun (.bit1 p) .one = (.gt, 1) := rfl

@[simp] theorem cmpRun_bit0_bit0 (p q : PosNum) :
    cmpRun (.bit0 p) (.bit0 q) = ((cmpRun p q).1, 1 + (cmpRun p q).2) := rfl

@[simp] theorem cmpRun_bit1_bit1 (p q : PosNum) :
    cmpRun (.bit1 p) (.bit1 q) = ((cmpRun p q).1, 1 + (cmpRun p q).2) := rfl

theorem cmpRun_bit0_bit1 (p q : PosNum) :
    cmpRun (.bit0 p) (.bit1 q) =
      ((match (cmpRun p q).1 with | .gt => .gt | _ => .lt), 1 + (cmpRun p q).2) := by
  change ((Ordering.casesOn (cmpRun p q).1 .lt .lt .gt : Ordering), _) = _
  cases (cmpRun p q).1 <;> rfl

theorem cmpRun_bit1_bit0 (p q : PosNum) :
    cmpRun (.bit1 p) (.bit0 q) =
      ((match (cmpRun p q).1 with | .lt => .lt | _ => .gt), 1 + (cmpRun p q).2) := by
  change ((Ordering.casesOn (cmpRun p q).1 .lt .gt .gt : Ordering), _) = _
  cases (cmpRun p q).1 <;> rfl

theorem cmpRun_value (p q : PosNum) : (cmpRun p q).1 = PosNum.cmp p q := by
  induction p generalizing q with
  | one => cases q <;> rfl
  | bit0 p ih => cases q <;> simp [cmpRun, PosNum.cmp, ih]
  | bit1 p ih => cases q <;> simp [cmpRun, PosNum.cmp, ih]

theorem cmpRun_cost (p q : PosNum) :
    (cmpRun p q).2 = min (bitLength p) (bitLength q) := by
  induction p generalizing q with
  | one => cases q <;> simp [cmpRun, bitLength_one, bitLength_bit0, bitLength_bit1]
  | bit0 p ih =>
    cases q <;> simp only [cmpRun, ih, bitLength_one, bitLength_bit0, bitLength_bit1] <;> omega
  | bit1 p ih =>
    cases q <;> simp only [cmpRun, ih, bitLength_one, bitLength_bit0, bitLength_bit1] <;> omega

theorem cmpRun_cost_le_left (p q : PosNum) : (cmpRun p q).2 ≤ bitLength p := by
  rw [cmpRun_cost]
  exact min_le_left _ _

theorem cmpRun_cost_le_right (p q : PosNum) : (cmpRun p q).2 ≤ bitLength q := by
  rw [cmpRun_cost]
  exact min_le_right _ _

theorem cmpRun_self_cost (p : PosNum) : (cmpRun p p).2 = bitLength p := by
  rw [cmpRun_cost, min_self]

theorem cmpRun_cost_log (p q : PosNum) :
    (cmpRun p q).2 = min (Nat.log 2 (numeric p) + 1) (Nat.log 2 (numeric q) + 1) := by
  rw [cmpRun_cost, bitLength_eq_log, bitLength_eq_log]

end Resources.PositiveArithmetic

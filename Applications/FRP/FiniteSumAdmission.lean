import Applications.FRP.FiniteSumLowering

/-! Admission itself is a finite circuit. Its gate work and temporary arena can
be charged alongside the lowered transition, without decoding runtime state. -/
namespace FRPSpec.FiniteSum
open Applications.Circuits

def zeroTest : (a : FirstOrderCompiler.Ty) → Circuit a .base
  | .base => Circuit.not
  | .unit => .compose (.gate (.constant true)) .terminate
  | .prod a b => .compose Circuit.and
      (.pair (.compose (zeroTest a) .first) (.compose (zeroTest b) .second))

@[simp] theorem and_execute (x y : Bool) : Circuit.and.execute (x,y) = (x && y) := by
  cases x <;> cases y <;> rfl

@[simp] theorem zeroTest_correct (a : FirstOrderCompiler.Ty) (x : FirstOrderCompiler.Val Bool a) :
    (zeroTest a).execute x = true ↔ x = zero a := by
  induction a with
  | base => cases x <;> decide
  | unit => cases x; decide
  | prod a b ha hb =>
    rcases x with ⟨x,y⟩
    simp only [zeroTest, Circuit.execute]
    rw [and_execute]
    simp only [Bool.and_eq_true, ha, hb, zero, Prod.mk.injEq]

/-- Both validity arms execute. The selected arm checks active validity and
inactive zero payload; malformed active nested sums are rejected recursively. -/
def validator : (a : Ty) → Circuit a.storage .base
  | .bool => .compose (.gate (.constant true)) .terminate
  | .unit => .compose (.gate (.constant true)) .terminate
  | .prod a b => .compose Circuit.and
      (.pair (.compose (validator a) .first) (.compose (validator b) .second))
  | .sum a b => .compose boolMux (.pair .first (.pair
      (.compose Circuit.and (.pair
        (.compose (validator a) (.compose .first .second))
        (.compose (zeroTest b.storage) (.compose .second .second))))
      (.compose Circuit.and (.pair
        (.compose (zeroTest a.storage) (.compose .first .second))
        (.compose (validator b) (.compose .second .second))))))

theorem valid_prod (a b : Ty) (x : Bits a) (y : Bits b) :
    Valid (.prod a b) (x,y) ↔ Valid a x ∧ Valid b y := by
  simp [Valid, encode, observe]

theorem valid_left (a b : Ty) (x : Bits a) (y : Bits b) :
    Valid (.sum a b) (false,(x,y)) ↔ Valid a x ∧ y = zero b.storage := by
  simp [Valid, encode, observe, eq_comm]

theorem valid_right (a b : Ty) (x : Bits a) (y : Bits b) :
    Valid (.sum a b) (true,(x,y)) ↔ x = zero a.storage ∧ Valid b y := by
  simp [Valid, encode, observe, eq_comm]

@[simp] theorem validator_correct (a : Ty) (x : Bits a) :
    (validator a).execute x = true ↔ Valid a x := by
  induction a with
  | bool => cases x <;> decide
  | unit => cases x; decide
  | prod a b ha hb =>
    rcases x with ⟨x,y⟩
    simp only [validator, Circuit.execute]
    rw [and_execute]
    simp only [Bool.and_eq_true, ha, hb, valid_prod]
  | sum a b ha hb =>
    rcases x with ⟨tag,x,y⟩
    simp only [validator, Circuit.execute]
    rw [boolMux_execute]
    cases tag with
    | false =>
      change Circuit.and.execute (_,_) = true ↔ _
      rw [and_execute, Bool.and_eq_true, ha x, zeroTest_correct, valid_left]
    | true =>
      change Circuit.and.execute (_,_) = true ↔ _
      rw [and_execute, Bool.and_eq_true, zeroTest_correct, hb y, valid_right]

/-- A circuit-backed admission function with exactly the canonical policy. -/
def checkedAdmit (a : Ty) (x : Bits a) : Option (Value a) :=
  if (validator a).execute x then some (observe a x) else none

theorem checkedAdmit_eq (a : Ty) (x : Bits a) : checkedAdmit a x = admit a x := by
  unfold checkedAdmit admit
  simp only [validator_correct a x]

/-- Validation does not decode payloads or retain a history. -/
def checks (a s : Ty) : Circuit (.prod a.storage s.storage) .base :=
  .compose Circuit.and (.pair (.compose (validator a) .first) (.compose (validator s) .second))

theorem checks_correct (a s : Ty) (x : Bits a) (st : Bits s) :
    (checks a s).execute (x,st) = true ↔ Valid a x ∧ Valid s st := by
  simp only [checks, Circuit.execute]
  rw [and_execute]
  rw [Bool.and_eq_true, validator_correct a x, validator_correct s st]

theorem checks_work (a s : Ty) :
    (checks a s).work = (validator a).work + (validator s).work + 9 := by
  simp only [checks, Circuit.work, Circuit.and, Circuit.not, Circuit.nand]
  omega

end FRPSpec.FiniteSum

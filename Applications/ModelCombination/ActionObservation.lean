module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Logic.Equiv.Basic

/-!
# A bounded combination of independently supplied action and observation

The native action is retained. An explicit pointed carrier equivalence transports
the independent observer. Recovery data also describe alternative presentations,
so a rejecting case can quantify over every combination with the same overlap.
-/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace NativeModelCombination
universe uM uX uY uD uZ
variable {M : Type uM} [Monoid M] {X : Type uX} [MulAction M X]
variable {Y : Type uY} {D : Type uD}

/-- Constructed model and its exact recovery contract. The action on Z is native;
left recovery must preserve it. Right recovery is invertible even if o is not. -/
structure Combination (M : Type uM) [Monoid M] {X : Type uX} [MulAction M X]
    {Y : Type uY} {D : Type uD} (x0 : X) (y0 : Y) (d0 : D) (o : Y → D)
    (Z : Type uZ) [MulAction M Z] where
  point : Z
  resultPoint : D
  out : Z → D
  left : Z ≃ X
  right : Z ≃ Y
  left_point : left point = x0
  right_point : right point = y0
  result_point : resultPoint = d0
  left_action : ∀ (m : M) (z : Z), left (m • z) = m • left z
  right_observation : ∀ y, out (right.symm y) = o y

variable (x0 : X) (y0 : Y) (d0 : D) (o : Y → D)

/-- No combined model or final recovery law is an input. -/
def combine (e : X ≃ Y) (point : e x0 = y0) : Combination M x0 y0 d0 o X where
  point := x0
  resultPoint := d0
  out := o ∘ e
  left := Equiv.refl X
  right := e
  left_point := rfl
  right_point := point
  result_point := rfl
  left_action _ _ := rfl
  right_observation y := by simp

namespace Combination
variable {x0 : X} {y0 : Y} {d0 : D} {o : Y → D}
variable {Z : Type uZ} [MulAction M Z]
variable (C : Combination M x0 y0 d0 o Z)

/-- Every exact recovery induces the common-carrier identification. -/
def overlap : X ≃ Y := C.left.symm.trans C.right

theorem overlap_point : C.overlap x0 = y0 := by
  calc
    C.overlap x0 = C.right (C.left.symm (C.left C.point)) :=
      congrArg (fun x => C.right (C.left.symm x)) C.left_point.symm
    _ = C.right C.point := by simp
    _ = y0 := C.right_point

theorem out_eq (z : Z) : C.out z = o (C.right z) := by
  simpa using C.right_observation (C.right z)

/-- Complete action reduct recovery through the chosen left identification. -/
theorem left_reduct : (fun (m : M) (x : X) => C.left (m • C.left.symm x)) =
    (fun m x => m • x) := by
  funext m x
  rw [C.left_action, C.left.apply_symm_apply]

/-- Complete observation reduct recovery through the chosen right identification. -/
theorem right_reduct : C.out ∘ C.right.symm = o := funext C.right_observation

/-- The result is derived from the native action law for every observer. -/
theorem mixed (m n : M) (z : Z) : C.out ((m*n) • z) = C.out (m • (n • z)) := by
  rw [mul_smul]

/-- Fixed overlap and recovery force all observed action results, even in an
alternative joint carrier. No invariance premise is introduced. -/
theorem action_output (e : X ≃ Y) (he : C.overlap = e) (m : M) (x : X) :
    C.out (m • C.left.symm x) = o (e (m • x)) := by
  rw [C.out_eq]
  have hr (z : Z) : C.right z = e (C.left z) := by
    rw [← he]
    simp [overlap]
  rw [hr, C.left_action, C.left.apply_symm_apply]

theorem output (e : X ≃ Y) (he : C.overlap = e) (x : X) :
    C.out (C.left.symm x) = o (e x) := by
  rw [C.out_eq, ← he]
  rfl

end Combination

@[simp] theorem combine_overlap (e : X ≃ Y) (point : e x0 = y0) :
    (combine (M := M) x0 y0 d0 o e point).overlap = e := rfl

/-- Canonical construction agrees with direct native function composition. -/
theorem combine_out (e : X ≃ Y) (point : e x0 = y0) :
    (combine (M := M) x0 y0 d0 o e point).out = o ∘ e := rfl

end NativeModelCombination

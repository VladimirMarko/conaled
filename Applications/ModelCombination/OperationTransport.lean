module
public import Mathlib.Algebra.Group.TransferInstance
public import Applications.ModelCombination.ActionObservation

/-! Operation transport with explicit invertible recovery, independent of signatures. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace NativeModelCombination.OperationTransport
universe u v w
variable {X : Type u} {Y : Type v} {I : Type w}

/-- Transport a supplied state-valued operation, retaining every argument. -/
def operation (e : X ≃ Y) (op : (I → Y) → Y) (xs : I → X) : X :=
  e.symm (op (e ∘ xs))

@[simp] theorem map_operation (e : X ≃ Y) (op : (I → Y) → Y) (xs : I → X) :
    e (operation e op xs) = op (e ∘ xs) := e.apply_symm_apply _

theorem recover_operation (e : X ≃ Y) (op : (I → Y) → Y) (ys : I → Y) :
    e (operation e op (e.symm ∘ ys)) = op ys := by
  simp [operation, Function.comp_def]

/-- A native binary interface to tuple transport. -/
def binary (e : X ≃ Y) (op : Y → Y → Y) (x y : X) : X :=
  operation e (fun a : Bool → Y => op (a false) (a true)) (fun b => if b then y else x)

@[simp] theorem binary_def (e : X ≃ Y) (op : Y → Y → Y) (x y : X) :
    binary e op x y = e.symm (op (e x) (e y)) := rfl

@[simp] theorem map_binary (e : X ≃ Y) (op : Y → Y → Y) (x y : X) :
    e (binary e op x y) = op (e x) (e y) := e.apply_symm_apply _

theorem recover_binary (e : X ≃ Y) (op : Y → Y → Y) (x y : Y) :
    e (binary e op (e.symm x) (e.symm y)) = op x y := by simp

/-- The native binary data are exactly Mathlib's existing algebraic transfer. -/
theorem binary_eq_mul (e : X ≃ Y) (op : Y → Y → Y) :
    binary e op = @Mul.mul X (@Equiv.mul X Y e ⟨op⟩) := rfl

theorem associative (e : X ≃ Y) (op : Y → Y → Y) (h : ∀ x y z, op (op x y) z = op x (op y z)) :
    ∀ x y z, binary e op (binary e op x y) z = binary e op x (binary e op y z) := by
  let : Semigroup Y := { mul := op, mul_assoc := h }
  let : Semigroup X := e.semigroup
  exact mul_assoc

theorem left_unit (e : X ≃ Y) (op : Y → Y → Y) (unit : Y)
    (h : ∀ y, op unit y = y) (x : X) : binary e op (e.symm unit) x = x := by
  apply e.injective
  simp only [map_binary, Equiv.apply_symm_apply, h]

theorem right_unit (e : X ≃ Y) (op : Y → Y → Y) (unit : Y)
    (h : ∀ y, op y unit = y) (x : X) : binary e op x (e.symm unit) = x := by
  apply e.injective
  simp only [map_binary, Equiv.apply_symm_apply, h]

/-- An actual common operation must agree through the chosen identification. -/
theorem common_iff (e : X ≃ Y) (native : X → X → X) (supplied : Y → Y → Y) :
    native = binary e supplied ↔ ∀ x y, e (native x y) = supplied (e x) (e y) := by
  constructor
  · intro h x y; rw [h, map_binary]
  · intro h; funext x y; apply e.injective; rw [map_binary]; exact h x y
end NativeModelCombination.OperationTransport

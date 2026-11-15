import Init.Data.Float

/-!
# Literal floating decimal execution

The operation data carry no decoder or arithmetic laws. Both concrete folds use
their own format's actual natural conversion, addition and division by ten. The
model bridges concern the pinned logical definitions, not native correspondence.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Numerals.Floating

/-- Exactly the operations of the source decimal step, without observation laws. -/
structure Operations (α : Type) where
  zero : α
  convert : Nat → α
  add : α → α → α
  divideTen : α → α

def fraction {α : Type} (ops : Operations α) (digits : List Nat) : α :=
  digits.foldr (fun d x => ops.divideTen (ops.add (ops.convert d) x)) ops.zero

def operations64 : Operations Float where
  zero := 0
  convert := Nat.toFloat
  add := Float.add
  divideTen x := x / 10

def operations32 : Operations Float32 where
  zero := 0
  convert := Nat.toFloat32
  add := Float32.add
  divideTen x := x / 10

def fraction64 (digits : List Nat) : Float :=
  digits.foldr (fun (d : Nat) (x : Float) => (d.toFloat + x) / 10) 0

def fraction32 (digits : List Nat) : Float32 :=
  digits.foldr (fun (d : Nat) (x : Float32) => (d.toFloat32 + x) / 10) 0

theorem fraction_operations64 (digits : List Nat) :
    fraction operations64 digits = fraction64 digits := rfl

theorem fraction_operations32 (digits : List Nat) :
    fraction operations32 digits = fraction32 digits := rfl

def fractionModel64 (digits : List Nat) : Float.Model :=
  digits.foldr (fun (d : Nat) (x : Float.Model) =>
    (d.toFloat.toModel + x) / (10 : Float).toModel) (0 : Float).toModel

def fractionModel32 (digits : List Nat) : Float32.Model :=
  digits.foldr (fun (d : Nat) (x : Float32.Model) =>
    (d.toFloat32.toModel + x) / (10 : Float32).toModel) (0 : Float32).toModel

theorem fraction64_nil : fraction64 [] = 0 := rfl
theorem fraction32_nil : fraction32 [] = 0 := rfl

theorem fraction64_cons (d : Nat) (ds : List Nat) :
    fraction64 (d :: ds) = (d.toFloat + fraction64 ds) / 10 := rfl

theorem fraction32_cons (d : Nat) (ds : List Nat) :
    fraction32 (d :: ds) = (d.toFloat32 + fraction32 ds) / 10 := rfl

theorem fraction64_model (digits : List Nat) :
    (fraction64 digits).toModel = fractionModel64 digits := by
  induction digits with
  | nil => rfl
  | cons d ds ih =>
    change (d.toFloat.toModel + (fraction64 ds).toModel) / (10 : Float).toModel =
      (d.toFloat.toModel + fractionModel64 ds) / (10 : Float).toModel
    rw [ih]

theorem fraction32_model (digits : List Nat) :
    (fraction32 digits).toModel = fractionModel32 digits := by
  induction digits with
  | nil => rfl
  | cons d ds ih =>
    change (d.toFloat32.toModel + (fraction32 ds).toModel) / (10 : Float32).toModel =
      (d.toFloat32.toModel + fractionModel32 ds) / (10 : Float32).toModel
    rw [ih]

private theorem zeroStep64 : (((0 : Nat).toFloat + (0 : Float)) / 10) = 0 := by
  decide +kernel

private theorem zeroStep32 : (((0 : Nat).toFloat32 + (0 : Float32)) / 10) = 0 := by
  decide +kernel

theorem fraction64_replicate_zero (n : Nat) : fraction64 (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, fraction64_cons, ih]
    exact zeroStep64

theorem fraction32_replicate_zero (n : Nat) : fraction32 (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, fraction32_cons, ih]
    exact zeroStep32

end Numerals.Floating

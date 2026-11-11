import SquareKit.DiagonalConstruction
import Compiler

/-! Positive cases, rejected laws, and the existing compiler applied to the diagonal. -/

namespace Examples.DiagonalConstruction
open SquareKit.DiagonalConstruction

def positive : Selected (fun c _ : Bool => c) (fun _ => false) where
  code := false
  represents _ := rfl

example : (fun _ : Bool => false) positive.witness = positive.witness := positive.fixed
example : positive.witness = false := rfl

example : Function.Surjective (fun _ _ : Unit => ()) := by
  intro f
  exact ⟨(), funext fun x => Subsingleton.elim _ _⟩

example : ∃ y : Unit, id y = y := baseline (fun _ _ : Unit => ())
  (by intro f; exact ⟨(), funext fun x => Subsingleton.elim _ _⟩) id

example (e : Nat → Nat → Bool) : ¬ Function.Surjective e := no_boolean_surjection e

/-- Same evaluation and step laws, but the new target code is not covered. -/
def partialPresentation : Map (fun _ _ : Unit => true) id
    (fun b _ : Bool => !b) id where
  code := fun _ => false
  value := id
  evaluation _ _ := rfl
  step _ := rfl

def sourceSelected : Selected (fun _ _ : Unit => true) id where
  code := ()
  represents _ := rfl

/-- The specific extra interpretation law fails, despite both local map laws. -/
theorem cannot_transfer_representation :
    ¬ ∀ b, (!partialPresentation.code sourceSelected.code) =
      diagonal (fun c _ : Bool => !c) id b := by
  intro h
  have hf := h true
  contradiction

example : ¬ Function.Surjective partialPresentation.code := by
  intro h
  obtain ⟨a, ha⟩ := h true
  contradiction

def flip : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b <;> rfl

def flippedPositive :=
  (presentationMap flip flip (fun c _ : Bool => c) (fun _ => false)).selected
    flip.surjective positive

example : flippedPositive.code = true := rfl
example : flippedPositive.witness = true := rfl
example : restep flip (fun _ => false) flippedPositive.witness =
    flippedPositive.witness := flippedPositive.fixed

/-- Invertible presentation change retains and recovers the selected result. -/
example (a : Bool ≃ Bool) :
    a.symm (((presentationMap a a (fun c _ : Bool => c) (fun _ => false)).selected
      a.surjective positive).witness) = positive.witness := recover_witness a a positive

example (a : Bool ≃ Bool) :
    a.symm (((presentationMap a a (fun c _ : Bool => c) (fun _ => false)).selected
      a.surjective positive).code) = positive.code := recover_code a a positive

def erased (b : Bool) : Selected (fun _ _ : Bool => ()) id where
  code := b
  represents _ := rfl

/-- Fixed-point values alone cannot recover the retained code. -/
theorem witness_forgetting_not_injective :
    ¬ Function.Injective (fun s : Selected (fun _ _ : Bool => ()) id => s.witness) := by
  intro h
  have he := congrArg Selected.code (h (show (erased false).witness = (erased true).witness from rfl))
  contradiction

namespace Compiled
open CategoricalCompiler

inductive Prim : Ty → Ty → Type where
  | evaluate : Prim (.prod .base .base) .base
  | step : Prim .base .base

def meaning {A : Type} (e : A → A → A) (h : A → A) :
    {a b : Ty} → Prim a b → Val A a → Val A b
  | _, _, .evaluate, p => e p.1 p.2
  | _, _, .step, y => h y

/-- Both uses refer to the same bound variable. -/
def term : Term Prim [.base] .base :=
  .prim .step (.prim .evaluate (.pair (.var .here) (.var .here)))

theorem compiled_diagonal {A : Type} (e : A → A → A) (h : A → A)
    (K : Target Prim) (S : Sound A K (meaning e h)) (a : A) :
    S.denote (compile K term) ((), a) = diagonal e h a :=
  compile_sound K S term ((), a)

/-- Compilation reuses the conditional proof, without manufacturing representation. -/
theorem compiled_selected {A : Type} {e : A → A → A} {h : A → A}
    (K : Target Prim) (S : Sound A K (meaning e h)) (s : Selected e h) :
    S.denote (compile K term) ((), s.code) = s.witness := by
  rw [compiled_diagonal]
  exact s.fixed

example : (rawSound (meaning (fun c _ : Bool => c) (fun _ => false))).denote
    (compile (rawTarget Prim) term) ((), positive.code) = false :=
  compiled_selected (rawTarget Prim) (rawSound _) positive

end Compiled
end Examples.DiagonalConstruction

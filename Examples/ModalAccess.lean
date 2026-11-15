import SquareKit.Internal.ModalAccess.Fragment

/-! The frozen #297 Task M client and two admissible substitutions (#375).
The ordinary, explicit restricted-context client remains a plain Lean function. -/
namespace Examples.ModalAccess
open SquareKit.Internal.ModalAccess

abbrev ac : Word := [.a, .c]
abbrev bc : Word := [.b, .c]
theorem κ : Cell ac bc := .tensor .alpha (.id [.c])

def Γ : Ctx 2 := fun i => if i = 0 then ac else []

def selected : Selected Γ bc :=
  ⟨.var 0 κ, .refl (.var 0 κ)⟩

theorem no_ordinary_key : ¬ Cell [] bc := by
  intro k
  have h := k.length
  contradiction

theorem no_illicit_replacement : ¬ Cell [] ac := by
  intro k
  have h := k.length
  contradiction

/-- Full valuations induce all lock-indexed environments; inaccessible entries
cannot be requested because the required cell has no constructor derivation. -/
def valuation (x y : Bool) (w : Word) : Env Γ w :=
  fun i _ => if i = 0 then x else y

def native (x : Bool) : Observation := ⟨x, ⟨rfl⟩⟩

theorem exact_native_comparison (x y : Bool) :
    selected.eval (valuation x y bc) = native x := rfl

/-- First rename x to fresh z and replace the ordinary variable by false.
Then negate each fresh variable. The declaration shapes agree, so fresh names
use the same de Bruijn indices. Both substitutions are typed at ac/1. -/
def σ : Sub Γ Γ := fun i => if i = 0 then .var i (.id (Γ i)) else .lit false
def τ : Sub Γ Γ := fun i => .neg (.var i (.id (Γ i)))

/-- The independently expected outcome is the negation of the permitted input,
including its reflexive identity certificate, after the two substitutions. -/
theorem two_substitutions (x y : Bool) :
    ((selected.subst σ).subst τ).eval (valuation x y bc) = native (!x) := by
  rw [Selected.eval_two_substitutions]
  rfl

theorem native_two_substitutions (x y : Bool) :
    ((selected.subst σ).subst τ).eval (valuation x y bc) =
      native (!x) := two_substitutions x y

/-- Every generated Boolean term at these locks is independent of y, including
terms produced by any admissible substitution. -/
theorem locked_environment_independent (x y y' : Bool) :
    valuation x y bc = valuation x y' bc := by
  funext i k
  by_cases h : i = 0
  · simp [valuation, h]
  · exact False.elim (no_ordinary_key (by simpa [Γ, h] using k))

theorem all_terms_independent (t : Term Γ bc) (x y y' : Bool) :
    t.eval (valuation x y bc) = t.eval (valuation x y' bc) := by
  rw [locked_environment_independent x y y']

theorem all_selected_independent (t : Selected Γ bc) (x y y' : Bool) :
    t.eval (valuation x y bc) = t.eval (valuation x y' bc) := by
  rw [locked_environment_independent x y y']

theorem ordinary_projection_not_definable :
    ¬ ∃ t : Term Γ bc, ∀ x y, t.eval (valuation x y bc) = y := by
  rintro ⟨t, h⟩
  have same := all_terms_independent t false false true
  rw [h, h] at same
  contradiction

theorem ordinary_projection_does_not_factor :
    ¬ ∃ f : Bool → Bool, ∀ x y : Bool, f x = y := by
  rintro ⟨f, h⟩
  have same := (h false false).symm.trans (h false true)
  contradiction

/-- Access restriction does not make the result type empty. -/
def closedSelected : Selected Γ bc := ⟨.lit true, .refl (.lit true)⟩

example : selected.eval (valuation true false bc) = native true :=
  exact_native_comparison _ _
example : ((selected.subst σ).subst τ).eval (valuation true false bc) = native false :=
  two_substitutions _ _
example : ((selected.subst σ).subst τ).eval (valuation false true bc) = native true :=
  two_substitutions _ _

/-- A nonconstant identity family detects fiber changes, rather than only
checking the reflexive diagonal selected by the frozen client. -/
def trueFiber : Env Γ bc → Type := IdFamily (.var 0 κ) (.lit true)

example : trueFiber (valuation true false bc) := ⟨rfl⟩

theorem false_fiber_empty : IsEmpty (trueFiber (valuation false true bc)) :=
  ⟨fun p => Bool.noConfusion p.down⟩

example : IdFamily ((Term.var 0 κ).subst τ) ((Term.lit true).subst τ) =
    fun ρ => trueFiber (τ.eval ρ) := IdFamily.subst _ _ _

/-- The key action also transports the entire selected dependent package. -/
example (x y : Bool) :
    (Selected.key (⟨.var 0 (.id ac), .refl _⟩ : Selected Γ ac) κ).eval
      (valuation x y bc) = native x := by
  rw [Selected.eval_key]
  rfl

end Examples.ModalAccess

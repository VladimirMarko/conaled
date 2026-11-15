import SquareKit.Internal.ModalAccess.Comprehension
import Examples.ModalAccess
import Mathlib.Data.Fintype.Card

/-! A native restricted-context contract and its dependent telescope realization.
The later finite-index type has cardinality two or three, depending on the
accessible Boolean. Both locks and the selected index remain observable. -/
namespace Examples.ModalComprehension
open SquareKit.Internal.ModalAccess
open SquareKit.Internal.ModalAccess.Comprehension
open Examples.ModalAccess (ac bc κ Γ valuation)

/-- Native specification: no modal annotations are required by the client. -/
def size (b : Bool) : Nat := if b then 3 else 2
abbrev Result := (b : Bool) × Fin (size b)

def largest (b : Bool) : Fin (size b) := by
  cases b
  · exact ⟨1, by decide⟩
  · exact ⟨2, by decide⟩

def native (b : Bool) : Result := ⟨b, largest b⟩

def nativeChange (r : Result) : Result := native (!r.1)

theorem native_twice (b : Bool) : nativeChange (nativeChange (native b)) = native b := by
  cases b <;> rfl

example : (native false).2.val = 1 := rfl
example : (native true).2.val = 2 := rfl
example : Fintype.card (Fin (size false)) = 2 := rfl
example : Fintype.card (Fin (size true)) = 3 := rfl

theorem fibers_not_equivalent : ¬ Nonempty (Fin (size false) ≃ Fin (size true)) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr e
  simp [size] at h

abbrev Base := Env Γ bc
def later : Base → Type := fun ρ => Fin (size (ρ 0 κ))
def baseContext : Context Base := locked Γ bc
def extended : Context (Sigma later) := .ext baseContext later

/-- The later declaration is an actual newest variable of the extended context. -/
def indexTerm : Comprehension.Term extended (fun e => later e.1) := .variable

def observe (e : Sigma later) : Result := ⟨e.1 0 κ, indexTerm.eval e⟩

def selected (b y : Bool) : Sigma later := ⟨valuation b y bc, largest b⟩

theorem native_comparison (b y : Bool) : observe (selected b y) = native b := rfl

/-- First change negates every accessible base value and chooses the largest
index of the resulting fiber. It is a typed dependent extension substitution. -/
def changeBase (e : Sigma later) : Base :=
  Examples.ModalAccess.τ.eval e.1

def change : Sub extended extended :=
  .extend later changeBase (.primitive (fun e => largest (changeBase e 0 κ)))

/-- Full dependent observation, with both selected components retained. -/
def resultTerm : Comprehension.Term extended (fun _ => Result) := .primitive observe

theorem change_observation (e : Sigma later) :
    observe (change.eval e) = nativeChange (observe e) := rfl

theorem two_changes (b y : Bool) :
    ((resultTerm.substitute change).substitute change).eval (selected b y) = native b := by
  rw [Comprehension.Term.two_substitutions]
  change observe (change.eval (change.eval (selected b y))) = native b
  rw [change_observation, change_observation, native_comparison, native_twice]

/-- The substitution's second component really has the reindexed later type. -/
example : Comprehension.Term extended (Model.reindex later changeBase) :=
  .primitive (fun e => largest (changeBase e 0 κ))

/-- Keying an extension transports its index without resetting it. -/
def earlier : Env Γ ac → Type := fun ρ => Fin (size (ρ 0 (.id ac)))

def keyed : Sub extended (.ext (locked Γ ac) earlier) := keyExtension κ earlier

theorem key_keeps_index (e : Sigma later) : (keyed.eval e).2 = e.2 := rfl

theorem key_keeps_selected (b y : Bool) :
    (⟨(keyed.eval (selected b y)).1 0 (.id ac),
      (keyed.eval (selected b y)).2⟩ : Result) = native b := rfl

/-- The actual key square satisfies the constructed pullback universal property. -/
theorem key_pullback_reconstruct :
    (id : Sigma later → Sigma later) =
      Model.pullbackFactor (Env.key κ) keyed.eval Model.projection (fun _ => rfl) := by
  exact Model.pullbackFactor_unique (Env.key κ) keyed.eval Model.projection
    (fun _ => rfl) id rfl rfl

/-- The generic comprehension universal property reconstructs this actual
parameter substitution from its base and selected typed component. -/
theorem change_from_components (f : Sigma later → Sigma later)
    (hp : ∀ e, (f e).1 = changeBase e)
    (hq : ∀ e, HEq (f e).2 (largest (changeBase e 0 κ))) : f = change.eval :=
  Model.pair_unique f changeBase (fun e => largest (changeBase e 0 κ)) hp hq

/-- No family or term over this restricted context can inspect y. The statement
covers even local native primitives, not just the old Boolean grammar. -/
theorem selected_independent (b y y' : Bool) : selected b y = selected b y' := by
  apply Sigma.ext (Examples.ModalAccess.locked_environment_independent b y y')
  rfl

theorem all_observers_independent {R : Type} (f : Sigma later → R) (b y y' : Bool) :
    f (selected b y) = f (selected b y') := by rw [selected_independent b y y']

theorem forbidden_dependency :
    ¬ ∃ f : Sigma later → Bool, ∀ b y, f (selected b y) = y := by
  rintro ⟨f, h⟩
  have same := all_observers_independent f false false true
  rw [h, h] at same
  contradiction

/-- A substitution trying to introduce ordinary y into the restricted base
would have to realize this impossible component. -/
theorem forbidden_substitution :
    ¬ ∃ σ : Sub extended baseContext, ∀ b y, σ.eval (selected b y) 0 κ = y := by
  rintro ⟨σ, h⟩
  exact forbidden_dependency ⟨fun e => σ.eval e 0 κ, h⟩

def reset (b : Bool) : Result := ⟨b, ⟨0, by cases b <;> decide⟩⟩

theorem reset_loses_selected (b : Bool) : reset b ≠ native b := by
  intro h
  have hv := congrArg (fun r : Result => r.2.val) h
  cases b <;> contradiction

/-- #375's selected identity witness and Boolean are recovered exactly. -/
example (b y : Bool) :
    (oldSelected Examples.ModalAccess.selected).eval (valuation b y bc) =
      Examples.ModalAccess.native b := by
  rw [recover_selected]
  exact Examples.ModalAccess.exact_native_comparison b y

example : identityType (SquareKit.Internal.ModalAccess.Term.var 0 κ) (.lit true) =
    Examples.ModalAccess.trueFiber := rfl

example (b y : Bool) :
    (booleanTerm (SquareKit.Internal.ModalAccess.Term.var 0 κ)).eval (valuation b y bc) = b := rfl

example : ¬ Cell [] bc := Examples.ModalAccess.no_ordinary_key
example : ¬ Cell [] ac := Examples.ModalAccess.no_illicit_replacement

end Examples.ModalComprehension

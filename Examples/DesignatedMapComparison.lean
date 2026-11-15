import SquareKit.Internal.DesignatedMap.Interpretations
import SquareKit.Internal.DesignatedMap.GroupoidControl
import Examples.LocalUniversesBoundary
import Examples.ReferenceDependentCalculus
import Mathlib.Data.Fin.Rev

/-! Checked applications and failed applicability controls for #366. The map
syntax is a restricted schema, not the quantified dependent source theorem. -/
namespace Examples.DesignatedMapComparison
set_option backward.isDefEq.respectTransparency false
open SquareKit.Internal.DesignatedMap
open Extensional

/-- An actual permutation gives equivalence of the actual comparison map. -/
def permutedRestriction {A Z : Type} (e : A ≃ A) :
    (A → Z) ≃ Cocone (id : A → A) id Z :=
  (Equiv.arrowCongr e.symm (Equiv.refl Z)).trans (Boundary.identityRestriction A Z)

def family (n : Nat) : Experiment where
  N := Fin (n + 2)
  L := Fin (n + 2)
  R := Fin (n + 2)
  S := Fin (n + 2)
  Z := Fin (n + 2)
  north := id
  west := id
  boundary := Boundary.identitySpan _
  universal := Boundary.identityUniversal _
  target := ⟨Fin.rev, Fin.rev, rfl⟩
  comparisonEquiv := fromEquiv (permutedRestriction Fin.revPerm)

/-- The derived cancellation witness selects the inverse of reversal. The
expected inverse is computed independently, then identified by fiber uniqueness. -/
theorem selected_inverse (n : Nat) :
    (family n).selected id = ⟨Fin.rev, by funext i; exact Fin.rev_rev i⟩ :=
  ((family n).result id).contraction _

/-- Two nonidentity substitutions change the actual fiber from Fin(n+2) to
Fin(2*n+3); both the selected inverse and its dependent fiber proof survive. -/
theorem selected_inverse_twice (n : Nat) :
    (((family ∘ (fun m => m + 1)) ∘ (fun k => 2 * k)) n).selected id =
      ⟨Fin.rev, by funext i; exact Fin.rev_rev i⟩ := selected_inverse (2 * n + 1)

example : ((((family ∘ (fun m => m + 1)) ∘ (fun k => 2 * k)) 2).selected id).val (0 : Fin 7) =
    (6 : Fin 7) := by
  rw [selected_inverse_twice]
  rfl

/-- The small code closures admit a dependent function and an actual fiber;
these native constructions do not encode quantification over the code object. -/
def lastFamily : (Represented.pi ⟨Nat⟩ (fun n => ⟨Fin (n + 1)⟩)).carrier := Fin.last

example : (Represented.applyPi lastFamily 6).val = 6 := rfl

example : (Represented.fiberCodeEquiv ⟨Fin 3⟩ ⟨Fin 3⟩ Fin.rev 0)
    ⟨2, ⟨⟨rfl⟩⟩⟩ = ⟨2, rfl⟩ := rfl

namespace Syntax
open ActionSource

def Variables : Kind → Type | .map => Bool | .cone => Unit

def env : ∀ s, Variables s → Value (Z := Nat) (id : Nat → Nat) id s
  | .map, false => fun x => x + 1
  | .map, true => fun x => 2 * x
  | .cone, () => ⟨id, id, rfl⟩

def client : Expr Variables .cone :=
  .post (.comp (.var true) (.var false)) (.var ())

def first : ∀ s, Variables s → Expr Variables s
  | .map, false => .var true
  | .map, true => .comp (.var true) (.var false)
  | .cone, () => .var ()

def second : ∀ s, Variables s → Expr Variables s
  | .map, false => .comp (.var false) (.var false)
  | .map, true => .var false
  | .cone, () => .var ()

example : (direct id id env client).left 3 = 8 := rfl
example : (direct id id env (client.subst first)).left 3 = 14 := rfl

theorem compared :
    (GuardedAction.encode ((client.subst first).subst second)).eval
        (GuardedAction.algebra id id)
        (fun v => GuardedAction.inject id id (env v.1 v.2)) =
      GuardedAction.Value.cone ⟨(fun x => x + 4), (fun x => x + 4), rfl⟩ := by
  rw [GuardedAction.compare_twice]
  apply congrArg GuardedAction.Value.cone
  apply Cocone.ext <;> funext x <;>
    simp [direct, client, first, second, Expr.subst, env, Cocone.post, Function.comp_def,
      Nat.add_assoc]

/-- A dependent selected tail over the interpreted output. -/
def outputFamily : Represented.Ty Nat := fun n => ⟨Fin (n + 1)⟩
def output : Nat → Nat := (direct id id env ((client.subst first).subst second)).left
def lastOutput (n : Nat) : Fin (output n + 1) := Fin.last (output n)
def extended : Nat → Represented.Ext outputFamily := Represented.pair output lastOutput

theorem extended_represents : Represented.represent outputFamily extended = ⟨output,lastOutput⟩ :=
  (Represented.represent outputFamily).apply_symm_apply ⟨output,lastOutput⟩

/-- Arbitrary changes of the base preserve the represented selected payload,
including its dependent finite bound. The general representation theorem,
rather than a separate evaluation proof, supplies the comparison. -/
theorem extended_twice {Δ Θ : Type} (σ : Δ → Nat) (τ : Θ → Δ) :
    Represented.represent outputFamily ((extended ∘ σ) ∘ τ) =
      ⟨(output ∘ σ) ∘ τ, fun θ => lastOutput (σ (τ θ))⟩ := by
  exact Represented.represent_natural outputFamily extended (σ ∘ τ)

example : ((((extended ∘ (fun n => n + 1)) ∘ (fun n => 2 * n)) 2).2).val = 9 := by
  have h := extended_twice (fun n => n + 1) (fun n => 2 * n)
  exact congrArg (fun p => (p.2 2).val) h

example : (extended 3).1 = 7 ∧ (extended 3).2.val = 7 := by
  have h := congrArg (fun p => (p.1 3, (p.2 3).val)) extended_represents
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
end Syntax

/-- Retain a selected higher witness from the non-orbifold algebraic client.
It is a regression, not a dependent higher model built by this experiment. -/
example : Examples.SecondIdentity.labelObservation
    (LocalUniversesBoundary.Witnesses.higherTwice.eval
      Examples.SecondIdentity.labelInput) = 1 :=
  LocalUniversesBoundary.Witnesses.higher_observation
end Examples.DesignatedMapComparison

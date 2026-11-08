import SquareKit.Internal.NominalBodies
import Examples.NominalTelescope

/-! Independent arithmetic expectations for the varying-body contract (#382). -/
namespace Examples.NominalBodies
open SquareKit.Internal.NominalTelescope
open SquareKit.Internal.NominalBodies
open Examples.NominalTelescope (N Z σ τ ρ selectedA selectedB selectedR)

/-- Uses both bound data and a free leaf occurring only in the body. -/
def mixed : Body := .add (.add .first .second) (.free (.var 2))
def sum : Body := .add .first .second

def q : SquareKit.Internal.NominalBodies.Abstraction N Z := abstractBody N Z mixed

/-- At the same free parameters and input, the old selection is 1 whereas
addition of bound inputs is 3. A fixed projection cannot implement both. -/
theorem sum_selected : observeAbstract
    (substitute τ (substitute σ (abstractBody N Z sum))) selectedA selectedB =
      (⟨7, ⟨3, by decide⟩⟩ : Observation) := by
  exact (two_substitutions _ σ τ ρ selectedA selectedB).trans
    ((observeAbstract_eq _ _ _).trans rfl)

theorem second_selected : observeAbstract
    (substitute τ (substitute σ (abstractBody N Z .second))) selectedA selectedB =
      (⟨7, ⟨1, by decide⟩⟩ : Observation) := by
  exact (two_substitutions _ σ τ ρ selectedA selectedB).trans
    ((second_specialization _ _).trans rfl)

theorem mixed_selected : observeAbstract (substitute τ (substitute σ q))
    selectedA selectedB = (⟨7, ⟨6, by decide⟩⟩ : Observation) := by
  exact (two_substitutions _ σ τ ρ selectedA selectedB).trans
    ((observeAbstract_eq _ _ _).trans rfl)

example : (substituteProgram τ (substituteProgram σ ⟨N,Z,q⟩)) =
    substituteProgram (fun x => (σ x).subst τ) ⟨N,Z,q⟩ := substitute_comp _ σ τ
example : substituteProgram .var ⟨N,Z,q⟩ = ⟨N,Z,q⟩ := substitute_id _

/-- Alpha quotient retains the generated body, even if numerical observations
at some inputs happen to agree. -/
example : abstractBody N Z sum ≠ abstractBody N Z .second := by
  intro h
  have hh := congrArg body h
  change sum = Body.second at hh
  cases hh

/-- Replacing the varied body by the old projection changes selected data. -/
theorem reset_body_fails :
    observeAbstract (substitute τ (substitute σ (abstractBody N Z sum))) selectedA selectedB ≠
    observeAbstract (substitute τ (substitute σ (abstractBody N Z .second))) selectedA selectedB := by
  rw [sum_selected, second_selected]
  decide

theorem reset_value_fails :
    observeAbstract (substitute τ (substitute σ q)) selectedA selectedB ≠
      (⟨7, ⟨0, by decide⟩⟩ : Observation) := by
  rw [mixed_selected]
  decide

/-- Body-only support raises the fresh names, even when the type bounds do not
mention that atom. Substitution images can collide with the old bound names. -/
def bodyOnly : Body := .add .second (.free (.var 8))
def collide : Nat → Expr := fun _ => .var 9

def before : Frame (SquareKit.Internal.NominalBodies.support (.lit 3) (.lit 5) bodyOnly) :=
  Frame.canonical _
def after : Frame (SquareKit.Internal.NominalBodies.support (.lit 3) (.lit 5)
    (bodyOnly.subst collide)) := Frame.canonical _

example : before.name 0 = 9 ∧ after.name 0 = 10 := by decide
example : before.name 1 = 10 ∧ after.name 1 = 11 := by decide
example : (bodyOnly.subst collide).concretize after =
    (bodyOnly.concretize before).subst (under before after collide) :=
  concretize_subst _ (by decide) _ _ _

/-- Freshening keeps the inserted free 9 distinct from the old bound first 9. -/
example : ((bodyOnly.subst collide).concretize after).eval
    (after.env (fun _ => 7) 2 1 0) = 8 := by decide

/-- Failing to freshen changes the inserted free 9 into the first bound value. -/
example : ((bodyOnly.subst collide).concretize before).eval
    (before.env (fun _ => 7) 2 1 0) = 3 := by decide

/-- Modulo is part of the independently stated result contract, rather than a
proof convenience: a sum can wrap and still occupy the same dependent fiber. -/
example : observeAbstract (abstractBody (.lit 2) (.lit 0) sum)
    (ρ := fun _ => 0) ⟨2, by decide⟩ ⟨2, by decide⟩ =
      (⟨2, ⟨1, by decide⟩⟩ : Observation) := by
  rw [observeAbstract_eq]
  rfl

/-- Third-tail specialization retains the selected third field under the same
two changes, and its projection agrees with the new quotient interpreter. -/
theorem third_selected : selectedTail (Z := Examples.NominalTelescope.finalZ)
    selectedA selectedB selectedR =
      (⟨7, ⟨1, by decide⟩, ⟨1, by decide⟩⟩ : TailObservation) := by
  let f := Frame.canonical (SquareKit.Internal.NominalTelescope.support
    Examples.NominalTelescope.finalN Examples.NominalTelescope.finalZ)
  exact (tail_comparison f selectedA selectedB selectedR).symm.trans
    ((tail_two_substitutions N Z σ τ ρ f selectedA selectedB selectedR).trans rfl)

example : (⟨(selectedTail (Z := Examples.NominalTelescope.finalZ)
    selectedA selectedB selectedR).1,
    (selectedTail (Z := Examples.NominalTelescope.finalZ)
      selectedA selectedB selectedR).2.1⟩ : Observation) =
    observeAbstract (abstractBody Examples.NominalTelescope.finalN
      Examples.NominalTelescope.finalZ .second) selectedA selectedB :=
  selectedTail_retains _ _ _

end Examples.NominalBodies

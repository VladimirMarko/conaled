import Examples.LocalUniversesBoundary
import SquareKit.Internal.PathTransport.EmptySubstitution

/-! Ambient terminality and terminality in a full subcategory of reachable
contexts are independent of the present laws. Generated arrows are a different
restriction; the source still constructs its own empty substitutions. -/
namespace Examples.DependentStructureBoundary
open SquareKit.Internal.PathTransport
open SquareKit.Internal.PathTransport.Typed

namespace ReachableLoops

def model : Model where
  Context := Unit
  Family _ := Unit
  Section _ _ := Unit
  Substitution _ _ := Bool
  empty := ()
  extend _ _ := ()
  idSub _ := false
  compSub σ τ := σ || τ
  subTy _ _ := ()
  subTm t _ := t
  weaken _ _ := false
  genericVariable _ _ := ()
  pairSub _ σ _ := σ
  base _ := ()
  fiber _ := ()
  identity _ _ _ := ()
  reflexivity _ _ := ()
  comp_id_left _ := rfl
  comp_id_right σ := Bool.or_false σ
  comp_assoc σ τ υ := Bool.or_assoc σ τ υ
  subTy_id _ := rfl
  subTy_comp _ _ _ := rfl
  subTm_id _ := HEq.rfl
  subTm_comp _ _ _ := HEq.rfl
  base_sub _ := rfl
  fiber_sub _ _ := rfl
  identity_sub _ _ _ _ := rfl
  refl_sub _ _ _ := HEq.rfl
  weaken_pair _ _ _ := rfl
  variable_pair _ _ _ := HEq.rfl
  pair_eta _ _ := rfl
  j _ _ _ _ _ := ()
  j_beta _ _ _ _ _ := HEq.rfl
  j_sub _ _ _ _ _ _ := HEq.rfl

/-- Even the interpreted empty context itself has two ambient endomorphisms. -/
theorem empty_not_terminal : ¬ Subsingleton (model.Substitution model.empty model.empty) := by
  intro h
  exact Bool.noConfusion (@Subsingleton.elim _ h false true)

/-- Merely restricting objects to generated contexts leaves both loops. -/
theorem generated_empty_has_two :
    ∃ s t : model.Substitution (emptyCode model) (emptyCode model), s ≠ t :=
  ⟨false, true, Bool.false_ne_true⟩

end ReachableLoops

/-- Retain the original Bool countermodel, whose inaccessible component has no
map into the selected empty context. It is not the concrete groupoid model. -/
example : ¬ ∃ Γ : LocalUniversesBoundary.MissingTerminal.model.Context,
    ∀ Δ, Nonempty (LocalUniversesBoundary.MissingTerminal.model.Substitution Δ Γ) :=
  LocalUniversesBoundary.MissingTerminal.no_terminal

/-- The chosen source projection exists even in the nonterminal model. -/
def pointEmpty : EmptySubstitution [.base]
    (extendCode emptyCode (baseCode emptyCode)) := Checked.pointContext.emptySubstitution

example : pointEmpty.2.1 ReachableLoops.model = false := rfl

end Examples.DependentStructureBoundary

import SquareKit.Internal.DependentJudgments.NativeTypeModel
import SquareKit.Internal.DependentJudgments.Theory
import SquareKit.Internal.DependentJudgments.ContextualMaps

/-! Checked boundaries of guarded dependent judgments: equality in one decoded
valuation does not generate source equality, and full model maps need not
reflect the definedness of raw applications. -/
namespace Examples.GuardedJudgmentBoundaries
set_option backward.isDefEq.respectTransparency false
open SquareKit SquareKit.GuardedTheory
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.PathTransport.Typed

abbrev native := NativeType.model Unit (fun _ => Unit)

abbrev gamma : Contextual.Expression (Fin 3) := .var 0
abbrev leftFamily : Contextual.Expression (Fin 3) := .var 1
abbrev rightFamily : Contextual.Expression (Fin 3) := .var 2

def typingPremises : List (Contextual.Judgment (Fin 3)) :=
  [Contextual.family gamma leftFamily, Contextual.family gamma rightFamily]

def left_typed : Contextual.Ty (Ω := typingPremises) gamma leftFamily :=
  .hypothesis (by simp [typingPremises])

def right_typed : Contextual.Ty (Ω := typingPremises) gamma rightFamily :=
  .hypothesis (by simp [typingPremises])

/-- Both family parameters have the same decoded meaning in this valuation. -/
def agreeing : Fin 3 → Value native.toStructuralModel :=
  ![.context Unit, .family Unit (fun _ => Unit), .family Unit (fun _ => Unit)]

/-- The same source typing assumptions also admit distinct meanings. -/
def separating : Fin 3 → Value native.toStructuralModel :=
  ![.context Unit, .family Unit (fun _ => Empty), .family Unit (fun _ => Unit)]

theorem agreeing_valid : ∀ p ∈ typingPremises, p.eval (Contextual.algebra native) agreeing := by
  intro p hp
  simp only [typingPremises, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> exact ⟨Unit, (fun _ => Unit), rfl, rfl⟩

theorem separating_valid : ∀ p ∈ typingPremises, p.eval (Contextual.algebra native) separating := by
  intro p hp
  simp only [typingPremises, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨Unit, (fun _ => Empty), rfl, rfl⟩
  · exact ⟨Unit, (fun _ => Unit), rfl, rfl⟩

theorem decoded_families_agree :
    leftFamily.eval (Contextual.algebra native) agreeing =
      rightFamily.eval (Contextual.algebra native) agreeing := rfl

theorem empty_ne_unit : (Empty : Type) ≠ Unit := by
  intro h
  exact Empty.elim (cast h.symm ())

/-- Even with both family judgments derived, equality in one interpretation
cannot be reflected into the source equality judgment. -/
theorem no_source_equality :
    ¬ Nonempty (Contextual.Equal (Ω := typingPremises) leftFamily rightFamily) := by
  rintro ⟨d⟩
  have h := Contextual.interpret d native separating separating_valid
  change Value.family (M := native.toStructuralModel) Unit (fun _ : Unit => Empty) =
    Value.family Unit (fun _ : Unit => Unit) at h
  have e : (fun _ : Unit => Empty) = (fun _ : Unit => Unit) :=
    eq_of_heq (Value.family.inj h).2
  exact empty_ne_unit (congrFun e ())

/-- A full contextual model with one element in every semantic sort. -/
def collapsed : SquareKit.Internal.PathTransport.Typed.Model where
  Context := Unit
  Family _ := Unit
  Section _ _ := Unit
  Substitution _ _ := Unit
  empty := ()
  extend _ _ := ()
  idSub _ := ()
  compSub _ _ := ()
  subTy _ _ := ()
  subTm _ _ := ()
  weaken _ _ := ()
  genericVariable _ _ := ()
  pairSub _ _ _ := ()
  base _ := ()
  fiber _ := ()
  identity _ _ _ := ()
  reflexivity _ _ := ()
  comp_id_left _ := Subsingleton.elim _ _
  comp_id_right _ := Subsingleton.elim _ _
  comp_assoc _ _ _ := rfl
  subTy_id _ := Subsingleton.elim _ _
  subTy_comp _ _ _ := rfl
  subTm_id _ := heq_of_eq (Subsingleton.elim _ _)
  subTm_comp _ _ _ := HEq.rfl
  base_sub _ := rfl
  fiber_sub _ _ := rfl
  identity_sub _ _ _ _ := rfl
  refl_sub _ _ _ := HEq.rfl
  weaken_pair _ _ _ := Subsingleton.elim _ _
  variable_pair _ _ _ := heq_of_eq (Subsingleton.elim _ _)
  pair_eta _ _ := Subsingleton.elim _ _
  j _ _ _ _ _ := ()
  j_beta _ _ _ _ _ := heq_of_eq (Subsingleton.elim _ _)
  j_sub _ _ _ _ _ _ := HEq.rfl

/-- This map preserves the actual full J operation, not only structural data. -/
def collapse : ModelMap native collapsed where
  context _ := ()
  family _ := ()
  mapTm _ := ()
  substitution _ := ()
  empty := rfl
  extend _ := rfl
  id _ := rfl
  comp _ _ := rfl
  subTy _ _ := rfl
  subTm _ _ := HEq.rfl
  weaken _ := HEq.rfl
  mapVariable _ := HEq.rfl
  identity _ _ _ := rfl
  reflexivity _ _ := HEq.rfl
  mapJ _ _ _ _ _ := HEq.rfl

theorem collapse_not_injective : ¬ Function.Injective collapse.context := by
  intro h
  exact empty_ne_unit (h (a₁ := Empty) (a₂ := Unit) rfl)

/-- The family is over Unit, but the substitution has codomain Empty. -/
def malformed : Contextual.Expression (Fin 2) := Contextual.subTy (.var 0) (.var 1)

def mismatched : Fin 2 → Value native.toStructuralModel :=
  ![.family Unit (fun _ => Unit), .substitution Empty Empty ⟨id⟩]

theorem malformed_invalid : malformed.eval (Contextual.algebra native) mismatched = .invalid := by
  simp [malformed, Term.eval, mismatched, Contextual.algebra,
    operation, Value.familyAt, Ne.symm empty_ne_unit]

theorem mapped_malformed_valid :
    malformed.eval (Contextual.algebra collapsed) (Value.map collapse.toStructuralMap ∘ mismatched) =
      .family () () := by
  simp [malformed, Term.eval, mismatched, Contextual.algebra,
    operation, Value.map, collapse, collapsed]

/-- Unconditional naturality on raw expressions would identify an invalid
source result with a defined target family. PartialHom therefore requires a
defined source result; a full ModelMap supplies no converse. -/
theorem no_unconditional_interpretation_map :
    Value.map collapse.toStructuralMap (malformed.eval (Contextual.algebra native) mismatched) ≠
      malformed.eval (Contextual.algebra collapsed)
        (Value.map collapse.toStructuralMap ∘ mismatched) := by
  rw [malformed_invalid, mapped_malformed_valid]
  simp [Value.map]

end Examples.GuardedJudgmentBoundaries

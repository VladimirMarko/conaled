import SquareKit.Internal.DependentJudgments.Comprehension
import SquareKit.Internal.PathTransport.InterpretationMaps

/-! Checked interpretations of annotation-free guarded derivations. This Type
instance checks dependency and selected values; it makes no higher-model claim. -/

namespace Examples.DependentJudgments
set_option backward.isDefEq.respectTransparency false
open SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.DependentJudgments

def typeModel : StructuralModel.{1} where
  Context := Type
  Family Γ := Γ → Type
  Section Γ A := ULift.{1} ((γ : Γ) → A γ)
  Substitution Δ Γ := ULift.{1} (Δ → Γ)
  empty := Unit
  extend Γ A := (γ : Γ) × A γ
  idSub _ := ⟨id⟩
  compSub σ τ := ⟨σ.down ∘ τ.down⟩
  subTy A σ := A ∘ σ.down
  subTm t σ := ⟨fun δ => t.down (σ.down δ)⟩
  weaken _ _ := ⟨Sigma.fst⟩
  genericVariable _ _ := ⟨Sigma.snd⟩
  pairSub _ σ t := ⟨fun δ => ⟨σ.down δ, t.down δ⟩⟩
  base _ := fun _ => Nat
  fiber x := fun γ => Fin (x.down γ + 1)
  identity _ x y := fun γ => PLift (x.down γ = y.down γ)
  reflexivity _ _ := ⟨fun _ => ⟨rfl⟩⟩
  comp_id_left _ := rfl
  comp_id_right _ := rfl
  comp_assoc _ _ _ := rfl
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
  pair_eta _ σ := by cases σ; rfl

def finiteFamily : typeModel.Family Nat := fun n => Fin (n + 1)
def shift : typeModel.Substitution Nat Nat := ⟨fun n => n + 2⟩
def selected : typeModel.Section Nat (typeModel.subTy finiteFamily shift) :=
  ⟨fun n => ⟨n, by change n < n + 2 + 1; omega⟩⟩

/-- The source judgment is interpreted with a value whose fiber depends on the
substituted natural-number parameter. The proof consumes source soundness. -/
theorem interpreted_selected :
    Value.term Nat (typeModel.subTy
      (typeModel.subTy finiteFamily (typeModel.weaken Nat finiteFamily))
      (typeModel.pairSub finiteFamily shift selected))
      (typeModel.subTm (typeModel.genericVariable Nat finiteFamily)
        (typeModel.pairSub finiteFamily shift selected)) =
    Value.term Nat (typeModel.subTy finiteFamily shift) selected := by
  have h := interpret_variablePair typeModel Nat Nat finiteFamily shift selected
  simpa [variablePairRule, SquareKit.GuardedTheory.Atom.eval,
    SquareKit.GuardedTheory.Term.eval, subTm, generic, pair, apply2, apply3,
    algebra, operation] using h

/-- Reading the retained component at 3 obtains 3 in Fin 6. -/
theorem selected_at_three :
    ((typeModel.subTm (typeModel.genericVariable Nat finiteFamily)
      (typeModel.pairSub finiteFamily shift selected)).down 3).val = 3 := by
  have e := (Value.term.inj interpreted_selected).2.2
  have e' := eq_of_heq e
  exact congrArg (fun t => (t.down 3).val) e'

/-- Restriction of a compatible family cannot construct its extension when
an added comparison demands invariance under Bool negation. -/
theorem no_extension_to_bool_symmetry : ¬ ∃ b : Bool, !b = b := by
  rintro ⟨b, h⟩
  cases b <;> cases h

end Examples.DependentJudgments

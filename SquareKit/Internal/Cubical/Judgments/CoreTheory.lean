import SquareKit.Internal.Cubical.Judgments.StructuralRules
import SquareKit.GuardedTheory.Extension

/-! The constructed interpretation validates arbitrary structural source
judgment derivations, including conversion and schematic substitution. -/
namespace SquareKit.Cubical.Source
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Internal.DependentJudgments
universe u

inductive CoreAxiom where
  | comprehension (a : ComprehensionAxiom)
  | subTy | subTm | comp | compIdLeft | compIdRight | compAssoc
  | subTyId | subTmId | subTyComp | subTmComp | termFamily | familyContext

def coreRule : CoreAxiom → Rule signature
  | .comprehension a => comprehensionTheory.rule a
  | .subTy => subTyRule
  | .subTm => subTmRule
  | .comp => compRule
  | .compIdLeft => compIdLeftRule
  | .compIdRight => compIdRightRule
  | .compAssoc => compAssocRule
  | .subTyId => subTyIdRule
  | .subTmId => subTmIdRule
  | .subTyComp => subTyCompRule
  | .subTmComp => subTmCompRule
  | .termFamily => termFamilyRule
  | .familyContext => familyContextRule

def coreTheory : Theory signature where
  Axiom := CoreAxiom
  rule := coreRule

noncomputable def coreModel : GuardedTheory.Model.{0,u+1} coreTheory where
  toAlgebra := algebra
  rules
    | .comprehension a => comprehensionModel.rules a
    | .subTy => subTy_valid
    | .subTm => subTm_valid
    | .comp => comp_valid
    | .compIdLeft => compIdLeftRule_valid
    | .compIdRight => compIdRightRule_valid
    | .compAssoc => compAssocRule_valid
    | .subTyId => subTyIdRule_valid
    | .subTmId => subTmIdRule_valid
    | .subTyComp => subTyCompRule_valid
    | .subTmComp => subTmCompRule_valid
    | .termFamily => termFamilyRule_valid
    | .familyContext => familyContextRule_valid

theorem core_interpret {V : Type} {Ω : List (Judgment V)} {a : Judgment V}
    (d : Derivation coreTheory Ω a) (ρ : V → Value.{u})
    (h : ∀ p ∈ Ω, p.Eval algebra ρ) : a.Eval algebra ρ :=
  d.sound coreModel ρ h

/-- This is substitution for schematic names, distinct from the interpreted
object-context substitutions expressed by subTy/subTm and their source rules. -/
theorem core_interpret_substitute {V W : Type} {Ω : List (Judgment V)} {a : Judgment V}
    (d : Derivation coreTheory Ω a) (σ : V → Expression W) (ρ : W → Value.{u})
    (h : ∀ p ∈ Ω, p.Eval algebra (fun x => (σ x).eval algebra ρ)) :
    (a.subst σ).Eval algebra ρ := by
  rw [Atom.eval_subst]
  exact core_interpret d _ h

/-- Interpretation of an equality proof gives literal equality of dependent
family representations, with no conversion to isomorphisms. -/
theorem core_family_equality {V : Type} {Ω : List (Judgment V)} {a b : Expression V}
    (d : Derivation coreTheory Ω (.eq a b)) (ρ : V → Value.{u})
    (h : ∀ p ∈ Ω, p.Eval algebra ρ) (Γ : Semantics.Context.{u})
    (A B : Semantics.Family Γ) (ha : a.eval algebra ρ = .family Γ A)
    (hb : b.eval algebra ρ = .family Γ B) : A = B := by
  have he := core_interpret d ρ h
  change a.eval algebra ρ = b.eval algebra ρ at he
  have hv := ha.symm.trans (he.trans hb)
  cases hv
  rfl

end SquareKit.Cubical.Source

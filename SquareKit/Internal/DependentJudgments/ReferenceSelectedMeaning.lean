import SquareKit.Internal.DependentJudgments.ReferenceRulePresentation
import SquareKit.Internal.DependentJudgments.ReferenceSoundness
import SquareKit.Institutions.Capabilities

/-! Selected term meanings alongside reference proof translation. The evidence
of this setting is semantic data, not a satisfaction predicate: validity of a
reference judgment is supplied separately by reference soundness. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.Reference.SelectedMeaning
open GuardedTheory Contextual
universe u

structure TermJudgment (V : Type) where
  context : Expression V
  family : Expression V
  term : Expression V

def TermJudgment.claim {V} (p : TermJudgment V) : Claim V :=
  .has (.tm p.context p.family) p.term

def TermJudgment.instantiate {V W} (θ : V → Expression W) (p : TermJudgment V) : TermJudgment W :=
  ⟨p.context.subst θ, p.family.subst θ, p.term.subst θ⟩

variable (M : PathTransport.Typed.Model.{u})

/-- Models here are environments for a fixed independently constructed Id/J
model. The full selected value retains its context, family and section. -/
def setting (V : Type) : Institutions.Setting where
  Sentence := TermJudgment V
  Model := V → Value M.toStructuralModel
  Evidence _ _ := Value M.toStructuralModel

def connection {V W} (θ : V → Expression W) :
    Institutions.Connection (setting M V) (setting M W) where
  sentence := TermJudgment.instantiate θ
  reduct ρ x := (θ x).eval (Contextual.algebra M) ρ
  evidence _ _ := id

/-- Object-language witnesses live in the expression, not in the host's proof
identity. Reference derivations continue to certify the expression's typing. -/
def proofs {V} (Ξ : List (Declaration V)) : Institutions.Proofs (setting M V) where
  Proof p := ULift.{u} (RulePresentation.Proof Ξ p.claim)
  interpret ρ p _ := p.term.eval (Contextual.algebra M) ρ

def proofMap {V W} (Ξ : List (Declaration V)) (θ : V → Expression W) :
    Institutions.ProofMap (connection M θ) (proofs M Ξ)
      (proofs M (Ξ.map (Declaration.instantiate θ))) where
  map _ d := ⟨RulePresentation.transport θ d.down⟩
  commutes ρ p _ := Term.eval_subst (Contextual.algebra M) ρ θ p.term

/-- A semantic realization uses actual contextual target syntax. Its decoder
is not claimed executable: contextual index tests and cubical sections are
noncomputable. The observation may inspect the retained section afterwards. -/
def realization (V : Type) : Institutions.Realization (setting M V) where
  Carrier _ _ := ULift.{u} (Expression V)
  decode ρ _ c := c.down.eval (Contextual.algebra M) ρ

def realizationMap {V W} (θ : V → Expression W) :
    Institutions.RealizationMap (connection M θ) (realization M V) (realization M W) where
  map _ _ c := ⟨c.down.subst θ⟩
  commutes ρ _ c := Term.eval_subst (Contextual.algebra M) ρ θ c.down

def compatible {V W} (Ξ : List (Declaration V)) (θ : V → Expression W) :
    Institutions.Compatible (connection M θ) (proofs M Ξ)
      (proofs M (Ξ.map (Declaration.instantiate θ))) (realization M V) (realization M W) :=
  ⟨proofMap M Ξ θ, realizationMap M θ⟩

/-- The quotation is the actual term certified by the reference judgment. -/
def quote {V} {Ξ : List (Declaration V)} {p : TermJudgment V}
    (_d : Derives Ξ p.claim) : ULift.{u} (Expression V) := ⟨p.term⟩

theorem joint {V W} (Ξ : List (Declaration V)) (θ : V → Expression W)
    (ρ) (p : TermJudgment V) (d : Derives Ξ p.claim) :
    (realization M W).decode ρ _ ((realizationMap M θ).map ρ p (quote d)) =
    (proofs M (Ξ.map (Declaration.instantiate θ))).interpret ρ _
      ((proofMap M Ξ θ).map p ⟨RulePresentation.encode d⟩) := rfl

/-- The independent local operation fold law gives both capability maps their
commuting equations. This remains exact selected-value equality. -/
theorem selected_preserved {V W} (θ : V → Expression W) (ρ) (e : Expression V) :
    (e.subst θ).eval (Contextual.algebra M) ρ =
      e.eval (Contextual.algebra M) ((connection M θ).reduct ρ) :=
  Term.eval_subst (Contextual.algebra M) ρ θ e

/-- A second compilation really composes source templates; it need not be a
renaming and can expand a declaration to a J-built expression. -/
theorem two_stage {V W X} (θ : V → Expression W) (υ : W → Expression X)
    (ρ) (e : Expression V) :
    ((e.subst θ).subst υ).eval (Contextual.algebra M) ρ =
      e.eval (Contextual.algebra M)
        ((connection M θ).reduct ((connection M υ).reduct ρ)) := by
  exact (selected_preserved M υ ρ (e.subst θ)).trans
    (selected_preserved M θ ((connection M υ).reduct ρ) e)

theorem realization_identity {V} (e : Expression V) : e.subst Term.var = e :=
  FinitaryTerm.bind_leaf e

theorem realization_comp {V W X} (θ : V → Expression W) (υ : W → Expression X)
    (e : Expression V) : (e.subst θ).subst υ = e.subst (fun v => (θ v).subst υ) :=
  FinitaryTerm.bind_assoc e θ υ

end SquareKit.Internal.DependentJudgments.Contextual.Reference.SelectedMeaning

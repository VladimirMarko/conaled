import SquareKit.DependentProjectionPresentationSubstitution

/-! Recursive presupposition evidence for contextual judgments. A premise's
boundary is available to a rule case; arbitrary open assumptions must supply
that evidence explicitly. This differs from certificates over bare premise heads. -/
namespace SquareKit.DependentPairJudgments
open DependentTheoryMaps DependentPairPresentations TypedSubstitution

/-- The context case records the types of its variables, needed by variable
lookup. Term equality retains both endpoints at its stated common type. -/
def ContextualBoundary {S : Signature} (R : Rules.{1,1} (Judgment S))
    (H : Judgment S → Type) (j : Judgment S) : Type 1 :=
  match j.form with
  | .ctx => ∀ v, Derivation R H (Judgment.type j.context (j.context.lookup v))
  | .type _ => Derivation R H (Judgment.ctx j.context)
  | .term _ A => Derivation R H (Judgment.ctx j.context) × Derivation R H (Judgment.type j.context A)
  | .typeEq A B => Derivation R H (Judgment.ctx j.context) ×
      Derivation R H (Judgment.type j.context A) × Derivation R H (Judgment.type j.context B)
  | .termEq a b A => Derivation R H (Judgment.ctx j.context) ×
      Derivation R H (Judgment.type j.context A) ×
      Derivation R H (Judgment.term j.context a A) × Derivation R H (Judgment.term j.context b A)

/-- Rule-local boundary reconstruction may use recursively established
presuppositions of the premise derivations. -/
structure LocalContextualBoundary {S : Signature} (R : Rules.{1,1} (Judgment S))
    (H : Judgment S → Type) where
  step : ∀ r : R.Label,
    (∀ i : Fin (R.count r), Derivation R H (R.premise r i)) →
    (∀ i : Fin (R.count r), ContextualBoundary R H (R.premise r i)) →
    ContextualBoundary R H (R.conclusion r)

def contextualPresuppositions {S : Signature} {R : Rules.{1,1} (Judgment S)}
    {H : Judgment S → Type} (laws : LocalContextualBoundary R H)
    (hypotheses : ∀ j, H j → ContextualBoundary R H j) :
    {j : Judgment S} → Derivation R H j → ContextualBoundary R H j
  | _, .hyp h => hypotheses _ h
  | _, .rule r children => laws.step r children
      (fun i => contextualPresuppositions laws hypotheses (children i))

namespace ContextualBoundary
variable {eta : Bool} {R : Rules.{1,1} (Judgment projectionSignature)}
  {H : Judgment projectionSignature → Type}

/-- Formation of an instantiated family is obtained by the admissibility
 theorem, rather than stipulated as another object rule. -/
def familyInstance
    (structural : TheoryMap (structuralRules projectionSignature) R id)
    (laws : Local (R := R) (H := H))
    (stable : ∀ j, H j → Reindexed (R := R) (H := H) j)
    {Γ : Context projectionSignature V} {A : PExpr V} {B : PExpr (Fin 1 ⊕ V)} {a : PExpr V}
    (ctx : Derivation R H (.ctx Γ))
    (family : Derivation R H (.type (.extend Γ A) B))
    (term : Derivation R H (.term Γ a A)) : Derivation R H (.type Γ (Elimination.instantiate B a)) :=
  substitute laws stable family Γ _ (single structural Γ A a ctx term)

/-- Actual boundary proofs for every primitive projection rule, including the
second beta's conversion through first beta. This is not a claim of full-theory
presuppositivity: structural, declaration and congruence cases are separate. -/
def projectionPrimitive
    (structural : TheoryMap (structuralRules projectionSignature) R id)
    (primitive : TheoryMap (rulesOf (ProjectionRule.schema (hasEta := eta))) R id)
    (laws : Local (R := R) (H := H))
    (stable : ∀ j, H j → Reindexed (R := R) (H := H) j)
    (r : ProjectionRule eta)
    (ps : ∀ i : Fin (ProjectionRule.schema r).premises.length,
      Derivation R H ((ProjectionRule.schema r).premises.get i)) :
    ContextualBoundary R H (ProjectionRule.schema r).conclusion := by
  let app (r : ProjectionRule eta)
      (children : ∀ i : Fin (ProjectionRule.schema r).premises.length,
        Derivation R H ((ProjectionRule.schema r).premises.get i)) :
      Derivation R H (ProjectionRule.schema r).conclusion :=
    (primitive.certificate r).graft (fun _ h => h.property ▸ children h.val)
  cases r with
  | formation Γ A B =>
      dsimp [ProjectionRule.schema, ProjectionRule.family] at ps
      exact ps 0
  | pair Γ A B a b =>
      dsimp [ProjectionRule.schema, ProjectionRule.components, ProjectionRule.family] at ps
      exact ⟨ps 0, app (.formation Γ A B)
        (Fin.cases (ps 0) (Fin.cases (ps 1) (Fin.cases (ps 2) (fun i => Fin.elim0 i))))⟩
  | first Γ A B p =>
      dsimp [ProjectionRule.schema, ProjectionRule.argument, ProjectionRule.family] at ps
      exact ⟨ps 0, ps 1⟩
  | second Γ A B p =>
      dsimp [ProjectionRule.schema, ProjectionRule.argument, ProjectionRule.family] at ps
      have first := app (.first Γ A B p) ps
      exact ⟨ps 0, familyInstance structural laws stable (ps 0) (ps 2) first⟩
  | firstBeta Γ A B a b =>
      dsimp [ProjectionRule.schema, ProjectionRule.components, ProjectionRule.family] at ps
      have pair := app (.pair Γ A B a b) ps
      have first := app (.first Γ A B (Projection.pair A B a b))
        (Fin.cases (ps 0) (Fin.cases (ps 1) (Fin.cases (ps 2) (Fin.cases pair (fun i => Fin.elim0 i)))))
      exact ⟨ps 0, ps 1, first, ps 3⟩
  | secondBeta Γ A B a b =>
      dsimp [ProjectionRule.schema, ProjectionRule.components, ProjectionRule.family] at ps
      have pair := app (.pair Γ A B a b) ps
      have second := app (.second Γ A B (Projection.pair A B a b))
        (Fin.cases (ps 0) (Fin.cases (ps 1) (Fin.cases (ps 2) (Fin.cases pair (fun i => Fin.elim0 i)))))
      have firstBeta := app (.firstBeta Γ A B a b) ps
      have fiberEq := rule structural (.familyCong Γ A B (Projection.fst A B (Projection.pair A B a b)) a)
        (Fin.cases (ps 0) (Fin.cases (ps 1) (Fin.cases (ps 2) (Fin.cases firstBeta (fun i => Fin.elim0 i)))))
      have converted := rule structural (.convert Γ (Projection.snd A B (Projection.pair A B a b))
        (Elimination.instantiate B (Projection.fst A B (Projection.pair A B a b)))
        (Elimination.instantiate B a)) (Fin.cases second (Fin.cases fiberEq (fun i => Fin.elim0 i)))
      exact ⟨ps 0, familyInstance structural laws stable (ps 0) (ps 2) (ps 3), converted, ps 4⟩
  | eta allowed Γ A B p =>
      dsimp [ProjectionRule.schema, ProjectionRule.argument, ProjectionRule.family] at ps
      have ty := app (.formation Γ A B)
        (Fin.cases (ps 0) (Fin.cases (ps 1) (Fin.cases (ps 2) (fun i => Fin.elim0 i))))
      have first := app (.first Γ A B p) ps
      have second := app (.second Γ A B p) ps
      have pair := app (.pair Γ A B (Projection.fst A B p) (Projection.snd A B p))
        (Fin.cases (ps 0) (Fin.cases (ps 1) (Fin.cases (ps 2)
          (Fin.cases first (Fin.cases second (fun i => Fin.elim0 i))))))
      exact ⟨ps 0, ty, pair, ps 3⟩
end ContextualBoundary
end SquareKit.DependentPairJudgments

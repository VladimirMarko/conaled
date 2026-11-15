import CachedEmittedAcceptance
import ConLeche.Verify.Cached.MainC
import EmittedClosed
import ConLeche.Model.Fold
/-! Experimental #417 model and general comparisons from exact cached-family acceptance.
SetTheory remains an explicit assumption.
See [scope report](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedAcceptedEmission
open SquareKit.Internal ConLeche ConLeche.SetTheory ConLeche.SetModel
open EmissionEncoding EmissionSemantics
universe w
variable {V : Type w} [SetTheory V]

theorem model_exists : Nonempty (ConLeche.Model V EmittedEnvironment.environment) := by
  obtain ⟨m⟩ := ConLeche.Cached.checkDecls_sound (V := V) rfl CachedEmittedAcceptance.accepted
  exact ⟨ConLeche.Model.Model.ofEnvModelM m⟩

noncomputable def model : ConLeche.Model V EmittedEnvironment.environment := Classical.choice model_exists

theorem source_comparison {S : Setting V} {L : Laws S u φ} {ρ : Nat → V}
    {em : GraphEmissionPure.Model} {a : GraphEmissionPure.Assignment Γ}
    {η : SquareKit.Internal.Env (interpretation S L) Γ}
    (hu : U.encode em.level = some u)
    (hm : Compatible (m := model (V := V)) (φ := φ) S ρ em)
    (ha : AssignmentCompatible (m := model (V := V)) S L ρ a η)
    (p : GraphTarget.SourceFormula Γ) (r : ConLeche.Expr) (P : V)
    (he : encode (GraphEmissionPure.formula em a (GraphTarget.translateFormula p)) = some r)
    (hd : Denotes (model (V := V)).cval EmittedEnvironment.environment φ ρ r P) :
    (pt : V) ∈ˢ P ↔ p.eval (interpretation S L) η :=
  EmissionSemantics.source_comparison (EmittedComparison.primitives (model (V := V)) u φ) hu hm ha p r P he hd

theorem emission_comparison {S : Setting V} {L : Laws S u φ} {ρ : Nat → V}
    (d : GraphTarget.Declaration) (em : GraphEmissionPure.Model)
    (a : GraphEmissionPure.Assignment d.context)
    (η : SquareKit.Internal.Env (interpretation S L) d.context)
    (hu : U.encode em.level = some u)
    (hm : Compatible (m := model (V := V)) (φ := φ) S ρ em)
    (ha : AssignmentCompatible (m := model (V := V)) S L ρ a η)
    (ty body rp rq : ConLeche.Expr) (P Q : V)
    (ht : encode (GraphEmissionPure.emitCore d).1 = some ty)
    (hb : encode (GraphEmissionPure.emitCore d).2 = some body)
    (hep : encode (GraphEmissionPure.formula em a d.premise) = some rp)
    (heq : encode (GraphEmissionPure.formula em a d.conclusion) = some rq)
    (hp : Denotes (model (V := V)).cval EmittedEnvironment.environment φ ρ rp P) (hq : Denotes (model (V := V)).cval EmittedEnvironment.environment φ ρ rq Q) :
    (GraphEmissionPure.ArtifactTyped (GraphEmissionPure.emit d) ∧
      GraphEmissionPure.ArtifactDenotes.{w} (GraphEmissionPure.emit d) (GraphTarget.Declaration.denote.{w} d)) ∧
    ((decode ty).map CoreSyntax.Expr.toLean = some (GraphEmissionPure.emit d).1 ∧
      (decode body).map CoreSyntax.Expr.toLean = some (GraphEmissionPure.emit d).2) ∧
    ((pt : V) ∈ˢ P → (pt : V) ∈ˢ Q) :=
  EmissionSemantics.emission_comparison d em a η (EmittedComparison.primitives (model (V := V)) u φ)
    hu hm ha ty body rp rq P Q ht hb hep heq hp hq

theorem closedTruth (φ : LevelParam → Nat)
    (A B C F G : V)
    (hA : A ∈ˢ univ (Level.eval φ EmittedComparison.carrierLevel))
    (hB : B ∈ˢ univ (Level.eval φ EmittedComparison.carrierLevel))
    (hC : C ∈ˢ univ (Level.eval φ EmittedComparison.carrierLevel))
    (hF : F ∈ˢ piV A (fun _ => B)) (hG : G ∈ˢ piV B (fun _ => C))
    (x : GraphAdapter.Member A) (z : GraphAdapter.Member C) (P Q : V)
    (hp : Denotes (model (V := V)).cval EmittedEnvironment.environment φ
      (EmittedComparison.assignment x.val z.val A B C F G) EmittedComparison.premise P)
    (hq : Denotes (model (V := V)).cval EmittedEnvironment.environment φ
      (EmittedComparison.assignment x.val z.val A B C F G) EmittedComparison.conclusion Q) :
    (pt : V) ∈ˢ P ↔ (pt : V) ∈ˢ Q :=
  EmittedClosed.closedTruth (model (V := V)) φ A B C F G hA hB hC hF hG x z P Q hp hq

end CachedAcceptedEmission
#audit_graph_module

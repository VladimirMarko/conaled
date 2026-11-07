import SquareKit.DependentPairPrimitiveMap
import SquareKit.DependentCertificateEmbedding
import SquareKit.DependentEliminationPresentationSubstitution
import SquareKit.DependentPairStructuralMaps

/-! Direct local certificates for pair formation and construction congruence. -/
namespace SquareKit.DependentPairJudgments
open DependentTheoryMaps DependentPairPresentations Judgment

abbrev GCongruencePremises (r : ProjectionCongruence) :=
  fun i : Fin (ProjectionCongruence.schema r).premises.length => map G ((ProjectionCongruence.schema r).premises.get i)

abbrev GCongruenceCertificate (r : ProjectionCongruence) :=
  MetavariableCertificate eliminationPresentation (GCongruencePremises r)
    (map G (ProjectionCongruence.schema r).conclusion)

private def direct (r : ProjectionCongruence) (s : EliminationCongruence)
    (law : s.schema = r.schema.map G) : GCongruenceCertificate r := by
  let plain : TheoryMap (rulesOf (fun _ : ULift.{1} Unit => r.schema))
      (rulesOf EliminationCongruence.schema) (map G) :=
    replayMap (fun _ : ULift.{1} Unit => r.schema) EliminationCongruence.schema G (fun _ => s) (fun _ => law)
  exact MetavariableCertificate.mapRules TypedSubstitution.fullEliminationCongruence
    ((MetavariableTheoryMap.ofTheoryMap plain).certificate ⟨()⟩)

def GFormationCongruence (Γ : Context projectionSignature V) (A A' : PExpr V)
    (B B' : PExpr (Fin 1 ⊕ V)) : GCongruenceCertificate (.formation Γ A A' B B') :=
  direct _ (.formation (Γ.map G) (G.act A) (G.act A') (G.act B) (G.act B')) (by
    simp [EliminationCongruence.schema, ProjectionCongruence.schema,
      EliminationCongruence.families, ProjectionCongruence.families,
      Schema.map, Context.map, map, mapForm, ctx, type, typeEq])

def GPairCongruence (Γ : Context projectionSignature V) (A A' : PExpr V)
    (B B' : PExpr (Fin 1 ⊕ V)) (a a' b b' : PExpr V) :
    GCongruenceCertificate (.pair Γ A A' B B' a a' b b') :=
  direct _ (.pack (Γ.map G) (G.act A) (G.act A') (G.act B) (G.act B')
    (G.act a) (G.act a') (G.act b) (G.act b')) (by
    simp [EliminationCongruence.schema, ProjectionCongruence.schema,
      EliminationCongruence.families, ProjectionCongruence.families,
      EliminationCongruence.endpoints, ProjectionCongruence.endpoints,
      Schema.map, Context.map, map, mapForm, ctx, type, typeEq, term, termEq])

end SquareKit.DependentPairJudgments

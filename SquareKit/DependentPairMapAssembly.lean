import SquareKit.DependentPairDirectCongruenceMaps
import SquareKit.DependentDeclarationMaps
import SquareKit.DependentProjectionInclusion

/-! Assembly of independent local certificates into the complete theory map. -/
namespace SquareKit.DependentPairJudgments
open DependentTheoryMaps DependentPairPresentations Judgment TypedSubstitution

/-- Inclusion of the independently specified eliminator fragment in its
structural, declaration and constructor-congruence extension. -/
def eliminationInclusion : TheoryMap Eη eliminationPresentation id where
  certificate r := match r with
    | .inl r => fullEliminationStructural.certificate r
    | .inr r => fullEliminationPrimitive.certificate r

/-- A presentation map assembles one certificate per constructor rule; the
subsequent proof translator is the generic derivation induction. -/
def fullGWithCongruence (congruence : ∀ r, GCongruenceCertificate r) :
    MetavariableTheoryMap (projectionPresentation true) eliminationPresentation (map projectionToElimination) where
  certificate r := match r with
    | .inl r => MetavariableCertificate.mapRules fullEliminationStructural
        ((MetavariableTheoryMap.ofTheoryMap (structuralMap projectionToElimination)).certificate r)
    | .inr (.inl r) => MetavariableCertificate.mapRules eliminationInclusion (gPrimitiveCertificate r)
    | .inr (.inr (.inl r)) => congruence r
    | .inr (.inr (.inr (.inl r))) => MetavariableCertificate.mapRules fullEliminationDeclaration
        ((MetavariableTheoryMap.ofTheoryMap DependentPairDeclarations.gDeclarations).certificate r)
    | .inr (.inr (.inr (.inr r))) => MetavariableCertificate.mapRules fullEliminationDeclarationCongruence
        ((MetavariableTheoryMap.ofTheoryMap DependentPairDeclarations.gDeclarationCongruence).certificate r)

/-- Composition retains the ordinary proof tree obtained by first transporting
through beta-to-eta inclusion and then replaying the projection templates. -/
def pairPipelineWithCongruence (congruence : ∀ r, GCongruenceCertificate r) :
    CertificatePipeline (projectionPresentation false) eliminationPresentation (map projectionToElimination ∘ id) :=
  (CertificatePipeline.step (MetavariableTheoryMap.ofTheoryMap projectionInclusion)
    (fullProjectionLocal true _)).comp
    (.step (fullGWithCongruence congruence) (fullEliminationLocal _))

end SquareKit.DependentPairJudgments

import SquareKit.DependentProjectionComposition
import SquareKit.DependentPairMapAssembly
import SquareKit.DependentPairFirstCongruenceMap
import SquareKit.DependentPairSecondCongruenceMap

/-! The complete forward translation between independent dependent pair calculi. -/
namespace SquareKit.DependentPairJudgments
open DependentTheoryMaps DependentPairPresentations Judgment TypedSubstitution

/-- Every constructor congruence is certified; the projection cases are
consequences of target split congruence with dependent motives. -/
def GCongruence : ∀ r, GCongruenceCertificate r
  | .formation Γ A A' B B' => GFormationCongruence Γ A A' B B'
  | .pair Γ A A' B B' a a' b b' => GPairCongruence Γ A A' B B' a a' b b'
  | .first Γ A A' B B' p p' => GFirstCongruence Γ A A' B B' p p'
  | .second Γ A A' B B' p p' => GSecondCongruence Γ A A' B B' p p'

/-- The full map has no remaining certificate parameters. -/
def fullG : MetavariableTheoryMap (projectionPresentation true) eliminationPresentation (map G) :=
  fullGWithCongruence GCongruence

def pairPipeline : CertificatePipeline (projectionPresentation false) eliminationPresentation (map G ∘ id) :=
  pairPipelineWithCongruence GCongruence

/-- Forward compilation of closed derivations checks typed metavariable uses
through the target's proved substitution theorem. -/
def compile {j : Judgment projectionSignature}
    (d : Derivation (projectionPresentation false) (fun _ => Empty) j) :
    Derivation eliminationPresentation (fun _ => Empty) (map G j) :=
  fullG.transportClosed (fullEliminationLocal _)
    (projectionInclusion.transport (fun _ h => Empty.elim h) d)

theorem pipeline_compiles {j : Judgment projectionSignature}
    (d : Derivation (projectionPresentation false) (fun _ => Empty) j) :
    pairPipeline.run d = compile d := by
  unfold pairPipeline pairPipelineWithCongruence
  simp only [CertificatePipeline.run, MetavariableTheoryMap.transportClosed]
  rw [MetavariableTheoryMap.transport_ofTheoryMap]
  rfl

/-- A single local certificate per beta rule, obtained by composing F with G. -/
def fullFG : MetavariableTheoryMap (projectionPresentation false) eliminationPresentation (map G ∘ id) :=
  fullG.precompReplay projectionReplay

theorem compressed_compiles {j : Judgment projectionSignature}
    (d : Derivation (projectionPresentation false) (fun _ => Empty) j) :
    fullFG.transportClosed (fullEliminationLocal _) d = compile d := by
  unfold fullFG MetavariableTheoryMap.transportClosed compile
  have empty_comp : (fun (_ : Judgment projectionSignature) (h : Empty) => (Empty.elim (Empty.elim h) : Empty)) =
      (fun (_ : Judgment projectionSignature) (h : Empty) => (Empty.elim h : Empty)) := by
    funext j h
    exact Empty.elim h
  simpa only [empty_comp, MetavariableTheoryMap.transportClosed] using
    projectionReplay_composition fullG (fullEliminationLocal _) (fun _ h => Empty.elim h)
      (fun _ h => Empty.elim h) (fun _ h => Empty.elim h) d

end SquareKit.DependentPairJudgments

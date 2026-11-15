import SquareKit.SmoothQuotientGeneratedBaseChangeSource
import Examples.SmoothSourceTransport
import Examples.SmoothTorsors
import Examples.SignatureInterpretationMaps

/-! The selected smooth square retains the source wrapper in the classical
and ineffective C4 models, and composes along a nonidentity parameter map. -/
noncomputable section
namespace Examples.SmoothSelectedComparison
open CategoryTheory SquareKit SquareKit.Internal.PathTransport
open GroupoidModel Comparison SheafActionQuotient SmoothOpenSite
open SmoothQuarterTurnQuotient SmoothQuarterTurnArcs
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section SourceConsumers
variable (A : SplitSheaf.Ty realBase)
variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]
variable {Y : Sheaf topology Type} (f : Y ⟶ realBase)

/-- This is the source interpretation used by origin_classical_composition. -/
example : SmoothQuotientGeneratedBaseChange.SectionCoherence diskRepresentation.action A f
    Typed.Authoring.UniversalTransfer.context Typed.Authoring.UniversalTransfer.type
    Typed.Authoring.UniversalTransfer.proof :=
  SmoothQuotientGeneratedBaseChange.universalTransfer_square diskRepresentation.action A f

/-- This is also the source interpretation used by ineffective_composition;
identity action on fibers does not remove the quotient arrows. -/
example : SmoothQuotientGeneratedBaseChange.SectionCoherence ineffectiveRepresentation.action A f
    Typed.Authoring.UniversalTransfer.context Typed.Authoring.UniversalTransfer.type
    Typed.Authoring.UniversalTransfer.proof :=
  SmoothQuotientGeneratedBaseChange.universalTransfer_square ineffectiveRepresentation.action A f

/-- The same selected square covers the independent dependent-J caller. -/
example : SmoothQuotientGeneratedBaseChange.SectionCoherence diskRepresentation.action A f
    SignatureInterpretationMaps.DependentTail.withFiber
    SignatureInterpretationMaps.DependentTail.command.motive.typing
    SignatureInterpretationMaps.DependentTail.generic :=
  SmoothQuotientGeneratedBaseChange.sectionCoherence diskRepresentation.action A f _ _ _

end SourceConsumers

open SmoothPresentationSite SmoothGeometricKL
abbrev parameter := representable (J := SmoothOpenSite.topology) (dual (free 0))
def kill : parameter ⟶ parameter := representableMap SmoothTorsors.killEps

/-- Two successive restrictions use the actual composite parameter map and
all generated arrows, at the source proof's context. -/
example := SmoothQuotientComparison.generatedContextMap_comp diskRepresentation.action kill kill
  Typed.Authoring.UniversalTransfer.context

example : SmoothTorsors.killEps ≠ 𝟙 (dual (free 0)) := SmoothTorsors.killEps_nonidentity

example := SmoothQuotientComparison.generatedContextMap_id (X := parameter)
  ineffectiveRepresentation.action Typed.Authoring.UniversalTransfer.context

example (m : realBase ⟶ scalar) :
    SmoothQuotientTransport.ineffectiveActionArrow Orbifolds.QuarterTurn.quarterTurn m ≠
      SmoothQuotientTransport.ineffectiveActionArrow 1 m :=
  SmoothQuotientTransport.ineffective_forward_distinct m

end Examples.SmoothSelectedComparison

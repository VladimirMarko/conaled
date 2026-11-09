import CachedRejectionsComposition
import CachedPending7
/-! Experimental exported cached rejection controls for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedRejections
open ConLeche ConLeche.Cached CachedRejectionsFamilies
set_option acceptance.measureTreeSize false
measured_theorem body_rejected : checkDecls .verified [] bodyDeclarations.toArray =
    .error ((.invalid s!"loose bound variable in value of {EmittedForwardAcceptance.cv.name}"),12) :=
  CachedRejectionsComposition.body_rejected CachedPending7.accepted
measured_theorem type_rejected : checkDecls .verified [] typeDeclarations.toArray =
    .error ((.invalid s!"type of theorem {CachedRejectionsType.cv.name} is not a proposition"),12) :=
  CachedRejectionsComposition.type_rejected CachedPending7.accepted
measured_theorem missing_rejected : checkDecls .verified [] missingDeclarations.toArray =
    .error (CachedRejectionsMissing.error,11) :=
  CachedRejectionsComposition.missing_rejected CachedPending7.accepted
end CachedRejections
#audit_graph_module

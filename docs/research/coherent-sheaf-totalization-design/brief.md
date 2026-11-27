# Coherent-sheaf totalization assessment

Date: 2026-11-27. Project f96e378241012feae903d6e06211c26bfe0f94b3;
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; Lean v4.35.0.
Clean starting checkout. Parent issue #708, Research remaining categorical
presentations and select additional interfaces.

## Decision and authorization

Assess whether extending the existing coherent local sheaf classification to
total categories over contexts adds worthwhile mathematics and author capability,
and identify the smallest justified interface and its proof obligations.
The user has now authorized this assessment after previously deferring #708.
No existing or blocked application is required. Evaluate language direction,
mathematical capability and shared proofs as well as practical caller costs.
Do not assume either adoption or rejection. This pass may recommend and specify
implementation, but does not implement the adapter or complete broader #708.

## Candidate and evidence

Candidate: retain independently defined LocalCode fibres and current reindexing;
derive their pseudofunctor coherence, coherent decoder/inverse and recovery;
use Mathlib CoGrothendieck and local CoGrothendieckMap for an equivalence of
total categories over the same base, preserving cartesian arrows and all maps.
Alternatives include direct sheaf totals only, a smaller equivalence-transport
construction, and a direct display/fibration interface. These are candidates,
not prescribed requirements or an exhaustive classification.

Inspect these pinned sources and their dependencies:
- SquareKit/Internal/CoherentSheafOver.lean, especially Local, LocalCode,
  sheafOverClassification, codeDisplayClassification and Substitution.
- Examples/CoherentSheafOver.lean: pairProjection, diagonal, pairDisplay,
  collapse_not_iso, support_map_not_iso, substitution examples.
- SquareKit/Internal/CoherentFamilyFibration.lean;
  SquareKit/Internal/RepresentableCoherentRecovery.lean;
  SquareKit/CoGrothendieckMap.lean.
- Mathlib/CategoryTheory/Sites/Over.lean and Sites/PseudofunctorSheafOver.lean;
  Mathlib/CategoryTheory/Bicategory/Grothendieck.lean and FiberedCategory/Grothendieck.lean.
- docs/research/coherent-family-fibration.md and
  docs/research/reconstructible-presentations-search.md (final coherent-sheaf discussion).
- docs/research/action-stackification-morita.md and actual source if relevant.
- docs/language-direction.md, especially complementary presentations and
  elegance/capability; docs/agents/architectural-quality.md.

Existing evidence: fibrewise equivalences, reindexId/reindexComp and
decodeReindex_id/comp exist. Do not describe those as unproved. The missing
complete packaging and which remaining laws are derivable are to be assessed.
Do not infer missing mathematics solely from missing wrapper declarations.
Current sheaf-side target has pseudofunctorOver. The #705 total bridge uses
different fibres and strict precomposition; it is not a drop-in replacement.
Preserve arbitrary maps, locality, full faithfulness, cover density, required
limits, independent site/value universes. Subcanonicity belongs to the display
comparison, not general substitution. Totalization is not stackification.

Proposed discriminating case: p: Bool×Bool→Bool (first projection),
d: Bool→Bool×Bool (diagonal). p∘d=id; d∘p(true,false)=(true,true).
Combine actual base changes with the noninvertible display collapse.
Assess what this can and cannot establish, and whether an additional abstract
compositional example is needed to demonstrate shared capability.

#723 owns assessment/extraction of reusable coherence across StackificationUniversal,
StackDescentTransformation and indexed-family clients. #708 owns adapter choice
and its exact contract. Coordinate boundaries without making a universal framework
or completion of #723 a prerequisite by assumption. #678/#679 are completed
selected action-stackification/atlas results, not this adapter.

## Independent lenses

1. Contract and foundations: derive precise remaining coherence and recovery
   obligations; inspect hypotheses/universes and potential false guarantees.
2. Implementation and use: research primary source code for a concrete useful
   author construction, caller obligations, reusable proof and maintenance costs;
   compare current and proposed routes without assuming a blocked client.
3. Alternatives and generality: compare mathematical alternatives including
   approaches beyond current local precedent; consult external primary sources
   and relevant nLab orientation, recording access dates and source limits.

Contract and Use receive fresh agents with no previous task involvement. The
host rejected creation of a third fresh agent with a thread-limit error, so
Alternatives uses the previous cleanup Standards reviewer, with that exposure
disclosed. Each receives this shared brief and its own instructions. Do not read
the other reports or coordinate
conclusions before all initial reports are saved. Distinct lenses are not model
diversity. Report recommendation, strongest evidence for retaining proposal,
concrete concerns with sources, smallest useful alternative, discriminating test,
missing evidence and validation limits. Separate inspected code, paper derivation
and executed checks. No promised productivity measurements or checked totalization.

Work read-only against project/dependencies. Scratch experiments may be isolated
under /tmp, without shared Lake writes or new admissions. No source edits, tracker
writes, issue creation, other-session messages, or recursive design challenge.
Save reports to assigned /tmp paths; root will preserve initial reports and
synthesize after all complete, then independently review/publish documentation.

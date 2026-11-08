# Architectural assessment after the external orbifold report

The [final disposition](disposition.md) supersedes this report’s pending #362
scheduling and assigns the bounded follow-ups. This report retains the evidence
and recommendations at its publication checkpoint; the original independent
assessments remain unchanged.

The incoming evidence changes the recommended next experiment. Compare a real
source theorem's model requirements and geometric meaning before extending the
current certificate interfaces. Retain conaled's constructed geometry and
specializations as regression requirements. Keep alternative interpretation and
model-construction foundations eligible to replace parts of the current core.
The evidence does not yet select a replacement or establish a productivity win.

This assessment incorporates the owner's two reports and checkpoint 080,
preserved in the [durable evidence directory](../../history/orbifold/agda-checkpoints/checkpoint-080/README.md),
into [#362](https://github.com/VladimirMarko/conaled/issues/362). The former
missing-report condition is satisfied. The previous [interim synthesis](synthesis.md)
remains a historical account of the independent comparison before this evidence.
No Lean implementation, migration, automatic Agda importer, or mixed-prover trust
chain was introduced. #358–#361 remain held while their comparison scopes are
revised; receipt of the report does not by itself validate their old priorities.

## Evidence and limits

Three separate assessments covered [consumer requirements and conaled source](orbifold-consumer-assessment.md),
[checkpoint integrity and theorem scope](orbifold-evidence-assessment.md), and
[primary-source alternatives](orbifold-alternatives-assessment.md). Each author
worked without reading the other new assessments. The coordinator read all three
before synthesis and supplied the evidence auditor with the coordinator's native
replay results. Agreement among agents is not independent model diversity or a
mathematical proof.

The source audit's 42 conaled files match the current checkout. The checkpoint's
2,294 manifest payloads and the 539-module Cubical and 54-module ordinary source
maps match their supplied receipts. The coordinator additionally performed a
fresh pinned Agda 2.8.0.2 check of all 54 ordinary modules, accepted with stable
sources and complete literal checking coverage. The original archive is
unchanged. The separate Cubical closure was not freshly replayed; its retained
receipt and source identity remain its acceptance evidence. Details, exact
hashes and new receipts are in the evidence directory.

This is feedback from an actual prospective consumer with a substantial existing
proof development. It is stronger demand evidence than an example selected to
exercise our APIs. It is still source review, not a controlled author trial:
the consumer has not completed its end-to-end theorem using conaled, nor measured
its authoring productivity against the other libraries. Its goal remains an
Agda-only proof, using conaled as a reference for mathematics to reconstruct.
That is a legitimate reuse case and does not prescribe conaled's host language.

## What the consumer found useful

The positive evidence concerns constructed mathematics: split dependent sheaves,
dependent products with proved sheafhood, actual smooth algebras and the smooth
site, first-order KL for arbitrary sheaf parameters, manifold full faithfulness,
and effective torsor/action-quotient descent. The quarter-turn example and
nontrivial clutching torsor provide stronger tests than a newly invented coarse
quotient example. The consumer identifies proof strategies it intends to reuse.
These findings support preserving those results through architectural change.

The missing ordinary-open comparison is precise. `ordinaryLocallyConstant`
turns a sheaf section into a locally constant group label. Its inverse on
ordinary opens and restriction compatibility remain to be constructed in the
inspected module. `chartArrowEquiv` already has both inverses, but its labels are
sheaf-valued. Completing the first comparison and composing the actual maps
would connect that existing equivalence to ordinary geometric arrows. Merely
adding another abstract equivalence field would not do this work.

## The principal architectural pressure is joint interpretation

A theorem can be proved under explicit assumptions while its intended model
remains unconstructed or incompatible with those assumptions. The checkpoint
makes this concrete in three distinct developments:

| Development | Established or inspected evidence | Additional obligation |
|---|---|---|
| Original synthetic main theorem | Parameterized proof of orbifold structure on an actual groupoid completion, with supplied Cubical acceptance evidence | Validate its joint smooth, crisp, identity, RealFlat, compactness and properness assumptions in the intended model. |
| Reduced ordinary atlas theorem | Freshly checked proof from bounded truncation, weak function extensionality, effective atlas data, actual mapping comparisons and vertex liftings | Construct the intended geometric test family and all these operations together; interpret the admitted source proof with its universe and substitution laws. |
| Presheaf obstruction | Freshly checked construction of restriction/right extension, adjunctions and a conditional contradiction for specified maps | Supply the counterobject and smooth/sheaf instance, and justify the crisp codes and exact source interpretation before applying it to the original theory. |

The archive's external sheaf and geometric arguments are further mathematical
evidence, not native constructions of the full model. The broader paper ledger
has checked, relative and corrected/refuted entries; completion of a conditional
main theorem must not be expanded into unconditional validation of every paper
claim. The evidence assessment records these distinctions without dismissing
parameterized proofs as empty interfaces.

This reinforces the owner's MakeLawful analogy. A proposed setting must validate
the chosen specification before a theorem can be transported into it. A failed
compatibility proof may reveal a mathematical obstruction, not simply missing
implementation effort. In particular, the RealFlat obstruction concerns a
specified constant-map/counit interpretation with explicit hypotheses. It is
neither a universal no-model theorem nor permission to silently change the
meaning of Flat. A reduced theory can be useful, but its changed specification
must remain visible.

A single smooth setting with the required higher identities and bounded type
operations is still a construction obligation. Putting the existing ordinary
sheaf model beside the separate higher cocycle model does not solve it. Likewise,
local-universe presentations for coherence and an object-language universe
classifying admissible families are different constructions. An interface whose
fields assume all desired closure laws only moves the model-builder's workload.

## Equality, selected data and constructive reuse

The consumer's actual proof uses the specified `mapping-comparison`, including
its cocone gluing path. An arbitrary equivalence between the same endpoint types
cannot replace it. The geometric comparison must preserve actual arrows,
composition and restriction; inverse labels relative to conventional forward
action arrows must be accounted for. Ineffective stabilizers are a useful
negative control because different arrows can have the same action.

The existing semantic-boundary direction remains relevant. What counts as equal
belongs to the intended setting and observation contract. The implementation
must prove that its operations respect that meaning, and the interpretation
must retain every distinction required by the specification. Neither
proof-irrelevant Lean equality nor equality of observed actions can stand in for
all the consumer's identity data. This is evidence for witness-sensitive
comparisons, not for one universal equality representation.

Constructive reuse adds a different distinction. Unique gluing can sometimes
eliminate truncated existence into a proved proposition of complete solutions;
arbitrary representative selection needs another justification. Negative
nonzero predicates, positive apartness, analytic existence and proof coherence
raise separate questions. A useful explicit-data core should expose the actual
operations and derive their laws, with classical wrappers recovering existing
results. It need not make every conaled theorem constructive. Per-declaration
logical dependencies and checked alternatives are needed before claiming a
constructive reconstruction; `classical` and `noncomputable` keyword counts
cannot establish one. No fresh transitive Lean axiom extraction was performed
in this assessment.

## Revised comparison programme

The next comparison should have two connected but separately accepted parts.
Their results are not yet implemented.

1. **Exact source and model comparison.** Freeze the mapping-square/gap-cancellation
   subargument of `DerivedAtlasOrbifold`, including its actual maps, quantified
   targets, identity data, universe levels and behavior under two substitutions.
   Compare the incumbent interpretation with natural-model/contextual-category
   formulations, permitting weak structure plus coherence where its hypotheses
   can be constructed. Count model setup and recurring proof obligations. Do not
   weaken the signature on only one route. The reduced full theorem later adds
   its bounded truncation and actual geometric instance; proving the small
   subargument does not certify that larger theorem.
2. **Ordinary geometric control.** Construct the ordinary-open section/locally
   constant-label inverse, then the actual C4 chart-arrow comparison with
   composition and restriction. Use disconnected label regions, four origin
   automorphisms, the regular-point result and ineffective arrows. Extend the
   test to cover refinement and the nontrivial clutching torsor. Properness and
   étaleness of the actual finite-action groupoid are separately stated geometric
   obligations. Finite stabilizers alone cannot replace properness.

The first tests reusable proof interpretation and model admission; the second
keeps a concrete geometric meaning in view. Their eventual connection is itself
a theorem to prove. An empty test family, a constant-only label example, a
coarse orbit set, or a globally trivialized torsor cannot satisfy the intended
consumer contract. The algebraic sums/tensors, distributive-law and relational
hiding alternatives from the first assessment remain independent comparison
candidates. Orbifold feedback should correct earlier sampling bias without
turning this one consumer into the specification of the whole library.

The primary-source assessment finds relevant alternatives beyond the owner's
original suggestions: natural-model soundness, structured syntax/initiality,
constructed sheaf CwFs, and cubical classifier and higher-sheaf constructions.
Their hypotheses and implementation limits are recorded there. For example,
[constructive higher sheaf models](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.LICS.2026.31)
provide model-construction mathematics worth investigating; they do not supply
our exact smooth instance or settle the original Myers axioms. No alternative
has yet won the matched comparison.

## Scheduling and ownership

| Existing issue | Consequence of this assessment |
|---|---|
| #362 | Incoming evidence is assessed; remaining work is to freeze and assign the revised comparisons and reconcile the downstream scopes. It is no longer waiting for the report. |
| #359 | First semantic priority: retain the higher selected-data requirement, but investigate a joint model and alternative interpretation foundations before extending current certificate machinery. |
| #358 | Design the source/model scaling test alongside #359; defer fresh productivity trials until the semantic contracts and competing interfaces are fixed. Include model construction and maintenance costs. |
| #361 | Investigate selected solutions, unique gluing and mere existence as different contracts. Do not silently replace this issue's operational partial-computation requirement with a sheaf theorem. |
| #360 | Keep its independent operational resource question. Crisp modalities in geometry are not evidence for a resource-mode implementation or a reason it must organize the semantic core. |
| #100/#36/#289/#290 | Existing owners for joint higher/smooth interpretation, model construction, coherence and source transport. The concrete comparison designs above should refine these agendas rather than create duplicate broad programmes. |
| #310 | Use checkpoint 080 as newer artifact evidence in the still-distinct connection/motion comparison. This assessment does not complete that common-problem research. |

The ordinary arrow comparison needs a bounded implementation scope under the
existing geometry/model owners. The explicit-data/dependency investigation needs
a declaration-level scope before claiming constructive parity. These are
recommended follow-ups, not completed ports. The owner requested examination of
the evidence; this publication does not start those implementations. #107 stays
paused, #108 unselected and #260 inactive. Preserve old usable specializations
and measure setup and change propagation as well as proof size when the next
experiment runs.

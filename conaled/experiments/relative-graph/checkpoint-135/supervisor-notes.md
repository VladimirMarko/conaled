# Supervisor notes for #135

Fixed base ad8e7a56de5027eed620486fe63f154eecdd3cd3. #132/#134 accepted and closed. #133 subsequently intent-PASS, combined integration check/closure pending. Continue producer route.

Initial inspection confirms native producer uses explicit helpers with z,x telescope; relative family uses direct Eq.rec and x,z. This is an actual body/binder/environment connection obligation, not satisfied by parallel native/relative truths.

Early acceptance probes (worker reported): direct rfl fails ~0.7s; unrestricted reduce hits maxRecDepth100000 ~4s even Eq-only prefix. Not infeasibility evidence yet: Array.foldlM may prevent useful reduction. Staged list-fold rewriting in progress. Supervisor suggested separating check-result success/discriminant from equality to independently reconstructed output environment, preserving exact final metadata identity via separate proof if needed. Existing-family acceptance remains distinct from actual emitted-family acceptance.

## Coordinator intent steering: reference-checker route

Coordinator permits the finite-fuel verified reference checker under the written fallback. Acceptance still requires a concrete kernel-checked success equation for the exact actual-emitted/encoded family and exact environment, audited checkDeclsPure_sound_of plus ofEnvModelM application with explicit SetTheory, and general formula/binder/source-denotation correspondence. Hypothesized success is insufficient. Cached timeout evidence is a measured limit, not impossibility. Exported Cached.checkDecls acceptance stays explicitly open and must be a separate follow-up if this route succeeds. Never infer cached success from one-way soundness or model existence. Inventory reference-model-route.md must be included in final evidence.

## Finite-fuel measurement checkpoint

Implementer reports execution-only checkDeclsPure success for the existing handwritten family at fuel 32/64 and failure at 8/16. Kernel cbv at fuel 32/256 reaches maxRecDepth 100000 with cbv.maxSteps 10000000; default cbv reaches its step limit. These are measured limits, not impossibility, and are neither a kernel success proof nor acceptance of the actual emitted family. Requested operation/phase certificates rather than further undirected whole-family limit sweeps. Actual syntax formula induction and its concrete semantic application continue.

## Semantic join and phase-proof milestone

Implementer reports emission_comparison compiled/audited (63 roots), combining #132 emit_typed/emit_denotes with exact type/body decoding and relative comparison. Concrete open-formula comparison compiled/audited (30 roots), with the native z,x assignment explicit. Existing structural selector equations allow a kernel-checked And former checkConstantVal certificate (~0.7s), then complete And checkBlockInds Boolean success; exact result extraction and constructor phase continue. Whole-family acceptance remains unproved; no review candidate yet.

## Positivity reduction checkpoint

Local CheckerReduction.depthGo_spec uses a valid-cache invariant and proves exact memoized/structural depth equality; audited49 roots, no checker/fuel change. Checked former/constructor/context/uniform certificates remain preserved. Positivity root remains open. Worker distinguishes opaque-probe timeouts that include large goal printing from reduction evidence; later conv/erw matching/composition attempts took20–30s and ~2.3GB before the next tactic. Next bounded attempt uses named nestCtors transition equations and crest/type/field certificates. These measurements do not establish impossibility.

## Actual stored-record semantic observation

Implementer reports AndPositivityStages compiled/audited103 roots: two ordinary-field lemmas and exact two-field nestFields result via named transitions. EmittedClosed.closedTruth compiled/audited4 roots: Model.mem for both actual emitted theorem records, native z,x telescope specialization through shared ClosedGraph.specialize, shifted encoded conclusion, and general formula denotation yielding pt-membership iff. This remains conditional on a model; the concrete acceptance equation and audited model construction remain mandatory and open. Crest inference/construction certificates are checked separately; root composition continues.

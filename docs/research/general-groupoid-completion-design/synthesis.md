# Construction decision

All three independent assessments favor principal groupoid bundles, with existing split-family effective descent as the underlying construction. Retain the represented operations and laws as input; derive section operations, unit full faithfulness, local generation and effective descent. Use the existing mapping-category universal theorem only after those proofs.

The alternatives report correctly observes that cover-data completion need not quotient its objects and can fit the same universes. Its principal advantage is direct input functoriality. Bundle completion instead reuses actual sheaf-family gluing and absorbs refinement through sheaf maps. For atlas comparisons, use actual input maps followed by extension through the proved universal property; do not assume bundles push forward along arbitrary groupoid functors without an extension construction.

Use the right-action convention of the contract report: a point anchored at n acts by an arrow m→n to produce a point anchored at m. The regular bundle at n consists of arrows into n. This makes unit arrows postcomposition and agrees with the old quotient after its inverse-label comparison.

The selected encoding indexes the underlying split family over X×G.objects, rather than storing an anchor on a family over X. Fibers are points with a specified anchor; the action is contravariant in that anchor. The total sheaf still maps to X and must be locally surjective. This is the same bundle mathematics, but avoids equality transports for the output anchor and may reuse family descent over X×G.objects directly. The implementation checks the universes, regular unit, substitution and varying-anchor descent. No conclusion is accepted as a primitive field.

The third report inspected the newly written, uncommitted SheafGroupoidAtlas.lean while the assessment ran. Its statement that atlasOperations exists describes that working input, not the pinned baseline. The first two reports predate that input; none inspected another report. No new Lean experiment was run by assessors. Root has checked atlas operations/laws and section operations/restriction in focused Lean runs; these checks do not establish completion.

Acceptance remains all of issue #727. The implementation must include full effective descent, all arrows, original action-client recovery, actual atlas/common-refinement comparisons, and nontrivial/no-global-chart and already-stack controls. Design agreement does not discharge those proofs.

The [implementation report](../general-groupoid-completion.md) records the resulting construction and checked consumers. The independent assessments above are pre-implementation design evidence, not acceptance reviews.

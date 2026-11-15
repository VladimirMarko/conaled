# #434 baseline preparation

Prepared 2026-11-09. This is a read-only evidence inventory, **not the final assessment or an investment recommendation**. The independent #108 attempt and evaluation must be archived and supplied before that assessment. No current #108 worktree, proof, scratch, logs, or unarchived artifact was inspected, and its author was not contacted. An initial repository filename listing included tracked historical trial paths; their contents were not opened. Subsequent reads used exact public revision/path pairs.

## Sources and reproducibility

The public baseline is commit `2f89f8651843797822efbb7da038311ab3d9f04d`. Paths below are relative to that tree unless marked otherwise. Read with `git show REV:PATH`; no Lean build, archive replay, or source edit was performed for this preparation.

Live full #434, including its empty comments list, is saved externally as `434-live.json` beside this note. Public #107 body/comments are saved as `434-public107.json`. #434 is already assigned. Its acceptance criteria permit this preparation but require archived #108 evidence before final synthesis; negative or inconclusive results are admissible without extending the author's budget.

| Evidence | Path / immutable locator | What it establishes |
|---|---|---|
| #106 protocol, attempt and evaluator packet | `docs/research/agda-transfer-independent-baseline/` | Prospective budget, archived unsuccessful general proof attempt, checked partial results, separate evaluator comparison |
| #106 evaluation | `evaluation.md` within that directory; Git blob `99768263f966b44ad8f2b065d7f8d65f6852eb2c` | Scope and limitations of the independent baseline |
| #107 repair | `docs/research/guarded-dependent-authoring-repair.md`; blob `2f52f51c16b435f02219e385f7937e8f172ddf53` | Constructed source proofs, helper boundaries, selected-recipe preservation, known regressions |
| Earlier repair diagnosis | `docs/research/dependent-congruence-resumption.md` | Why raw reindexing agreement did not solve freshly rebuilt model-indexed annotations; superseded intermediate state |
| Accepted public freeze and inventory | https://github.com/VladimirMarko/conaled/issues/107#issuecomment-6751641963 | Exact accepted baseline, validation and distinction between new repair and other intervening capabilities |
| Bounded elaboration | `docs/research/bounded-elaboration.md`; blob `4adf26e0258aa3773095c839ee4c99ca016a9636` | A working but restricted typed frontend experiment |
| Agda internal inspection | `docs/research/agda-internal-retention.md`; blob `a3583dc22b0c6e5f57953c6b57f0b15670cb5b7c` | Retained declaration evidence and candidate export boundary, not an importer |
| Reference calculus | `docs/research/reference-dependent-calculus.md`; blob `86be5aacefd766974b979b5ce05a1a0b228232c3` | Independent calculus and forward translation into an explicit guarded extension, without reverse adequacy |
| #433 partial model checkpoint | `4944103646e5ee20ce197069c46d34ef7c0bc1af:docs/research/smooth-source-interpretation.md`; blob `41a013d118f6a741689a6ee4e2506d5c4fcb7bcd` | Technical reuse and remaining parameterized-model work; not acceptance or productivity evidence |

I independently recomputed the following SHA-256 values from the frozen Git blobs using Python `hashlib.sha256(subprocess.check_output(['git','show', REV + ':' + PATH]))` in `direnv exec . python`:

- `unassisted-baseline.tar.gz`: `27c81261b1ff1452acfdb2d999eaab6cd9c8293100fdbae057a9c9308d9f129f`
- `MANIFEST.sha256`: `502e3e3d1128ae34f38739861c92504871c236bfc0369aa035014fc13e8280ab`
- `protocol.md`: `3c88e9c3b9a5146a207fca18bb8e042337ba9d7238e5cb5674593f104414cd78`

The evaluator reports verifying 122 manifest entries and 123 archive files. This preparation verified the three enclosing blobs, not every archive member or the archived Lean replay.

## Four costs that must not be conflated

### Framework and repair

The #106 attempt used frozen API `8b1ed308f29cbe9d00e03c8b6b7780ffeb4b7c17` (production `8267b71c1c275c44b21bacfe878749d0b99dce1c` has the identical tree). Framework changes were prohibited during the attempt. Zero framework modifications during that attempt does not mean the framework had zero construction cost.

#107 subsequently moved presented elimination, dependent-tail squares, endpoint transport, context conversion and operation-substitution obligations into reusable helpers. It preserved the first-path concatenation recipe instead of substituting the previously available right-path recipe. Its source associativity theorem covers arbitrary endpoints and paths, and its transport-composition proof covers an arbitrary dependent family and element. Branches are constructed from source computation/congruence; target associativity is not supplied as the source proof.

The repair uses the already adopted guarded telescope theory and its finite-tail equations. It does not add a source rule, axiom or semantic model law. This is still substantial framework work: the obligations moved into helpers rather than disappearing. Fresh operations can require new substitution lemmas. The reports contain useful diagnoses and rejected cases but no standardized total time/token ledger for this investment. A future assessment must not infer net effort savings from short repaired clients alone.

The accepted freeze reports fresh candidate validation: 2255 compiled modules, exhaustive audit of 2256 modules, permitted axiom union `propext`, `Classical.choice`, `Quot.sound`, and exact fresh verification. The recorded 3073.45 seconds measures build/check execution, **not proof-author or repair effort**. Both review axes passed. The repair report's earlier pending-acceptance language describes its writing time; the public freeze establishes subsequent acceptance.

### Independent incremental author effort

#106 asked a fresh author for agda-unimath `foundation-core.identity-types.assoc` at upstream `75518656f287c203b41cb7f71df46e02b987a084`, preserving first-path elimination. Author provenance is recorded as session `01a15f76-ecf1-7da1-bc56-717ed6849978`, without inherited turns or an implementation role. Source proofs and public code were permitted. A scope reviewer saw a neighboring upstream proof, but the record says no coaching was relayed. Independence is supported by provenance records, not a filesystem theorem about all communication.

The 40 prospective substantive work cycles were exhausted without the general source associator. Initial investigations were not all separate terminal captures; the 37 categorized cycles comprise translation 7, investigation 7, debugging 11, helpers 9, application 1 and validation 2. The evaluator records 31 Lean checks, 17 failures and six source-read/search commands. These author-defined cycles are not standardized hours, tokens, or a productivity ratio.

The final partial includes the general goal and four-entry dependent motive, a reflexive-first-path specialization with remaining paths arbitrary, branch normalizations and raw rebuilding agreement. It does not contain the general branch/J proof or applications of that general source theorem. Fresh annotation comparisons still obstructed completion despite raw reindexing agreement. This is bounded negative authoring evidence, not a proof that the fragment cannot express the theorem.

The partial was checked and its 58 selected declarations audited for the permitted axioms. This is not an exhaustive production audit. It retained a local scratch heartbeat limit of 800000 after a default-limit diagnostic; production settings were unchanged.

The evaluator's direct Lean comparison occurred **after archival**, outside the author's budget. Generic category associativity and its set-valued action theorem checked on the first invocation; two concrete-example attempts failed before the third succeeded. Faithful and trivial C4 examples used the generic theorem, with labels 1,1,1 composing to 3. That is a direct ordinary proof and comparison, not a source interpretation or a controlled timed independent-author trial.

#108 evidence is pending. Nothing in this note assesses its performance or outcome.

### Model construction

The allowed #433 checkpoint applies the unchanged first source transport-composition proof to smooth quotient deformations. It builds a family over all quotient torsors, not only globally trivial presentations. Deformations are equivariant sheaf maps with a zero-boundary condition; inverse torsor arrows act on them. Boundary-fiber comparison, chart identification and parameter restriction/descent require separate constructions.

Its technical source path is `SmoothQuotientDeformations.source_composition` through `GroupoidTransport.transport_concat`, `UniversalTransfer.transport_concat_universes`, and the exact existing `Typed.Authoring.UniversalTransfer.proof`. A model's transport-composition law supplies model setup, not a substitute for consuming that source proof. The fragment does not need source universes, univalence, cohesion, crispness, or a newly successful associativity trial.

The report expressly leaves restriction/descent of generated source contexts and sections, identity/J preservation, and the complete parameter-indexed model unfinished. Models at individual parameters plus descent for a primitive family do not establish that combined result. The current generic structural-map interface is too broad for an immediate argument over every semantic context; source-context-indexed comparisons require construction. Endpoint naturality and discrete equality uniqueness alone do not supply it.

The report has focused checks and named-root axiom evidence, not a fresh complete acceptance receipt. Its deformation, boundary, chart and descent work is model cost. It is not evidence that a fresh author can economically write new source arguments. Conversely, unfinished model work is not evidence of a source-authoring failure.

### Demonstrated reuse

#107 demonstrates recovery of a known arbitrary associativity proof and another known transport-composition argument, together with ordinary groupoid specializations and preserved legacy clients. These are useful correctness and reuse regressions. They are not independent new-author evidence or a scaling result. Exact selected source certificates remain distinguished from reindexed old certificates unless an appropriate comparison is proved. Ordinary groupoid discreteness cannot justify arbitrary higher-witness uniqueness.

#433 supplies evidence of an existing source proof being consumed in a new geometric model, conditional on the report's explicitly unfinished combined model scope. Model setup and comparison proofs are part of the reuse cost. The #106 direct category theorem already generalizes across ordinary groupoids and set-valued families; merely adding more such examples does not establish that a source encoding is more economical.

## Public capabilities available after the old baseline

The entire accepted tree is the public corpus. The #107 inventory identifies entry points, not a restriction to just those files:

1. New #107 helpers: `SquareKit/Internal/DependentJudgments/{PresentedElimination,PresentedSquares,SourcePath,SourcePathArguments,TelescopeAuthoring,TelescopeTransport,LeftConcatenationSubstitution,LeftAssociativity,LeftTransportComposition}.lean` and the four `Examples.GuardedLeft*` clients.
2. Intervening guarded infrastructure: `ContextualRules.lean`, `TelescopePresentation.lean`, `Examples/GuardedContextualJudgments.lean`. These predate the resumed repair and must not be charged as newly invented #107 logical rules.
3. Independent reference calculus: `Examples/ReferenceDependentCalculus.lean`. Its forward translation does not establish reflection or equivalence with the original engine.
4. Existing semantic clients: `Examples/GroupoidTransport.lean`, `Examples/GroupoidRoutes.lean`, `SquareKit/Internal/PathTransport/`.
5. Bounded higher/cubical clients: `Examples/TwoFamilyStructuralModel.lean`, `Examples/CubicalSourceIdentity.lean`. Their preservation contracts do not give an Agda importer.
6. Bounded elaboration: `Applications/Elaboration/{Syntax,Elaborator,Examples}.lean`. Its typed fixed-sort natural/dependent-vector fragment reduces some elaboration bookkeeping but does not elaborate arbitrary dependent identity elimination or open Agda terms.
7. Source inspection: retained `experiments/dependent-higher-identity/{Monodromy,FrozenMemo}.agda` and `experiments/agda-internal-retention/`. Completed Agda declaration/environment inspection is a possible frontend input. It is not certified source admission, a complete decoded export, or a Lean model of cubical computation.

These changes mean the old and new attempts cannot be treated as identical-interface A/B trials. Any later comparison must name the changed theorem, helpers, public corpus and author provenance. Better syntax or access to Agda internals could reduce transcription work; it cannot by itself prove substitution laws, conversion correspondence, selected-witness preservation or semantic model soundness.

## Evidence required before the assessment

Obtain the independently archived #108 packet and evaluation only after closure:

- Exact prospective protocol, frozen revision, approved theorem/scope and novelty check; independence and permitted communication record.
- Original budget and accounting conventions; completion or stop condition, including a negative/inconclusive outcome without retrospective extension.
- Immutable manifest/archive digests, all submitted successes and failures, commands and validation logs; distinguish author work from evaluator replay/comparison and post-archive repairs.
- Which public helpers were used, which fresh substitution/typing obligations remained, whether any framework change or intervention occurred, and its separately recorded cost.
- Whether the selected source recipe, arbitrary contexts/motives/branches and intended observations were retained. Closed or reflexive examples cannot replace the required quantifiers.
- Checked interpretations/clients, if required by the approved scope, and actual reuse beyond rewriting a final ordinary theorem. Do not demand additional work beyond that scope to rescue the evaluation.
- Comparable effort measurements only where their definitions permit comparison. Report unknown total repair/model cost rather than estimating it from code length or build time.

Also obtain #433's final technical disposition and validation when available. If still partial, carry its concrete missing model obligations into #434 rather than waiting circularly for a favorable authoring result. Technical smooth-entry work and the economic assessment are separate obligations.

After those inputs, the final reviewer can assess bounded selective porting, a separately scoped repair, a frontend investment or reconsideration. This preparation deliberately selects none of them. One new author outcome cannot establish broad scaling or total-cost amortization; a negative outcome can still support a complete assessment. The final durable report and #103/#100 updates require the parent workflow's independent Standards and Spec reviews.

## Historical policy reconciliation

The #106 packet records the former policy that smooth entry should wait for a successful/favorably assessed retest. Preserve that historical record. The approved split into #433 technical construction and #434 assessment supersedes it: no favorable #108 result is required for technical work, and no forced successful attempt is required to close the assessment. Likewise, intermediate repair diagnosis and pending-validation passages should not be mistaken for the status of accepted #107 at the public freeze.

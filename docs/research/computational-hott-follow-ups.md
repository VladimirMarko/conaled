# Computational HoTT follow-up specifications

These construction and experiment scopes follow the research synthesis in
[computational-hott-research.md](computational-hott-research.md). They separate
new mathematical capabilities from source interpretation and authoring evidence.
The issue tracker will hold assignment and current status; the scope below is
the reviewed basis for creating those issues.

Small family codes precede Glue/univalence. Circle elimination can proceed
independently with externally admitted families. The unchanged cover consumer
requires both. The bounded conversion service is independent of that chain.
These dependencies concern the advertised complete deliverables, not a claim
that all exploratory mathematics must wait for every prerequisite.

## Construct small cubical family codes with decoding and substitution

Part of #36; follows #393, #402, #403.

### Objective

Construct the first size/classification milestone needed to interpret the retained circle cover. Existing context-quantified lawful fillers and finite-set codes do not yet provide this internal universe. This ticket does not claim univalence.

### Acceptance

- Pin the selected CCHM/Agda source rules and Lean universe levels. Compare representable-local composition data with existing context-quantified `Filling`; construct the required bridge and uniformity laws. If the size or naturality requirements fail, record the exact obstruction and revise the construction plan before claiming completion.
- Construct a presheaf of codes and decoding for the explicitly admitted small lawful families. Prove code/decode comparisons and arbitrary-context reindexing. Distinguish strict equalities from coherent isomorphisms and justify the exact source rules supported.
- Lift Pi, Sigma, Path and the required discrete families, including the integer-cover fiber, to codes; prove decoding and dependent-substitution compatibility. No self-containing universe or finite-only surrogate closes this scope.
- Exercise a nonconstant dependent code `B : El a → U` under two substitutions, and constructor composition using the existing native providers. Reject an oversized/self code, absent filler and missing uniformity.
- Preserve the existing universe-free clients and identify what still remains for Glue, universe filling, source conversion and operational behavior.

### Research basis

`docs/research/cubical-universe-glue-milestone.md` and `docs/research/fibrancy-capability-assessment.md`; CCHM arXiv:1611.02108v1, Definition 18 and section 8.3. The unchanged source consumer is the retained `experiments/dependent-higher-identity/Monodromy.agda`.

### Validation and boundary

Preserve ordinary Lean callers and existing stronger contracts. Read the architectural quality standard and language direction. Use statement review and checked specializations for formal claims, the README artifact-appropriate build/proof audit, and independent Standards and Spec review. No host axioms or audit exceptions. State literature assumptions, new checked results, execution guarantees and remaining source coverage separately. A failed prerequisite or a partial construction must be reported precisely; it does not silently satisfy the advertised construction milestone.

## Construct cubical Glue and a univalent universe for cover transport

Part of #36; follows #393, #403.

### Objective

Extend the admitted small-family classifier with constructed Glue and universe filling, then prove univalence at that exact scope. This is a semantic construction and source-rule obligation; operational evaluation and cost need separately named contracts.

### Acceptance

- Construct Glue from a partial small lawful family, an ambient family and a genuine homotopical equivalence. State its fiber-contractibility data rather than substituting a mere bijection or natural isomorphism for general equivalence.
- Prove formation, introduction, elimination, full-face, eta and substitution equations. Derive lawful Glue filling with its selected structure; do not accept filling as an unproved field.
- Construct the universe's filling, `ua`, the univalence theorem and the transport comparison, with declared universe levels and no extra host axiom.
- Exercise Boolean transposition and integer-successor orientation, plus structured state-package transport compared with explicit conjugation. Reject malformed face data and non-equivalence gluing; retain direct native equivalence clients.
- Interpret the particular Agda 2.8.0.2 Glue/transp/hcomp rules required by the retained cover, or explicitly leave the exact uncovered conversions to the source-admission consumer. Do not claim a CCHM theorem establishes all Cubical Agda judgments or evaluator canonicity.

### Research basis

`docs/research/computational-univalence-transport.md`, `docs/research/cubical-universe-glue-milestone.md`, and CCHM arXiv:1611.02108v1. Requires the small-family classification milestone; it does not itself construct the circle or indexed identity conversion.

### Validation and boundary

Preserve ordinary Lean callers and existing stronger contracts. Read the architectural quality standard and language direction. Use statement review and checked specializations for formal claims, the README artifact-appropriate build/proof audit, and independent Standards and Spec review. No host axioms or audit exceptions. State literature assumptions, new checked results, execution guarantees and remaining source coverage separately. A failed prerequisite or a partial construction must be reported precisely; it does not silently satisfy the advertised construction milestone.

## Construct cubical circle elimination for the retained cover consumer

Part of #36; follows #402, #404, #405.

### Objective

Construct the circle-family and dependent-elimination capability needed by the retained monodromy source. This is an independently reviewable prerequisite of cover interpretation and can proceed before universe/Glue completion, using explicitly admitted external families.

### Acceptance

- Freeze the selected source circle rules and compatible dimension/face calculus. Audit the actual pinned Cubical circle source and its declaration dependencies, not merely module imports. Compare current providers and Cavallo–Harper's indexed cubical schema under their precise hypotheses.
- Construct the circle family, point and loop constructors, and lawful filling. Construct its dependent eliminator with point, path and required composition equations and prove context/dimension substitution compatibility.
- Include a dependent family consumer with nontrivial loop action and a rejection for inconsistent loop endpoints or boundary data. Separate rules supplied with externally admitted families from internal universe rules not yet constructed.
- State exactly how the constructor/eliminator rules will be interpreted from the selected source. A fresh groupoid or integer-action proof is not unchanged source interpretation.
- Retain general K(Z,2), suspension, hub/spoke truncation and other HITs as residual scope. No generic HIT framework is required unless the chosen construction proves its reuse and scope.

### Research basis

`docs/research/computational-higher-inductive-consumers.md`, `docs/research/cubical-judgment-compatibility.md`; Cavallo–Harper, Computational Higher Type Theory IV, and the experiment's Cubical v0.9 source pin. Coordinate with the small-code/Glue tasks; independent circle construction must not be reported as the complete cover.

### Validation and boundary

Preserve ordinary Lean callers and existing stronger contracts. Read the architectural quality standard and language direction. Use statement review and checked specializations for formal claims, the README artifact-appropriate build/proof audit, and independent Standards and Spec review. No host axioms or audit exceptions. State literature assumptions, new checked results, execution guarantees and remaining source coverage separately. A failed prerequisite or a partial construction must be reported precisely; it does not silently satisfy the advertised construction milestone.

## Interpret the unchanged circle cover and its dependent monodromy witness

Part of #36; follows #393, #402, #404, #405.

### Objective

Connect the constructed cubical capabilities to one unchanged substantive source consumer, preserving its dependent witnesses and the loop-erasure observation. This is not a request for an arbitrary Agda importer or a full smooth/cohesive model.

### Frozen source and acceptance

- Freeze `experiments/dependent-higher-identity/Monodromy.agda`, SHA-256 `bbca6eabc7d35040fd5bb1fcc84f49c12ddfcfb90ffc2edb6d922a8c6e622aa3`, Agda 2.8.0.2 and Cubical commit `b150186d2544e7efeddd31e5d14a8b9ecbb100f7`. Record exact declaration dependencies and any later intentional source change; a changed proof is a separate comparison.
- Interpret source `Cover`, the successor path, Path-to-inductive-identity conversion and the precise rules used by `step`. Source typing, term/dimension substitution and promised conversion must be explicit, not inferred from similar semantic operations.
- Preserve `transport-three`, `transport-two`, `value-and-witness-twice` and `transported-witness-twice` through the interpreted derivation. Retain the observer distinguishing 3 from 2 after erasing the selected loop. Fresh target proofs with the same integers do not satisfy source preservation.
- If an indexed-identity or conversion rule is unsupported, identify it and compare a changed Path-only proof without claiming unchanged reuse. Completion still requires the stated source contract or an explicit owner-approved scope revision.
- Compare the selected construction with a direct native integer-action proof and a Cartesian rederivation, accounting for source admission, setup, repair and preserved observations. Expose the coordinate-preserving connection obstruction without asserting that all Cartesian comparisons are impossible.
- Keep semantic conversion, source evaluation, runtime execution and cost distinct. Any new evaluator requires its own simulation/adequacy contract. Smooth/cohesive realization remains under #36/#100; the complete higher K(Z,2) artifact remains separate.

### Research basis

`docs/research/computational-higher-inductive-consumers.md`, `docs/research/cubical-judgment-compatibility.md` and the preserved experiment. Depends on the Glue/univalent-universe and circle-elimination constructions; their acceptance does not automatically discharge this source-interpretation task.

### Validation and boundary

Preserve ordinary Lean callers and existing stronger contracts. Read the architectural quality standard and language direction. Use statement review and checked specializations for formal claims, the README artifact-appropriate build/proof audit, and independent Standards and Spec review. No host axioms or audit exceptions. State literature assumptions, new checked results, execution guarantees and remaining source coverage separately. A failed prerequisite or a partial construction must be reported precisely; it does not silently satisfy the advertised construction milestone.

## Add optional open beta-eta conversion for the dependent-function fragment

Part of #36; follows #398, #399.

### Objective and baseline

Supply an optional executable equality service for generated `SquareKit.Internal.DependentFunctions` terms, retaining open binders and dependent result-family indices, and assess it against the existing direct helpers. Coordinate #235/#401. This does not activate #260, reopen #214, or resume protected #107/#108 tasks.

### Acceptance

- Freeze the well-typed Dep/Func grammar, existing DepEq/FuncEq relation, context rules and a concrete generated-term consumer. Use existing `FuncEq.eta`, `DepEq.beta`, `substituted_eta`, `substituted_beta` and interpretation laws as the unrestricted native baseline.
- Define normal/neutral syntax and an executable conversion service. Compare a direct structural normalizer with typed NbE before selecting machinery. Prove soundness, completeness for the admitted relation including typed substitution, and termination separately. An incomplete recipe checker cannot close the full-conversion milestone.
- Retain formation, result-family index and free-variable identity through weakening and binders. Prove renaming and substitution compatibility up to re-normalization; reuse interpretation soundness without assuming semantic equality reflects source conversion.
- Supply two-substitution eta/beta fixtures, changed-free-variable/index rejection and a dependent-index repair. Return existing checked derivations through an optional author interface with explicit annotations, expected-type policy and diagnostics. Conversion completeness does not imply arbitrary elaboration/hole-solving completeness.
- Compare independent direct-helper and optional-service authors on the same frozen task and a held-out binder variant. Record model/version, tools, resources, assistance, repairs, diagnostics and successful checks; separate engine/setup cost from author cost. Do not claim productivity improvement if the native route is as effective or cheaper. A negative adoption decision may retain the proved optional service.
- Do not advertise this base-domain dependent-function fragment as arbitrary Pi, cubical syntax, univalence or full equality reflection. The #401 selected higher-coherence obligation remains a separate admission condition unless genuinely expressible here; preserve higher witnesses rather than replacing them with conversion.

### Research basis

`docs/research/open-term-normalization.md` and `docs/research/typed-nbe-and-authoring.md`. Full cubical normalization, universes/HITs, global subtyping and historical assistant recreation are outside scope. Partial, lazy and noncomputable settings retain their own observation contracts.

### Validation and boundary

Preserve ordinary Lean callers and existing stronger contracts. Read the architectural quality standard and language direction. Use statement review and checked specializations for formal claims, the README artifact-appropriate build/proof audit, and independent Standards and Spec review. No host axioms or audit exceptions. State literature assumptions, new checked results, execution guarantees and remaining source coverage separately. A failed prerequisite or a partial construction must be reported precisely; it does not silently satisfy the advertised construction milestone.

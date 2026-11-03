# Reusing higher theory and outsourcing coherent blocks

Investigated 2026-10-20 against the retained #96 decision and the current source
checkouts listed below. This note supplements
[the tangent integration assessment](myers-tangent-integration.md). The initial
investigation did not change #98/#99 or authorize a dependency, port, or new
foundation.

Subsequent planning: [#100](https://github.com/VladimirMarko/conaled/issues/100)
now organizes this integration milestone under #36.
[#101](https://github.com/VladimirMarko/conaled/issues/101) owns the concrete
authoring/model interface design that #96 did not implement. It can proceed
independently of #98; #99 requires their reviewed outcomes and interface
reconciliation. #97 remains deferred.

The owner clarified that external ChatGPT Pro formalization has sometimes
worked but is slow and unreliable as a workflow. Porting selected Agda theory
remains desirable; outsourcing is undecided. The packages below are useful
units of work even when implemented sequentially with local tools. They must
not depend on reliable parallel delegation or external-session throughput.

**Recommendation:** stop treating the next semantic lemma as the only available
work. Develop a reusable higher-language block and a smooth-model block under
one shared contract, while using existing HoTT libraries as proof sources.
Delegate whole mathematical interfaces with checked consumers, rather than
asking each agent to discover another prerequisite. Do not make implementing
all of HoTT or all of SDG an entry condition.

The source search found substantial relevant formal mathematics. It did not
find an inspected library providing the entire Lean-checked chain

```
internal derivation → constructed smooth higher model → classical Lean theorem.
```

That last statement is an evidence boundary for this search, not a claim that
no such project can exist. None of the external Agda checkouts was rebuilt in
this investigation. Capability statements below come from inspected source;
upstream toolchain claims are distinguished from local validation.

## Reuse candidates and foundation boundaries

| Candidate and inspected revision | Existing body of work | Internal theory | Constructed smooth semantics and classical Lean comparison |
| --- | --- | --- | --- |
| [agda-unimath](https://github.com/UniMath/agda-unimath/tree/75518656f287c203b41cb7f71df46e02b987a084) | Torsors, classifying types, group actions, identity/transport, truncation, synthetic descent, modalities, flat/crisp reasoning | Native intensional Agda with explicit univalence assumptions; modal files use extra crisp rules and postulates | No interpretation into this repository's smooth site found in inspected modules; mathematical proof reuse requires an explicit interpretation or proof translation |
| [Cubical library](https://github.com/agda/cubical/tree/c37782bb4e382dc41035e0970409a0c17b55e6ce) | Univalence, HITs, homotopy theory, general modality interface and lex properties | Computational cubical paths; library flags include `--safe --cubical` | Cubical checking does not prove a Lean interpretation; no smooth-model bridge found in inspected modules |
| [Generated deloopings](https://github.com/smimram/generated-deloopings-agda/tree/e448f006d24719f631d4d8b17cf3b3d94efb0a96) | Torsor delooping of groups, action equivalences, principal-torsor automorphism group, generated presentations | Concrete Cubical Agda proofs; useful whole torsor/delooping block | Not sheaf torsor descent or nilpotent invariance on our site |
| [DCHoTT-Agda](https://github.com/felixwellen/DCHoTT-Agda/tree/ca8c755af0b26f8f50c5a60d3b7f9384a26f5d0e) | Formal disks, formally étale maps, formal disk bundles, homogeneous spaces, associated bundles | Differential/modal HoTT arguments over postulated coreduction and univalence | Does not construct the modality on our smooth site or compare to Mathlib manifolds; formal disks must not be identified with our first-order `D` without a theorem |
| [HoTT-Agda](https://github.com/HoTT/HoTT-Agda/tree/1037d82edcf29b620677a311dcfd4fc2ade2faa6) | Extensive older HoTT, HIT and modal proof library | `--without-K --rewriting`, postulated univalence | Older proof reference; no direct Lean dependency or smooth realization |

### agda-unimath: substantial torsor and source-language material

[`group-theory/torsors.lagda.md`](https://github.com/UniMath/agda-unimath/blob/75518656f287c203b41cb7f71df46e02b987a084/src/group-theory/torsors.lagda.md)
constructs `Torsor-Group`, its principal object, torsor equivalence/identity
characterization, connectedness, `classifying-type-Group`, and
`group-concrete-group-Group`, an isomorphism recovering the original group.
The universe rises explicitly to `lsuc l1`; a port must preserve that fact or
prove the required resizing. This is more useful than rebuilding the
classifying-space argument theorem by theorem.

The library's `synthetic-homotopy-theory/descent-*` files concern descent for
synthetic constructions such as pushouts and the circle. Their names do not
establish descent of torsor sheaves for our arbitrary-principal topology.
Likewise, the [univalence module](https://github.com/UniMath/agda-unimath/blob/75518656f287c203b41cb7f71df46e02b987a084/src/foundation/univalence.lagda.md)
postulates its univalence witnesses. It is a proof source in a stated theory,
not evidence that native Lean equality can retain isotropy.

The [flat module](https://github.com/UniMath/agda-unimath/blob/75518656f287c203b41cb7f71df46e02b987a084/src/modal-type-theory/flat-modality.lagda.md)
uses `--cohesion --flat-split`, defines `♭` with a crisp constructor, and proves
its idempotence. The [sharp module](https://github.com/UniMath/agda-unimath/blob/75518656f287c203b41cb7f71df46e02b987a084/src/modal-type-theory/sharp-modality.lagda.md)
explicitly postulates sharp, its rules and computation properties, and labels
some further text as unfinished, untypechecked notes. The flat-sharp
adjunction is also postulated. These are valuable rule and proof inventories;
they do not settle which modal laws the proposed smooth model satisfies.
Combining this code with Cubical Agda also needs care: the
[official flat documentation](https://agda.readthedocs.io/en/latest/language/flat.html)
warns that pattern matching on crisp arguments in Cubical Agda can trigger
`UnsupportedIndexedMatch` and fail to compute properly. A common Agda
implementation does not make the two libraries' rule sets interchangeable.

### Cubical proofs and a focused delooping application

The Cubical library's
[`Modality`](https://github.com/agda/cubical/blob/c37782bb4e382dc41035e0970409a0c17b55e6ce/Cubical/Modalities/Modality.agda)
record abstracts the modal predicate, reflector, unit, dependent elimination
and computation. Its file credits translation from HoTT-Agda. This is a
precedent for moving a coherent theorem interface between foundations, while
rechecking its proofs. It is not itself a cohesive or differential instance.

The generated-deloopings project's
[`Deloopings.agda`](https://github.com/smimram/generated-deloopings-agda/blob/e448f006d24719f631d4d8b17cf3b3d94efb0a96/Deloopings.agda)
defines `BG` from the component of the principal `G`-set, proves `isGroupoidBG`,
and proves `PGloops : GroupIso (π₁ ...) G`. `GSetProperties.agda` supplies
identity/equivariant-isomorphism comparison. This is a suitable source for a
bounded package covering group actions, torsors, delooping and transport.
Its external paper is [*Delooping generated groups in homotopy type theory*](https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/docs/mimram_generated_delooping.pdf).
The torsors here live in the source type theory. Making them into locally
trivial objects of the existing smooth topos is additional work.

### DCHoTT: reuse differential arguments as a block

[`Im.agda`](https://github.com/felixwellen/DCHoTT-Agda/blob/ca8c755af0b26f8f50c5a60d3b7f9384a26f5d0e/Im.agda)
postulates an infinitesimal-shape operator, unit, idempotence, induction,
computation and closure of modal identity types. It derives functoriality and
further laws. [`FormallyEtaleMaps.agda`](https://github.com/felixwellen/DCHoTT-Agda/blob/ca8c755af0b26f8f50c5a60d3b7f9384a26f5d0e/FormallyEtaleMaps.agda)
defines étaleness through the unit naturality pullback.
[`FormalDiskBundle.agda`](https://github.com/felixwellen/DCHoTT-Agda/blob/ca8c755af0b26f8f50c5a60d3b7f9384a26f5d0e/FormalDiskBundle.agda)
constructs formal disk bundles and proves triviality over homogeneous types;
its transport argument is relevant to the selected Myers consequence.
The observed hole markers in that file occur inside a commented-out proposed
lemma; they must not be reported as holes in the checked triviality theorem.

This is a direct answer to the request for existing differential HoTT proof
material. A delegation could extract the required modal calculus, formally
étale transport and bundle consequences together. It must first reconcile the
operator's assumptions with Myers' crystalline modality and the finite
first-order target. Renaming the operator would not establish that agreement.
In particular, `Im.agda` contains a live `ℑ-is-lex` postulate inside its
`identity-types-of-sums` experiment, used to define `ℑ-transport`. The nearby
unfinished `encode` argument is commented out. Myers' Warning 4.3.9 rules out
assuming ordinary left exactness of the crystalline modality. Audit the
selected declarations' dependencies and exclude that stronger principle
unless a different model and an appropriate theorem justify it. A textual
search found no uses of `ℑ-transport` outside that experiment; this is not
a compiled transitive dependency audit.
No license file was found in the inspected repository tree. Treat it as a
mathematical reference until code reuse permission is established.

The smaller [Cohesion-Agda](https://github.com/dlicata335/cohesion-agda/tree/6cf2f4e1085701f10ca4945b8ccdaecc6de3744c)
contains `FlatSharp*.agda` experiments with postulated modal principles and
rewrite rules. It is useful provenance for rule design, but was not selected
as the basis of a broad port. No README or license was found in its tree.

## Toolchains and licenses inspected

| Source | Toolchain evidence at inspected revision | License evidence |
| --- | --- | --- |
| agda-unimath | `.github/workflows/clean-build.yaml` selects Agda 2.8.0; library uses `--without-K` | `LICENSE.md`: MIT |
| Cubical library | README says current master/v0.9 works with Agda 2.8.0; `.agda-lib` names cubical-0.9 | MIT with individual-file exceptions listed in `LICENSE`; check the selected import closure |
| Generated deloopings | README reports testing with Agda 2.6.3 and Cubical 0.5 | `LICENSE`: MIT, Champin and Mimram |
| DCHoTT-Agda | README says Agda 2.6.2.2 | No license file located |
| HoTT-Agda | README requires Agda 2.5.3 and says newer support is lacking | MIT |

These versions cannot be combined by merely pointing one Agda invocation at
all repositories. A reproducible delegated package should pin one compatible
upstream stack, rebuild its chosen closure, and inventory postulates,
rewrites, unchecked literate blocks and generated artifacts. Native Agda
checking is evidence about that source theory, not a replacement for the
repository's Lean axiom audit.

## Books as specifications for delegated blocks

Use books to supply established proofs and dependencies, not as instructions
to formalize every chapter in order.

- [Rijke, *Introduction to Homotopy Type Theory*](https://arxiv.org/abs/2212.11082),
  with its [formalization project](https://github.com/HoTT-Intro/Agda), supplies
  organized proof material for identity, equivalence, truncation and synthetic
  homotopy theory. Prefer agda-unimath's inspected modules where they already
  contain the required block, rather than a second foundations port.
- [*Homotopy Type Theory: Univalent Foundations of Mathematics*](https://homotopytypetheory.org/book/)
  supplies the common statement vocabulary. The existing #96 assessment pins
  its relevant identity/transport sections; it is not a ready-made Lean model.
- [Kock, *Synthetic Differential Geometry*, second edition](https://users-math.au.dk/kock/sdg99.pdf),
  separates synthetic reasoning from algebraic/sheaf model construction.
  Use it for broader SDG packages only when a selected application needs them;
  the repository has already implemented substantial first-order material.
- [Moerdijk–Reyes, *Models for Smooth Infinitesimal Analysis*](https://link.springer.com/book/10.1007/978-1-4757-4143-8)
  is a model-construction reference to examine for any proposed larger smooth
  model package. Only its publisher record was checked in this investigation;
  no uninspected theorem from the book is claimed to solve the current torsor
  or higher-language obligation.

## Delegation packages that advance the complete bridge

The following are proposed work contracts, not new tickets or assignments.
Each should use independent review against its whole contract. Parallel work
starts after the source and model interfaces agree.

1. **Reusable identity/action/torsor source block.** Extract from agda-unimath
   or generated-deloopings the dependency closure for action quotients,
   stabilizer identity and transport. Produce reusable derivations in the
   agreed Lean-hosted fragment, with explicit universe and truncation
   requirements. Require two consumers: the singular quarter-turn action and
   an ineffective finite action. Include the soundness obligations as named
   interfaces; source proofs alone are only this package's output.
2. **Smooth higher interpretation block.** Reuse Mathlib's category/descent
   infrastructure and audit SynthLean's relevant model components as already
   proposed in #96. Construct the required groupoid-stack interpretation,
   substitution/identity transport and set-family operations, with a discrete
   embedding preserving the existing `R`, `D` and KL comparison. #98's torsor
   invariance is a gate inside this coherent package, not a reason to defer
   designing the source interpretation indefinitely.
3. **Differential quotient comparison block.** Consume the first two contracts
   to interpret the selected quotient/tangent derivation and recover the
   existing classical quarter-turn derivative and stabilizers. Require the
   same source proof to serve the ineffective-action test. This is the
   end-to-end integration test that prevents parallel libraries from remaining
   unrelated.
4. **Conditional modal theory block.** If the intended source theorem truly
   requires the modal proof rather than the bounded lifting formulation,
   delegate a complete formally-étale/formal-disk calculus using DCHoTT and
   Myers as references. Its contract must enumerate the modal/crisp laws and
   require evidence that the selected model validates them. Postulated laws
   in an external formalization are requirements to discharge, not Lean
   axioms to import. Do not make this larger block prerequisite to the bounded
   end-to-end test without a proof dependency justifying it.

A useful first milestone is one preserved identity/transport theorem through
both layers, including a nontrivial automorphism. It tests the transfer
mechanism before funding a large source port. After that, agents can own
whole blocks and run their review/fix loops autonomously. Reviews should ask
whether the integrated consumer works, not merely count completed lemmas.

If using Agda as an external proof authoring system is desired, there is an
additional engineering project: export a specified proof fragment to checked
Lean derivations and prove its interpretation sound. A general Agda-to-Lean
translator is not provided by any inspected source. A scoped exporter or
manual translation of a coherent theorem block may be worthwhile; choosing
between them requires a small transfer experiment. Trusting an Agda verdict
as a new Lean axiom would change the accepted verification contract.

## What this changes in the plan

#96 was right to expose the torsor/model compatibility gap, but its statement
that no broad formal-library search was proposed was too narrow as an overall
work-allocation strategy. Existing libraries cover enough of the higher and
modal proof layer to justify outsourcing larger blocks now. They do not remove
the need for the model interpretation, and they should not be used to postpone
that interpretation behind a complete new HoTT library.

Keep #98 as a discriminating semantic checkpoint. In parallel, prepare a
bounded source-proof block and its interpretation contract. Judge progress
by the completed source/model/classical chain and the number of additional
applications it supports, rather than by how much foundational theory has
been accumulated. The initial research did not change issue scope or status;
the subsequent organization is recorded in #100 and #101 above.

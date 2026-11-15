# A structural consumer over represented families

Issue [#324](https://github.com/VladimirMarko/conaled/issues/324) exposes the
sections-over-a-base construction through the existing `IndexedFamilies` and
`Representation` interface. It preserves the old `StructuralModel` consumer
exactly and exercises the same construction with dependent functions, the
native Type provider, the groupoid provider and the interpreted universal
transport client. It adds no capability hierarchy or model-builder fields.

## Selected construction and its requirements

Given a family `A` over `Γ` and a substitution `f : Δ → Γ`, the construction
identifies a section of `A[f]` with a map `Δ → Γ.A` whose projection is `f`.
The map remembers the selected section. The inverse recovers that section,
including its dependent type. Further substitution commutes with this
correspondence.

The earlier consumer is
`StructuralModel.sectionsOver` in
[`Comprehension.lean`](../../SquareKit/Internal/PathTransport/Comprehension.lean).
It takes a full structural model even though the proof uses no empty context,
base/fiber signature, identity type or reflexivity operation. The independently
defined [`RepresentedFamilies.lean`](../../SquareKit/RepresentedFamilies.lean)
already provides the appropriate structural interface. This change builds
`Representation.sectionsOver` there and derives its substitution law from
`pair_natural`.

| Data or law | Role in the consumer |
|---|---|
| A category of contexts | Supplies maps, composition and identities. |
| Families, sections and strict reindexing | Gives the dependent source and target types. |
| Chosen representing objects and natural hom-set equivalences | Supplies pairing, projection, generic variable and uniqueness. |
| Pair projection, variable, eta and naturality | Derived consequences, reused rather than new provider fields. |
| Type substitution composition | Aligns the inverse's dependent type. |
| Type substitution identity | Aligns the identity-base specialization `Representation.sections`. |
| Empty context, base/fiber signature, Id, reflexivity and J | Absent from the independent provider and structural construction. |

This is not a claim that every field of `IndexedFamilies` is needed by every
individual lemma. That interface also carries term identity/composition laws
for its other clients. It remains a strict reindexing presentation; it is not
the weakly stable comparison sought by #325.

Three choices were considered. Direct parameters could expose each operation
and law used by this proof, but would make this consumer repeat a large
dependent parameter list and its representing-equivalence contract. A new
family of capability records would duplicate the existing representation.
Using `IndexedFamilies.Representation` gives an independently constructed
provider and an existing old-model adapter, so it is the chosen scope here.
Further factoring should respond to another actual consumer.

## Recovering existing providers and terms

[`Representability.lean`](../../SquareKit/Internal/PathTransport/Representability.lean)
already adapts an arbitrary `StructuralModel` to indexed families and a
representation. Its projection, generic variable and pairing recovery results
retain the selected operations. The new `representedSectionsOver` applies the
independent consumer through that adapter. `representedSectionsOver_eq` proves
equality with the complete old equivalence, so both its forward map and its
inverse are recovered, not merely an isomorphism class of maps.

The old entrypoint is retained to avoid an unrelated import restructuring:
`Representability` currently imports `DisplayCategory`, which imports
`Comprehension`. The independent implementation is available to new structural
consumers without importing that chain. The adapter theorem establishes exact
agreement rather than leaving two unconstrained implementations.

The identity-base specialization represents an arbitrary selected term as a
section of its display projection. It can therefore consume a term constructed
using richer operations without requiring those operations itself. The selected
extension is `Authoring.UniversalTransfer.proof`, the existing contextual-J
construction for transport along a concatenation.

Constructing that source proof still requires the existing base/fiber
declarations, identity/reflexivity and contextual J with its beta and
substitution laws, including the generalized dependent variables used by the
command. The independent representation does not derive these capabilities.
`FullClient.transportArrow` packages the actual interpreted certificate;
`recoveredTransport_eq` recovers the complete semantic section for every
supplied full model. `recoveredTransport_sub` preserves it under an arbitrary
context substitution. These equalities precede extracting a groupoid endpoint
equation and do not rely on a proof-irrelevant native specialization.

This is reuse of a structural consumer by a full dependent client. It is not
the migration in #328, a new implementation of J, or evidence that the higher
models in #321/#322 are complete.

## Checked cases and statement boundaries

[`Examples.DependentCapabilities`](../../Examples/DependentCapabilities.lean)
contains the retained cases:

- `SignatureFree` uses the direct dependent-function representation, without
  constructing any `StructuralModel`. Its fibers are `Fin (n + 1)`, its base
  map doubles an input, and its selected section retains that input as a fiber
  index. Substituting successor first sends input `3` to base `8` with fiber
  value `4`. Reversing those base maps would give `7`, so the case detects
  composition order through `sectionsOver_natural`.
- Distinct sections of the two-element family produce distinct represented
  arrows. The proof uses injectivity of the new equivalence, checking that an
  implementation which kept only existence could not satisfy this contract.
- `Native` specializes the old-model adapter to the existing Type provider
  with `Nat` and `Fin (n + 1)`. Its chosen lifted pairing function agrees with
  the expected dependent pair at every input.
- `Groupoids` specializes the same adapter to the existing cyclic-groupoid
  binary family. It recovers complete sections and records the family's
  nonidentity action: the generating loop sends `0` to `1`. The generic
  recovery theorem concerns sections, including their arrow data, rather than
  only the values at objects.
- `FullClient` uses the named universal transport derivation and preserves its
  selected interpretation and arbitrary substitution for every full provider.

Statement review checked the direction of composition, the common dependent
family of the recovered section, arbitrary rather than source-only base maps,
and the equality level. The equivalence laws compare actual terms and maps in
the chosen semantic presentation. They assert neither object-language identity
reflection nor equality between different providers. Concrete dependent
functions and the existing groupoid model give usable instances; the generic
full-model theorem remains conditional on supplying its stated provider.

No additional assumptions are imposed on existing Type or groupoid providers.
New structural callers supply the existing category/indexed-family/
representation interface, with no dummy signature or identity fields. The
old full dependent caller keeps its existing assumptions and source recipe.

## Remaining work

#325 owns comparisons between different selected presentations, #326 and #330
own source adequacy and generated-empty uniqueness, and #327/#331 own the
weaker dependent-sum contract. None is supplied by this structural equivalence.
The [finitary-calculus study](https://github.com/VladimirMarko/conaled/issues/332)
records the broader architectural comparison. Existing strong interfaces stay
available while those investigations proceed.

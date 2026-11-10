# Selected generated signature comparisons (#446)

The implementation constructs selected comparisons on the existing generated
interpretation from a primitive natural isomorphism and its compatible fiber
square. The context, family, section, substitution, root/tail and smooth-source
results have focused Lean checks. Parent orchestration owns the fresh integrated
build, exhaustive proof audit and independent Standards/Spec reviews. This file
does not claim completion of those acceptance steps or of #433's descent work.

## Construction and selected data

`SignatureCylinder` uses objects `(c, d, i : F c ≅ d)` with arrows inherited
from `C`. Projection to `C` is an equivalence. Evaluation sends `f` to
`i⁻¹ ≫ F f ≫ j`. The endpoint inclusions select identity and the supplied
`η : F ≅ G`. Fibers are pulled back from `C`; evaluation uses
`α c ≫ Q.map i.hom`.

Existing generated composition and equivalence results make the generated
projection an equivalence and both generated endpoint maps its strict sections.
The unique lift of identity gives `generatedEndpointIso`; evaluation and proved
endpoint equalities give `contextComparison` between the original generated
maps. Neither compared base functor nor primitive fiber map must be invertible
or faithful. Only the auxiliary projection needs an equivalence.

`GeneratedCylinderPrimitive.contextComparison_primitive` identifies the
comparison at the generated base context with the supplied primitive natural
isomorphism, with explicit endpoint normalizations.
`normalizedPrimitiveComparison_fiber` recovers exactly `η.hom.app c`.
This is recovery from the generated comparison, beyond recovery inside the
primitive cylinder.

## Coherence and dependent families

The public context laws are:

- `GeneratedCylinderIdentity.contextComparison_refl`.
- `GeneratedCylinderComposition.contextComparison_trans`.
- `GeneratedCylinderPostcompose.contextComparison_postcompose`.
- `GeneratedCylinderPrecompose.contextComparison_precompose`.
- `GeneratedCylinderCoherence.contextComparison_substitution` for every
  supported generated substitution, including root and finite-tail maps.

Change-of-reference and pre/postcomposition functors between cylinders preserve
projection and evaluation. Uniqueness of the selected lifts proves the context
laws; their endpoint transports are retained explicitly. Individual
`Comparison.Section` and `Comparison.Substitution` strict fields are unchanged.

`GeneratedCylinderFamilies.familyComparison` extracts a dependent family
modification from the comprehension comparison. Its base is the selected context
component. Naturality along every actual base arrow follows from total-category
naturality, without a faithfulness assumption on the compared maps.
`TotalModification.modification_total` proves that reconstructing comprehension
from the extracted components recovers every original total arrow.
`GeneratedCylinderFamilyLaws` proves identity, vertical composition and both
whiskering laws for those total family comparisons. Together with
`familyComparison_total` and the faithful fiber inclusions used by the
extraction, these laws retain the selected fiber components, rather than only
an isomorphism class.

## Root, counit, branches and J

`GeneratedContractionSquares.generatedRootTail_square` uses the actual native
normalized root/tail contractions at the direct endpoints, including their
chosen inverse functors and counits. `contextComparison_rootTail_counit`
derives the selected external counit square from the root substitution square.
Its branch comparison is the same `contextComparison` at the generated branch
context; finite dependent tails are unrestricted within the supported syntax.

`GeneratedCylinderTerms.contextComparison_section` is the square of actual
interpreted whole-section functors. It is derived using the generated pairing
substitution for the supplied source term. It applies to contextual J, its
endpoint applications and reindexed branches. No generated compatibility,
counit compatibility, or J-preservation field is supplied by the caller.
The underlying generated composition result already proves strict J
preservation through the existing contraction construction.

The checked two-binder path-command example has a second binder depending on
the first. It exercises both the selected contraction counit and the actual
contextual-J section. Another example checks its reindexed tail substitution.

## Actual smooth square and retained source

`SmoothQuotientGeneratedBaseChange` applies the construction to
`Descent.baseChangeComparison` and `CocycleDatum.fiberBaseChange_square`.
`primitive_square` derives the required orientation with the existing
`fiberComparison` inverses. Its context and family comparisons use the actual
cocycle, quotient and all-torsor deformation families.

`SmoothQuotientGeneratedBaseChangeSource.leftSignature_composed` and
`rightSignature_composed` identify both routes with the existing actual
horizontal signatures. `UniversalTransferComparison` obtains the type
derivation for the unchanged `Typed.Authoring.UniversalTransfer.proof` and
feeds that source derivation to the section theorem.
`universalTransfer_square` is its actual smooth specialization. The named
`SectionCoherence` proposition states the same whole-section equation while
avoiding repeated expansion of the large source code in theorem headers.
All elaboration and kernel limits remain unchanged.

`Examples/SmoothSelectedComparison.lean` specializes that source square to the
models used by `origin_classical_composition` and `ineffective_composition`,
and to the independent dependent-J caller. It also checks the existing
generated parameter identity and composition laws at the unchanged source
context, using two restrictions along `SmoothTorsors.killEps`, whose
nonidentity proof is retained. Distinct ineffective quotient arrows remain
distinct. These comparisons do not assert effectiveness of independent
matching data; that obligation belongs to #445 and integration into #433.

## Statement review and examples

The quantified primitive hypothesis is an equality of natural transformations
`α ≫ whiskerRight η.hom Q = β`. It includes actual-arrow naturality; it is not
an objectwise equality or a generated preservation assumption. Conclusions are
natural isomorphisms of whole context functors, coherent dependent family
components, and equations using the same selected components.

`Examples/SignatureCylinder.lean` checks unequal isomorphic base functors and
a noninjective primitive fiber map. `Examples/GeneratedSelectedComparison.lean`
adds a nonfaithful C4 base map, the dependent J/tail callers, exact recovery of
a selected nonidentity C4 quarter-turn with trivial fiber action, and the
unchanged source wrapper. Its negative checks establish:

- Strict equality of the generated base-family maps would identify unequal
  primitive functors.
- Individually invertible objectwise choices can fail naturality along a
  bridge arrow and therefore cannot supply the primitive natural isomorphism.

The original source transport consumers and their classical derivative and
ineffective-arrow results remain imported. The new tests concern selected
comparison data and source interpretation, rather than replacing those
consumers with direct semantic transport calculations.

## Validation boundary

All added modules and examples receive focused checks with the repository's
pinned toolchain and default heartbeat limits. The root application imports
both new regression files, so integrated acceptance includes their declarations.
Focused axiom inspection of 19 public results and negative examples found only
`propext`, `Classical.choice`, and `Quot.sound`. The driver and log are retained
at `/tmp/conaled-445-448-orchestration/446-focused-axioms.lean` and the adjacent
`.log` in this session. Independent review and fresh integrated acceptance are
still required before marking #446 done.

# Constructor substitution and recomputation

The native Pi and Path decoder comparisons have identity and composition laws
in both cube models. The original model also has whole-section recomputation
for its dependent pair and function transport algorithms. Comparing the two
canonical decoder transports gives a native path retaining the original and
rebuilt comparison bodies. For the original model, the fixed Sigma and Pi
constructors now preserve those complete selected bodies exactly when rebuilt
after substitution. The corresponding native Cartesian result remains under
[#671](https://github.com/VladimirMarko/conaled/issues/671), following the
algorithms developed independently in #631.

## Decoder comparisons

For `R = pi a b`, `piSubstitution a b σ` has source
`liftedDecode (σ ≫ R.code)` and target
`liftedDecode (pi (σ ≫ a) (liftSub (liftedDecode a) σ ≫ b)).code`.
Its three factors are the restricted old decoder, the native Pi reindexing
isomorphism, and the inverse rebuilt decoder. `piSubstitution_comp` cancels
the intermediate decoder and uses the native reindexing composite. The Path
law has the same three factors, reindexing both endpoint sections as well as
the family over the interval. Identity laws retain the same explicit decoder
adapters. These are family-isomorphism equalities, not equality of code maps.

`LargeFamilySubstitution` and `CartesianLargeFamilySubstitution` expose the
matching native laws. Their existing `*_filling` results preserve complete
returned filling operations; the Cartesian operations include variable caps.
Those contracts and the preexisting negative controls are unchanged.

## Whole sections and actual transports

Put `L = liftSub (interval Ξ) σ`, `a' = L ≫ a` and
`b' = liftSub (liftedDecode a) L ≫ b`. `pairSection_reindex` identifies the
whole freshly rebuilt pair section with the original section restricted by
`L`. Its initial pair is `z.reindex σ`. `functionSection_reindex` gives the
same equality through `piReindexIso`, including its endpoint-zero adapter on
the initial function. It reduces the complete
backwards-argument function algorithm to its selected Pi forward section and
uses the whole-operation Pi filling reindexing law.
Neither theorem replaces sections with endpoint values.

For a constructor result `R` and a section `z`, `transportInFamily` expresses
the actual canonical decoder transport in the constructor family.
`comparisonInFamily` maps the existing `transportComparison` through the
endpoint-one decoder. `comparisonInFamily_body` is exact equality of the
complete body after that map. `transportFromSection_body` also identifies
that body with the public pair/function transport formulas, whose endpoint
proof relabeling leaves the body unchanged.

Given an independently constructed `S : Result D`, a family isomorphism
`e : C ≅ D`, and independently reconstructed `w : Term D` satisfying
`Term.map e.hom z = w`, `rebuiltComparison` maps the entire comparison chosen
by `S` back into `C`. `rebuiltComparison_body` records this body explicitly.
`compareRebuilt` concatenates the original comparison with the reverse of
that rebuilt comparison. The result compares the two actual transports,
using their common reconstructed section. It assumes no equality of their
fillers or of their comparison bodies. `pairRecomputedComparison` and
`functionRecomputedComparison` establish the section premise from the new
recomputation laws; callers do not supply a final preservation theorem.
`compareRebuiltTwice` composes two such comparisons, mapping the second back
through the first family isomorphism. `pairRecomputedComparisonTwice` and
`functionRecomputedComparisonTwice` supply the two actual rebuilt sections
and their comparison premises. All three canonical transports and both
constituent paths remain in this composition.

## Exact fixed-constructor bodies

After these explicit family and decoder adapters, the stronger equation is

```lean
pathApp (R.comparisonInFamily z) =
  pathApp (S.rebuiltComparison e z w hw)
```

For substitution, `R` here is the restricted original result, and `S` is the
constructor freshly rebuilt from substituted codes. The right side uses
`NativeDecode.filling S.code`; the left side uses the restriction of
`NativeDecode.filling R_original.code`. `transport_eq_of_comparisonBody_eq`
checks a necessary consequence: their actual transported starts must agree
under the endpoint adapter. The common finish alone does not supply this
condition or the whole-body equation.

The exact selected-operation obligation before applying comparison naturality
is, for the Sigma or Pi decoder comparison `d` over the substituted line,

```lean
((NativeDecode.filling R_original.code).reindex L).transport d =
  NativeDecode.filling S.code
```

This retains the full operation, every context, face and cap. The completed
[#607 recovery](canonical-decoder-filling-recovery.md) proves this equation
as `sigmaSubstitution_native_filling` and `piSubstitution_native_filling`.
It first recovers the supplied full lawful operation through
`SmallPresentation.Data.code` and `nativeIso`, including the represented
chart, lowering and decoding steps. Equality of the displayed families alone
would not give this recovery. The result identifies `NativeDecode.filling`
with the returned selected operation for the fixed construction; the two
operations remain distinct in the general interfaces.

`NativeTransportComposition.sectionComparison_body_transport` supplies the
other part of the proof. It maps the actual `sectionsInitial` path through
the family isomorphism, using the existing
`SelectedPathTransport.reindex_inverse_map`. The existing
`SelectedPathTransport.filling_transport` preserves the selected Path filler.
Transport of the forward filled section then preserves `sectionsFilled`.
The last endpoint restriction gives equality of the full `sectionComparison`
body. None of these steps replaces the selected filling algorithm or assumes
that paths with the same endpoints agree.

`Result.comparison_body_eq_of_filling` combines this naturality with an
explicit full-operation preservation equation. Its decoder-section
roundtrips and endpoint isomorphism cancellation retain the actual original
and rebuilt bodies. The public `pair_comparison_body_recomputed` and
`function_comparison_body_recomputed` discharge that equation using #607 and
supply the section equality from `pairSection_reindex` and
`functionSection_reindex`. Their statements are exactly the displayed
whole-body equation for independently rebuilt Sigma and Pi, with `Iso.refl`
and `piReindexIso` respectively. Callers supply codes, an initial section and
a substitution; they do not supply a comparison-body equality or a filler
preservation hypothesis.

Arbitrary independently selected paths are different: equal endpoints do not
determine the body. The checked `independent_bodies_not_equal` control uses the
existing nonreflexive universe loop and the reflexive loop at the same code.
It is a counterexample to endpoint-determined selection, not a counterexample
to the fixed constructor's recomputation equation. The positive control
`comparisonInFamily_body_reindex` retains exact body equality when the same
result is restricted.

The earlier `compareRebuilt` and two-step comparison interfaces remain
available. The new exact fixed-constructor results strengthen what callers
can prove about their selected constituents. The general interfaces still
allow independently selected operations, for which exact equality needs an
additional preservation theorem.

This is the original-model milestone of
[#671](https://github.com/VladimirMarko/conaled/issues/671), not closure of
its full scope. The Cartesian branch must use the native variable-cap
algorithms from [#631](https://github.com/VladimirMarko/conaled/issues/631)
and prove their corresponding selected-comparison naturality and exact body
result. The existing Cartesian Pi/Path decoder laws and #607's complete
variable-cap operation recovery supply parts of that route, not its final
comparison theorem. No De Morgan restriction is used as a replacement.

## Reuse and validation

The earlier [constructor audit](small-universe-constructor-gap-audit.md)
separates returned operations from canonical decoder operations. The present
analysis keeps that distinction. `NaturalUnivalenceLaws` obtains exact body
recomputation by classifying full parameter records; it is a useful method,
but it does not identify constructor comparison selections automatically.
`KunnethTransport.tensorTranspose_transport`, its conjugation law and
`inverse_transport` similarly retain chosen maps through endpoint adapters.
`KunnethIndexed.pushComp` derives its comparison from chosen adjunctions.
Their categorical map equalities provide cancellation methods, not a cubical
higher-body preservation theorem.

The original-model exact-body clients use identity, successor, twice and
`twiceSub ≫ successorSub` for both Sigma and Pi. The nonreflexive
`stateLine`/`stateField` examples state the complete body equations explicitly.
The `suppliedPath`/`suppliedDependentCode` examples use the actual varying
`Fin(n+1)` family and its initial pair/function terms. The function initial
term is adapted by the inverse endpoint Pi isomorphism. Existing
`successor_nonidentity`, `twice_nonidentity`, `varying_fibers`,
`carrierPath_nonreflexive` and `function_direction_sensitive` establish the
relevant properties of these inputs. Existing empty-domain and incompatible
path controls remain imported. Integrated build and exhaustive proof audit,
plus independent Standards and Spec review, are required for acceptance.

## Elaboration costs

The four generic Pi/Path composition proofs use default heartbeat, recursion
and kernel limits, with local `backward.isDefEq.respectTransparency false`
for categorical cancellation through the dependent adapters. Earlier
800,000-heartbeat Pi and 1,600,000-heartbeat Path elementwise proofs were
replaced, not retained. The updated native and Cartesian law files built in
6.7 and 7.6 seconds respectively.

`pairSection_reindex` retains a local 400,000-heartbeat budget after the default
200,000 timed out, including a local transparency trial. The other core and native example declarations added for #606 used defaults.
At that delivery the complete core built in 14 seconds and its native
examples in 10 seconds. The explicit Cartesian
Pi composition example retains a local 1,600,000-heartbeat budget: 200,000,
400,000 and 800,000 trials timed out; its complete example module passed in
83 seconds. These are measured bounded settings, not exact minima.

The original direct concrete two-step pair client reached the default
recursion limit. A separate trial at recursion depth 1024 and 800,000
heartbeats reached a 120-second process bound without a completed Lean result.
The shared two-step APIs retain all three transports and supply reusable
section premises. Passing at the default recursion depth is not an acceptance
criterion, and the bounded direct trial does not establish impossibility.

The #671 original-model additions use default heartbeat, recursion and kernel
limits. The generic selected-comparison naturality module checked in 19
seconds; the constructor module, including both fixed exact-body theorems,
checked in 14 seconds. The complete original-model recomputation example
module checked in 24 seconds, including its old clients and the new explicit
body equations and substitutions. These are focused module timings, excluding
time waiting for the shared compiler lock. The initial generic decoder proof
trials encountered dependent lawfulness-proof rewriting and transparency
errors. A small equality-elimination lemma handles those proof arguments;
no filling algorithm or theorem statement changed to resolve the errors.
These measurements support this implementation only, not a general authoring
productivity claim.

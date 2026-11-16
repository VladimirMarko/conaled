# Small-universe constructor gap audit

At `622219ab2fec5dad78924ca74cbb53f7edb10222`, the original-model
arbitrary-context Σ/Π/Path constructors and dependent transport formulas
requested by [#529](https://github.com/VladimirMarko/conaled/issues/529)
already exist. The issue's integration paragraph names the older small-context
modules but misses the larger-context implementation and its later clients.
The useful next action is to reconcile the issue with that implementation,
not split its already delivered contracts into implementation children.

This is a source and statement audit, with no new Lean claims or build replay.
The [original constructor report](large-context-constructors.md) records the
implementation contract; the
[originator review](https://github.com/VladimirMarko/conaled/issues/529#issuecomment-6890393457)
accepted that contract, including its explicit distinction between returned
constructor fillers and the universal decoder's filler. The source links below
identify the declarations inspected. Proposed stronger laws below are unproved
obligations, not findings against that accepted scope.

## Universe and context scope

Write `Uᵤ = smallFamilyCodes.{u}`. In the original model,
`Context.{u} = Cubeᵒᵖ ⥤ Type u` and `Family Γ = Γ.Elements ⥤ Type u`.
`Uᵤ` itself is a `Context.{u+1}`. This same-level `Family` interface explains
the explicit lifts; it does not imply that every large context is small.
See [Presheaf](../../SquareKit/Internal/Cubical/Presheaf.lean) and
[SmallFamilyCodes](../../SquareKit/Internal/Cubical/SmallFamilyCodes.lean).

The two constructor entry points have different quantifiers:

| Interface | Inputs and output |
| --- | --- |
| Original `sigmaCode` / `piCode` | `Γ : Context.{u}`, `a : raisedContext Γ ⟶ Uᵤ`, `b : raisedContext (total (Presheaf.decode a)) ⟶ Uᵤ`; output on `raisedContext Γ` |
| `LargeConstructors.sigma` / `pi` | Arbitrary `Ξ : Context.{u+1}`, `a : Ξ ⟶ Uᵤ`, `b : total (SmallUniverse.liftedDecode a) ⟶ Uᵤ`; output on the same `Ξ` into the same `Uᵤ` |
| `LargeConstructors.path` | Arbitrary `Ξ : Context.{u+1}`, `b : total (interval Ξ) ⟶ Uᵤ`, with terms at its two decoded endpoints; output on `Ξ` into `Uᵤ` |

These are the signatures in
[SmallFamilyConstructors](../../SquareKit/Internal/Cubical/SmallFamilyConstructors.lean)
and [LargeFamilyConstructors](../../SquareKit/Internal/Cubical/LargeFamilyConstructors.lean).
Instantiating the old constructors at `u+1` would instead target `Uᵤ₊₁` over
raised contexts at the next level. That is not the fixed-small-universe result.

`Presheaf.decode` decodes on a small context after `raisedElements`.
`SmallUniverse.decode` in
[UniverseFilling](../../SquareKit/Internal/Cubical/UniverseFilling.lean)
takes any `a : Ξ ⟶ Uᵤ` and has `Type u` fibers on `Ξ.Elements`;
`liftedDecode a` raises those fibers to fit `Family Ξ`.
[UniverseDecode](../../SquareKit/Internal/Cubical/UniverseDecode.lean)
already constructs `NativeDecode.filling`, its lawfulness, and exact
`filling_reindex` for arbitrary larger contexts. A missing large-context El
filler is therefore not the constructor problem.

## Delivered original-model constructions

[LargeFamilyClassification](../../SquareKit/Internal/Cubical/LargeFamilyClassification.lean)
provides the reusable admission interface `SmallPresentation.Data`: a
`Type u` representative and an equivalence to each native fiber, plus a supplied
lawful native filler. Its restriction maps are conjugated through those
equivalences. `chartFamily`, `chartIso`, `localFamily`, and `local_reindex`
pull this data onto small represented charts. `Data.code` assembles an actual
natural transformation `Ξ ⟶ Uᵤ`; `decodeIso` and `nativeIso` construct its
decoder comparisons. Callers do not supply the requested output code.

The public constructors derive the required presentations. Σ uses small
dependent sums. Π uses `FunctionValues` and `functionValues_injective`:
a Kripke function is determined by cube restrictions and small arguments,
even though `Ξ.Elements` is large. Only after proving that injection does
`Data.pi` use `Shrink`. Path uses a subtype of the small function space.
Thus the implementation proves closure for these inputs without resizing.
Its native fillers are the same `sigmaFilling`, `piFilling`, and `pathFilling`
used by the small constructors.

The raising adapters remain useful for existing small clients:
`Raising.totalIso` identifies raised comprehension with comprehension of
the raised family; `sigmaIso`, `pathIso`, and the term/path round trips retain
the explicit maps. `SmallUniverse.liftedDecode_raised`, `lowerChartMap`, and
`lowerChartEquivalence` connect decoder operations on small charts. They do
not assert a small presentation of an arbitrary context.
See [UniverseRaising](../../SquareKit/Internal/Cubical/UniverseRaising.lean).

### Exact operations and comparison strengths

`LargeConstructors.Result C` returns a code, `liftedDecode code ≅ C`, and
a lawful filler on that decoder. `construct` obtains this returned filler by
transporting the native constructor filler through the inverse decoder
isomorphism. `construct_filling` recovers that entire operation after transport
back. It does not identify it with `NativeDecode.filling Result.code`.

This distinction is already used by a structured consumer:
[ChartFamily](../../SquareKit/Internal/Cubical/ChartFamily.lean)
builds finite-label Σ/Σ/Path families through `LargeConstructors.construct`.
Its `path_selected`, `inner_selected`, and `outer_selected` preserve the named
returned operations. The alternative `encodedInner` uses stock nested code
constructors; `encodedInner_selected` explicitly retains the universal
decoder's filler for the inner code. Neither route silently identifies the
two choices. The [chart-family report](cubical-chart-family.md) explains the
client interface and its exact contracts.

| Law | Existing scope |
| --- | --- |
| Small `sigmaCode_reindex`, `piCode_reindex`, `pathCode_reindex` | Decoded-family isomorphisms over `Γ, Δ : Context.{u}`; dependent display substitutions retained |
| Small selected operations | `LocalFamily.sigma_reindex` is equality; Π and Path have explicit filler-preservation equations through their reindexing maps |
| Large `sigmaSubstitution`, `piSubstitution`, `pathSubstitution` | Decoded-family isomorphisms with independently rebuilt constructors for every `σ : Ω ⟶ Ξ`, where both contexts have level `u+1` |
| Large `*_Substitution_filling` | Equality of complete returned filling records after transport through those isomorphisms |
| `sigmaSubstitution_comp` | Equality between the direct composite comparison and the composite of successive comparisons |
| `Result.transportComparison_body_reindex` | Exact body reindexing of the comparison for a restricted `Result` and restricted supplied section |

Sources: [SmallFamilySubstitution](../../SquareKit/Internal/Cubical/SmallFamilySubstitution.lean),
[LargeFamilySubstitution](../../SquareKit/Internal/Cubical/LargeFamilySubstitution.lean),
and [ConstructorTransport](../../SquareKit/Internal/Cubical/ConstructorTransport.lean).
The large substitution comparisons are not equalities of code maps.
The last row does not state recomputation naturality of `pairAlongPath` or
`functionAlongPath` with independently rebuilt constructor results.

## Dependent transport formulas and their clients

[ConstructorTransport](../../SquareKit/Internal/Cubical/ConstructorTransport.lean)
already supplies both formulas. Given arbitrary `p : Term (paths a₀ a₁)`,
`inputLine p` is its actual code-valued body, with `inputLine_zero/one`
recovering the endpoints. A second code `b` may vary over the whole
comprehension of its decoded line. The input is an initial pair or function,
not a pre-assumed comparison or whole section.

For a pair, `pairFirst` fills its first component using the input universal
decoder's chosen filler. `pairSecond` fills the dependent component over the
display formed from that exact first section. `pairSection` pairs the results.
`pairAlongPath` compares universal transport in the constructed Σ code to
the final pair, by a native path, with the inverse decoder maps at both
endpoints.

For a function, `functionSection` uses `FunctionComposition.comp`: extend
the argument backwards, apply the initial function there, and compose its
dependent result forwards. It retains the De Morgan scaling and the added
initial face. `functionSection_selected` identifies this with the existing
selected Π filler; `functionSection_zero` recovers the initial function.
`functionAlongPath` compares its final section to actual universal transport
in the constructed Π code, again by a native path with endpoint decoder maps.

The connection is `Result.transportFromSection`, using
`NativeTransportComposition.sectionComparison` from
[DependentTransportComposition](../../SquareKit/Internal/Cubical/DependentTransportComposition.lean).
`Result.codePath_transport` identifies the path's map with
`IntervalTransport.map (NativeDecode.filling R.code)`. These results therefore
compare the actual universal transport to the constructor algorithm without
assuming equality of independently selected fillers.

[#528's report](compositional-univalence.md) and
[NaturalUnivalenceLaws](../../SquareKit/Internal/Cubical/NaturalUnivalenceLaws.lean)
remain the sources for dependent concatenation/reversal/identity and chosen ua
comparison laws. [UnivalenceLawParameters](../../SquareKit/Internal/Cubical/UnivalenceLawParameters.lean)
classifies complete equivalence records. Those results support the constructor
clients; by themselves they do not prove constructor closure.

| Required evidence | Retained source |
| --- | --- |
| Generic code inputs in a larger context; dependent `Fin(n+1)` fibers proved inequivalent | `genericSum`, `genericProduct`, `varying_fibers` in [CubicalLargeConstructors](../../Examples/CubicalLargeConstructors.lean) |
| Two nonidentity substitutions and their composite | `successor_nonidentity`, `twice_nonidentity`; Σ/Π/Path rebuild comparisons; observable `Fin 4`, `Fin 5`, `Fin 6` count fibers in the same module |
| Initial pair and function connected to public formulas | `checkedPairTransport`, `checkedFunctionTransport` in the same module; their supplied path is reflexive |
| Nonreflexive specializations of both formulas | `pairComparison`, `functionComparison`, `carrierPath_nonreflexive`, `field_genuinely_dependent` in [CubicalConstructorState](../../Examples/CubicalConstructorState.lean) |
| Independently observed dependent outputs and function direction | `pairOutput_observation`, `functionOutput_observation`, `function_direction_sensitive`; target argument 4 reads source 3, distinguished from unchanged 4 and forward 5, in that module |
| Complete package regression | `initialPackage_eq`, `finalPackage_eq` in [CubicalStatePackageUa](../../Examples/CubicalStatePackageUa.lean), including invariant proof fields |
| Empty domain and compatible/incompatible Path controls | `empty_sum_rejected`, `emptyFunction_unique`, `incompatible_endpoints_rejected`, `reflexivePathSection` in `CubicalLargeConstructors` |
| Zero labels, empty chart domain, and incompatible endpoints with nonzero labels | `zero_labels`, `zero_charts`, `empty_domain`, `incompatible_endpoints`, alongside `positive`, in [CubicalChartFamily](../../Examples/CubicalChartFamily.lean) |

The later nonreflexive client directly addresses the originator review's
nonblocking next-client observation. The whole-package client remains a
separate regression; importing it alone would not have established use of
the newer pair/function APIs.
`CubicalLargeConstructors`, `CubicalConstructorState`, and `CubicalChartFamily`
are imported by [SquareApplications](../../SquareApplications.lean), so these
are retained library clients rather than detached scratch examples.

## What the Cartesian implementation contributes

The Cartesian modules deliver dependent family operations and fillers over
arbitrary contexts at a fixed level. Their contextual classifier has
`LocalFamily.decodeCode_record`, `code_decode`, and `localFamilyEquiv`, retaining
the entire chosen local filling operation. This is not a new guarantee missing
from the original model: its corresponding `LocalFamily.decoded_code` and
`code_decoded` live in
[SmallFamilyGlue](../../SquareKit/Internal/Cubical/SmallFamilyGlue.lean), beyond
the older classifier file. Both contextual classifier interfaces still take
`Γ : Context.{u}` and code on `raisedContext Γ`.
See [CartesianSmallFamilyClassification](../../SquareKit/Internal/Cubical/CartesianSmallFamilyClassification.lean).

| Concrete difference | Consequence for reuse |
| --- | --- |
| Original `Filling` takes a `Cofibration` and a cap at false; Cartesian `Filling` takes an arbitrary `Subcontext` and a variable interval section `r` as cap | The filling records and their quantified law premises cannot be substituted for each other |
| Original Π filling extends composition using De Morgan scaling; Cartesian Π filling constructs an argument from its variable target dimension | A shared function-transport algorithm would need an explicit common interval/box contract and checked recovery of both selections |
| Cartesian classifier recovers selected records, with a different cube category and box data | Similar generic-evaluation proofs do not establish a model bridge |
| Cartesian native univalence acts on its own codes and universal family | `CartesianUnivalenceCompletion.univalence` does not imply original-model code closure or its constructor transport equations |

Sources: [Filling](../../SquareKit/Internal/Cubical/Filling.lean),
[CartesianFilling](../../SquareKit/Internal/Cubical/CartesianFilling.lean),
[FunctionFilling](../../SquareKit/Internal/Cubical/FunctionFilling.lean),
[CartesianPiFilling](../../SquareKit/Internal/Cubical/CartesianPiFilling.lean),
[CartesianDependentFamilies](../../SquareKit/Internal/Cubical/CartesianDependentFamilies.lean),
[CartesianDependentFilling](../../SquareKit/Internal/Cubical/CartesianDependentFilling.lean),
[CartesianPathFilling](../../SquareKit/Internal/Cubical/CartesianPathFilling.lean),
and [CartesianUnivalenceCompletion](../../SquareKit/Internal/Cubical/CartesianUnivalenceCompletion.lean).

The cube categories themselves are defined in
[Dimensions](../../SquareKit/Internal/Cubical/Dimensions.lean) and
[CartesianDimensions](../../SquareKit/Internal/Cubical/CartesianDimensions.lean).

The demonstrated useful shared interface is already within the original model:
`SmallPresentation.Data` plus a lawful filler feeds `LargeConstructors.construct`.
Both generic constructors and finite-label chart families use it, so callers
avoid repeating represented-chart assembly. Keep the model-specific fillers
and concrete clients. A common original/Cartesian abstraction should be assessed
for mathematical generality, reusable laws and future capabilities against its
adapter and recovery costs. Similar proofs alone do not establish those benefits,
and extraction is not needed to discharge #529.

A Cartesian counterpart of `SmallPresentation.Data` and the fixed-small-universe
large-context constructor API would be a separate extension. The inspected
Cartesian family fillers and raised-context classifier supply ingredients,
but do not themselves expose that contract. The original represented-function
smallness argument is a concrete proof design to assess for that extension;
its Cartesian specialization would still need checked chart assembly, decoder,
selected-operation and substitution laws. This would extend Cartesian capability
rather than complete an original-model obligation. If prioritized, coordinate
that separate scope under #289/#235 instead of making it a child of #529.

## Disposition and possible stronger contracts

Keep #529 coherent and reconcile its open status with the delivered original
implementation and later client evidence. There is no independently missing
constructor-admission or transport contract here that warrants a child issue.

Several stronger statements remain distinct from the delivered contract:

- Equality of the returned constructor filler with `NativeDecode.filling` of
  its code. A consumer demanding this would need a theorem preserving the
  complete chosen operation, not only an underlying-family isomorphism.
- Direct laws for recomputation of the pair/function comparison bodies after
  independent reconstruction, and Π/Path counterparts of the named Σ
  composite-comparison law. Their absence from the inspected interface is not
  failure of the existing arbitrary-substitution laws.
- A common original/Cartesian construction or a general bridge between the
  models. It would require specifying and proving how cube maps, cap choices,
  faces, selected fillers, and dependent comparisons are preserved.

These are proposed, unproved extensions. Assess their mathematical value, reuse
and implementation cost separately; they are not missing #529 obligations or
prerequisites for reconciling its status. For selected-operation transport work,
the [preserved #554 helper
source](https://github.com/VladimirMarko/conaled/issues/529#issuecomment-6893323711)
offers `piFilling_transport_second` and `contrFilling_reindex` as reuse leads.
They remain development evidence rather than integrated API at this revision,
so adopting them requires porting and validation.

The achieved closure is fixed-small-universe Σ/Π/Path admission over arbitrary
larger contexts with the explicit comparisons above. It establishes no
cumulative hierarchy, resizing, arbitrary HIT closure, source judgmental
conversion, executable algorithm, or cost bound. #422's source obligations
and #289/#235's broader coherence work remain separate.

# Cubical Glue and univalence construction

The #420 implementation constructs lawful Glue and universe filling, universal
decoding, `ua`, its transport comparison, the full native univalence theorem,
and the required transport consumers.
The checked components retain selected filling operations and chosen native
fiber contractions under substitution. The final assembly in
`NativeUnivalenceInverse.lean` and `NativeUnivalence.lean` passes focused Lean
checks, including both inverse homotopies for the same constructed `ua` map.
This document does not yet record final guarded build, exhaustive proof audit,
or independent Standards/Spec acceptance.

The construction extends #419's small-family classifier. Its mathematical
reference is [CCHM, arXiv:1611.02108v1](https://arxiv.org/html/1611.02108v1).
The separate [source-rule ledger](cubical-glue-source-rule-ledger.md) records
which semantic equations support the pinned Agda rules and which source
conversions remain with #422. Semantic construction, source admission, and
execution are separate claims.

## Native equivalences and extension

`HomotopyEquivalences.lean` defines homotopy fibers using native dependent sums
and cubical paths. Contractibility includes a chosen center and a path from
that center to the generic element. `HomotopyEquivalence` supplies this
contraction over the generic target, retaining its dependence on context and
target. `ofIso` constructs the native fiber contraction for a supplied natural
isomorphism. The Boolean-to-Unit rejection client refutes the same contract by
observing two fiber elements through native discrete-path rigidity.

`EquivalenceExtension.lean` derives extension of partial fiber data from the
contraction and a lawful filler. `homotopyFiberFilling` constructs the required
filler from the domain and codomain sum/path providers. Boundary recovery
retains both the selected source point and its comparison path. Source-input
and target-context substitution preserve the chosen extension, including its
supplied equivalence and fillers.

`UniverseFilling.lean` constructs `IntervalTransport.equivalence` for the actual
transport map of a lawful interval-family filling. It extends partial fibers
by filling a comparison square, then derives the chosen center and contraction
from contextual extension. `IntervalTransport.equivalenceOf_reindex` preserves
the whole chosen witness under substitution. No constant-transport regularity
axiom is used.

## Glue, selected fillers, and codes

`Glue.lean` constructs the face/ambient compatible carrier, introduction,
elimination, and compatible-presentation eta. `GlueSubstitution.reindexIso`
preserves the complete compatible data under arbitrary substitution.

`GlueFillingSubstitution.lean` constructs the lawful whole Glue filler. Its
preliminary operation fills the ambient family, extends a fiber over the face,
and corrects the ambient values along that path. The selected-face repair uses
the supplied face filler. `filling_full` recovers that entire operation after
restriction, for every context, line, face, and open box. `filling_input_reindex`
retains the selected operation under source substitution.

`SmallFamilyGlue.lean` normalizes the off-face carrier on represented cubes.
The resulting families and selected fillers satisfy strict semantic
substitution and full-face equalities. `Glue.code_full` recovers the original
supplied partial code; `Glue.code_substitution` preserves the complete supplied
codes. `LocalFamily.decoded_code` and `LocalFamily.code_decoded` recover the
original local family and contextual code map, including selected filling.
These are proved semantic equalities, not claims about an imported language's
judgmental conversion.

`GlueEquivalence.lean` constructs `Glue.unglueEquivalence`, with native contractible fibers for
the elimination map. Its proof uses the supplied face equivalence and lawful
face/ambient fillers. The Boolean-flip client checks the resulting center and
its path to the target.

## Universe filling and universal decoding

`CodeSystem.glue` and `CodeSystem.Maps.glue` assemble compatible codes and maps
on unions of faces. `CodeSystem.Box.partialCode` derives cap/tube compatibility
from the open-box boundary equation. A constant Boolean box exercises a
nonempty overlap; a Boolean cap with an incompatible Unit tube is rejected.
A partial Boolean/Unit endpoint boundary alone is not a universe path.

`UniverseComposition.lean` contracts the whole cap/tube face along an interval
connection. Actual backward transport along that line supplies the equivalence
used by Glue. `Box.fillCode` recovers the original cap and tube codes exactly
and commutes with substitution. The construction does not identify transport
along an arbitrary constant line with the identity.

`UniverseKan.lean` reads a universe open box on small represented charts,
applies this filler, and assembles the result. `SmallUniverse.filling_lawful`
proves cap/tube recovery and uniform substitution for the universe family.
`UniverseDecode.lean` constructs the universal decoding family over larger
contexts. `NativeDecode.filling_lawful` and `filling_reindex` retain the chosen
fillings supplied by the small charts.

Codes live at level `u+1`, while their small decoded fibers live at level `u`.
The native universal decoder raises those fibers explicitly with `ULift`.
`UniverseRaising.lean` supplies raising/lowering adapters for families, terms,
paths, sums, and fibers. `lowerChartEquivalence` lowers a genuine equivalence
on each small chart; `UniverseRaisingNaturality.lean` preserves the complete
lowered witness under substitution. No resizing axiom is assumed.

## Constructed ua and comparison

`Univalence.lean` uses disjoint endpoint equivalences to construct `uaCode`.
Its endpoint equalities recover the original codes and their selected fillers.
`UnivalenceSubstitution.lean` preserves the complete code under substitution;
`GlueEliminationSubstitution.lean` preserves its actual unglue map.
`UniverseCodePaths.lean` converts exact code lines into native universe paths.

`NativeUnivalenceUa.lean` assembles this construction over arbitrary contexts
at the larger universe level. Its `ua` has exact endpoints, and `equivToPath`
is a native map from the internal equivalence family to the native path family.
The chart coherence required by this assembly is proved for the constructed
`ua`, rather than left as an input hypothesis.

`UniversePathEquivalence.lean` constructs `pathToMap` by the actual universal
El filling and derives `pathToEquivalence`. `NativeUnivalenceMap.lean` packages these as the native map `pathToEquiv`
into internal equivalences. In `NativeUnivalenceElimination.lean`,
`uaComparison` uses the actual unglue line to give
a native path from the supplied map's output to the transported input.
`NativeUnivalenceComparison.lean` lifts this to `uaEquivalenceComparison`, a
path between the complete selected internal equivalences.

`EquivalenceFamilies.lean` constructs native contractibility, equivalence-witness,
and equivalence families with derived lawful fillers. Their section bridges
preserve maps, fiber centers, and contractions. `EquivalencePaths.ofHomotopy`
turns a native map homotopy into a path between specified equivalence witnesses;
its endpoint correction uses the native proposition construction for the
witness family, not host proof irrelevance on contraction records.

`EquivalenceWitnessSubstitution.lean` and `EquivalenceFamilySubstitution.lean`
prove full selected-data substitution laws. `EquivalenceFamilyReindex.lean`
constructs a native family isomorphism between substitution of the internal
equivalence family and the equivalence family of substituted carriers. Its
section law works after arbitrary further substitution and recovers the exact
supplied map and witness in both directions.

## Native univalence theorem

The following declarations pass focused Lean checks. They discharge the inverse
homotopy and total-contraction premises of the intermediate constructions; the
final theorem assumes only the two codes in the admitted universe. Integrated
acceptance remains subject to the guarded build, exhaustive audit, and review.

| Declaration | Contract of the final assembly |
| --- | --- |
| `rightInverseAt`, `rightInverseHomotopy` | The constructed `equivToPath` is a right inverse of `pathToEquiv` through a native path retaining the full chosen equivalence, in every substituted context. |
| `equivalenceTotal` | The total family of equivalences from a fixed code is contractible, using the constructed right-inverse homotopy. |
| `movingUnivalence` | The actual path-to-equivalence map has native contractible fibers while the target code varies. |
| `univalence` | For arbitrary codes `a` and `b` over a context at level `u+1`, `HomotopyEquivalence (pathToEquiv a b)` holds. |
| `leftInverseHomotopy` | The same constructed `equivToPath` is also a left inverse through a native path. |

The checked prerequisites are `NativePathSingleton.contractible`, native
concatenation and homotopy retraction in `HomotopyRetracts.lean`, the total
homotopy construction in `FiberwiseHomotopyRetracts.lean`, and
`HomotopyEquivalence.ofContractibleTotals`. The latter constructs actual fiber
contractions from contractible totals and lawful fillings.
`EquivalenceIsoTransport.lean` transports an equivalence through specified
native source/target isomorphisms. `NativeUnivalenceMapNaturality.pathToEquiv_conjugate_reindex` identifies the
fixed-target transported map with `pathToEquiv a b` itself, retaining the full
selected equivalence data.

This route uses native homotopies and exact chosen-data substitution. It does
not require chosen transport along a constant family to be literally identity.
The reverse-map beta laws and fixed-target map comparison are proved inputs
to the assembly. No inverse homotopy, map comparison, or fiber contraction
remains as a supplied premise of `univalence`.

## Checked transport consumers

`Examples/CubicalUnivalenceTransport.lean` observes actual decoded `ua`
transport: Boolean transposition sends true to false and false to true;
integer successor sends 3 to 4, and its inverse sends 3 to 2. Native
discrete-path rigidity converts the comparison paths to these observations.
The universal-decoder clients also exercise the larger-context transport.

`Examples/CubicalStatePackageFamily.lean` constructs the dependent package
family from native sums/products and derives its lawful filler. The package
contains an initial state, transition, invariant, initial-validity proof, and
preservation proof. `Examples/CubicalStatePackageUa.lean` fills that whole
package along the actual successor carrier line. `initialPackage_eq` recovers
the complete even package; `finalPackage_eq` recovers the conjugate odd
package, including proof fields. Its initial state is 1, its transition adds
2, and its invariant is odd parity. A separate equivalence of host package
types is not substituted for this filling.

`Examples/CubicalNativeUnivalence.lean` exercises the full theorem for Boolean
and integer codes and after adjoining an interval parameter. Its
`recoveredBooleanLoop_path` is a native path from the Glue loop recovered from
the actual selected transport equivalence back to the original Boolean
transposition loop. `booleanEquivalence_roundtrip` retains the whole chosen
internal equivalence witness.

The equivalence-family substitution and reindex clients retain the selected
witness of actual Boolean universal transport through two interval parameters
and through the native family isomorphism. Malformed-face and constant
Boolean-to-Unit controls remain in `Examples/CubicalGlue.lean`. These are
semantic results; no execution or cost bound is claimed.

## Source admission, history, and acceptance

The pinned source experiment uses Agda 2.8.0.2 and Cubical v0.9 commit
`b150186d2544e7efeddd31e5d14a8b9ecbb100f7`. The
[source-rule ledger](cubical-glue-source-rule-ledger.md) retains the exact
boundary: the optimized empty-face `equivProof` computation and the relevant
split `transp`/`hcomp` reduction branches still require source-judgment mapping
where the unchanged #422 cover uses them. #421 owns the circle construction.
No evaluator simulation, canonicity, or all-level Agda interpretation follows
from the native univalence construction.

Earlier stopping points remain in the
[checkpoint document at b6efed37](https://github.com/VladimirMarko/conaled/blob/b6efed37aba9d92e9c408c3e4c6d6dfaa3e7d94b/docs/research/cubical-glue-univalence.md)
and the [#420 tracker](https://github.com/VladimirMarko/conaled/issues/420).
Their unfinished-work descriptions record those checkpoints, not current
limitations of the checked components above.

Focused checks and targeted axiom inspection cover the described checked
components. Inspected dependencies are `propext`, `Classical.choice`, and
`Quot.sound`. Two private inverse-hom coherence proofs in
`UnivalenceSubstitution.lean` use a local `maxHeartbeats 400000`; the failed
default-limit and scheduling-only trials remain in the task evidence.
This changes no mathematical premise. Guarded full build, exhaustive audit,
and independent Standards/Spec review remain required before #420 acceptance.

# Univalence observations across settings

Issue #532 compares native cubical transport with ordinary host bijections and
proof-bearing state packages. The bounded route preserves the transport action,
composition and inverse observations, and the complete admitted discrete
package. It does not interpret the whole native universe or reconstruct every
selected higher witness in the target. A separate obstruction rejects any route
that identifies the Boolean identity and negation loops while claiming to
preserve their action.

The starting source is `68604a4a8f13d8cef2b2093ca590a70aca74fa68`, including
#528's compositional univalence and #530/#531's package and loop results. The
[three-perspective design challenge](design-challenges/2026-11-15/univalence-preservation/synthesis.md)
compares direct laws, a small interface and a broader semantic model morphism.
The implementation follows its direct-law recommendation. No foundation,
production evidence interface or Wasm backend is adopted.

## Source and target

The source consists of closed native paths between the constant universe codes
for host types `S` and `T`. These paths contain native transport data; they are
not Lean equality proofs between `S` and `T`. The target arrow is an ordinary
`S ≃ T`. Target arrow equality is host equality, obtained from native comparisons
only through the declared discrete observation.

[The implementation](../../Examples/CubicalInterpretationObservations.lean)
constructs `pathBijection` by lowering the actual `pathToMap`, conjugating with
the constant decoder isomorphisms, and applying `DiscreteEquivalences.closedEquiv`
to its actual contractible-fiber witness. Its inverse therefore comes from the
selected native fiber center. This is a change from native paths to host
mathematical arrows, rather than substitution within one context or a mere
renaming of carriers. It remains an observation comparison of a named fragment,
not an all-context interpretation of cubical type theory.

`pathBijection_apply` identifies each target output with the decoded native
transport of that input. `bijection_map` reconstructs the entire native carrier
map in this constant-code fragment. `transport_input` connects its image to the
native input constructor. `pathBijection_loop` identifies the endomorphism
specialization with #531's existing permutation observer, preserving its loop
classification and separation results.

## Composition and selected data

`pathBijection_concat` covers arbitrary closed composable paths with potentially
different endpoint types. It observes the actual native concatenation filler,
using `concatTransportComparison`; it is not limited to ua representatives.
`pathBijection_reverse` observes actual reversal using `reverseTransportLeft`.
No strict regularity of a constant filler is assumed.

`pathBijection_comparison` maps an actual native two-path to equality of target
bijections. `selected_identity`, `selected_composition` and `selected_inverse`
apply this result to the public comparisons in `NaturalUnivalenceLaws`. The
composition input retains the original `f`, `E`, `g`, `D` and the selected
`compositeEquivalence`; the inverse input names the actual `inverseMap` and
`inverseEquivalence`. No replacement of these records by independently chosen
isomorphism witnesses is needed.

The conclusion is equality of observed arrows. It does not identify the source
homotopy bodies, recover their whole contraction records, or preserve the full
code-valued comparison square as target data. The existing native
`comparisonSquare_injective` and exact public body-reindexing laws remain
available without change. There is no new proof of noninjectivity of square
observation either; that would require a separating pair. The existing triple
diagram does not supply an inherited recomputation law or pentagon.

The retained finite calculation detects order: the swap of 0 and 1 followed by
the swap of 1 and 2 sends 0 to 2, while the reverse order sends 0 to 1.
`finite_order_observations` obtains both outputs through the general composition
and ua laws. Identity versus negation retains the distinct Boolean outputs.
These are mathematical observations, not execution or cost measurements.

## Whole packages and the lowering boundary

`ua_admittedCarrier` connects the bijection of the actual native ua path to
#530's `admittedCarrier`, using `Raising.lowerMap` and
`Raising.lowerEquivalence` on the supplied map and complete equivalence record.
The lowered data supplies the existing package construction over its exact
lowered ua line. This explicitly uses the established raising/lowering adapter;
it does not assert host equality between differently presented universe lines.

`package_observation` identifies the entire observed target package with
conjugation by that same `pathBijection`. `package_section_recovery` also
reconstructs the entire native filled section through `pullPackage`. The five
`StatePackage` fields are initial state, operation, invariant, initial validity
and invariant preservation. Thus an initial-state or cardinality comparison
alone cannot discharge the theorem.

`finite_package_observation` specializes the bridge to the existing `Fin 3`
machine and its distinct `Phase` presentation. The imported #530 controls retain
`wrong_rejected` and `wrong_path_rejected`: a bijection fixing the initial state
can still fail to intertwine the transition. The full package contract excludes
that map. Existing integer even/odd and nonreflexive dependent constructor
clients remain available under their original hypotheses.

The recovery theorem uses the documented constant presentation and PLift proof
fibers. It does not generalize to arbitrary higher proof fields, all varying
families, or unrestricted structure identity. Complete section recovery in this
fragment uses all generalized-point readouts, including dependent function
values; it is not a theorem that zero-dimensional observations determine every
native family.

## A checked obstruction to collapsed observations

`no_collapsing_action` considers any target `Q` and any erasure of closed Boolean
loops into it. If the erasure identifies the native identity and negation loops,
there is no target action reproducing `pathBijection p b` for every loop and
Boolean input. Identity at true yields true; negation at true yields false.
The action-factorization requirement is the failed hypothesis.

`no_subsingleton_action` specializes this to subsingleton targets, and
`no_host_equality_action` to host equality loops `a = a`. This rejects a claimed
transport-preserving interpretation through proof-irrelevant equality. It does
not assert that every erasure is impossible or that every set-valued target
loses the action. `permutation_action_exists` supplies a positive target whose
distinct bijections retain it. The rejection concerns the actual native
transport via `pathBijection_apply`, rather than two newly invented programs.

## Preservation inventory

| Component | Established by this route | Remaining boundary |
|---|---|---|
| Codes and El | Constant-code endpoints and actual decoder maps | No entire target universe/classifier or arbitrary El interpretation |
| Paths | Closed paths become bijections; native comparisons induce equality | No general target identity family or selected two-path recovery |
| Dependent constructors | Complete admitted state package and native section recovery | No arbitrary dependent Sigma/Pi or higher-proof preservation |
| Chosen fillers | Their actual carrier action and the specified package section | No interpretation of the complete Kan operations |
| Equivalences | Bijection and inverse selected from native contractible fibers | No reconstruction of the full native contraction record |
| ua | Exact supplied action, connected to the original package carrier | No host univalence or source-conversion theorem |
| Composite/inverse witnesses | Observations of the actual selected records and public comparisons | No target encoding of all homotopy/square bodies |
| Substitution | Existing native laws remain available | They do not establish a different semantic setting's full preservation |
| Execution | None claimed | Noncomputable semantic constructors are not evaluators |

## Reuse and further work

#446 supplies a useful method: primitive coherent comparisons derive whole
section and selected component laws. Its groupoid/J construction is not a
cubical universe interpretation. #405's connection-syntax obstruction likewise
does not prove semantic comparison between cubical theories impossible. The
#490/#492 evidence studies separate witness admission from artifacts; neither
supplies the missing native model map. The
[preservation inventory](preservation-contract-inventory.md) keeps those
contracts distinct.

Keep direct laws for this fragment. A small preservation interface needs a
second concrete route consuming the same obligations. A broad model morphism
could eventually derive ua and package preservation from primitive operations,
but this observation target does not provide all those operations. Requiring
the desired preservation theorem as a field would not construct it.

The residual task under #235 is to choose a genuinely different cubical or
higher setting with constructed identity and filling operations, then test
preservation of the complete selected equivalence record and comparison-square
body on these clients. A Cartesian fibrant presentation is a candidate, not an
adopted foundation. The task must distinguish direct restriction from fibrant
reconstruction and prove its own hypotheses. Exact, native-path and weaker
observational preservation remain separate possible contracts.

## Validation scope

New claims are checked through the public native transport, discrete equivalence
and package-recovery results. The retained cases cover mixed carriers,
arbitrary closed composition/reversal, actual chosen comparison witnesses,
noncommuting permutations, complete packages and a positive/negative target
action pair. The design assessments distinguish proposed proofs from checked
implementation. Candidate build/audit and independent Standards/Spec acceptance
are recorded by the implementation workflow; this report makes no timing,
normalization or author-productivity claim.

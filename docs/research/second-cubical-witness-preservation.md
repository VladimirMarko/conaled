# Selected witnesses in Cartesian cubical presheaves

Research for [#574](https://github.com/VladimirMarko/conaled/issues/574), at
local revision `fae1621cae2d44c788f65400392820d942dabccd`.

The bounded route restricts the existing De Morgan presheaves to
Cartesian cube substitutions. It constructs target paths and contractible
fibers from the actual source witnesses. It does not construct a new target
univalent universe or a chosen Cartesian Kan operation. The distinction is
between interpreting a selected completed construction and recomputing that
construction from a second model's independently supplied operations.

This report gives mathematical constructions and proofs for research review.
They are not new Lean declarations. Existing local Lean declarations supply
the source data and controls; a formal implementation of the comparison is
remaining work. The design challenge and independent research review assess
the stated hypotheses and conclusions, not kernel validation of these proofs.

## Sources and prior obligations

[CCHM v1, §§8.1–8.3](https://arxiv.org/html/1611.02108v1#S8.SS1)
supplies the De Morgan cube and dependent-presheaf definitions.
[Angiuli–Hou–Harper, CSL 2018, §§2–6](https://doi.org/10.4230/LIPIcs.CSL.2018.6)
separates Cartesian dimension syntax from its fibrant type operations. The
local [#405 report](cubical-judgment-compatibility.md) pins that PDF and
proves the scope of its failed connection translation. Neither paper is
cited as a theorem about this library's selected witnesses.

For an independent fibrant reconstruction, the author manuscript
[Syntax and Models of Cartesian Cubical Type Theory](https://www.cs.cmu.edu/~rwh/papers/uniform/uniform.pdf)
was inspected on 2026-11-16, SHA-256
`ea235cf09eae29d3859f31976bc43a939a6565410ff4117addb99d0602c213a3`.
Theorem 2 assumes a finite-product base, distinct interval endpoints, and
decidable cofibrations closed under interval equality, disjunction and interval
quantification; it constructs universes of diagonal-Kan families. Section 3.4
compares endpoint and diagonal Kan structures in the same De Morgan setting
with the extra cofibrations available. Its further universe comparison is a
proposal, not a theorem comparing the two presheaf categories used here.

The restriction and witness arguments below are this investigation's direct
derivations from the stated category definitions. They do not inherit a
cross-model theorem from those papers. The local comparison starts from
[#532's bounded observation route](univalence-interpretation-observations.md),
[#528's selected composition data](compositional-univalence.md),
[#530's package construction](cubical-structure-identity.md), #531's loop
controls, and [#554's selected inverse](selected-native-inverses.md).

## Fixed source and target

Write D for the local category `SquareKit.Cubical.Cube`. Objects are natural
dimensions. A map m→n is an n-tuple of De Morgan expressions on m variables,
modulo the equations in `Expr.Conv`. Substitution defines composition.
Write C for the category with the same objects whose map m→n is an n-tuple
from `{0,1,x₁,…,xₘ}`. Repeated variables, unused variables and permutations
are allowed. Substitution again defines composition. Both have products
given by addition of dimensions. The functor i:C→D includes these expressions,
is identity on objects, and preserves the selected products and endpoints.
Its identity and composition laws follow by substituting variables/constants.
Here n+1 means adjoining a fresh coordinate. The local
[CubeProducts.lean](../../SquareKit/Internal/Cubical/CubeProducts.lean) puts
it at index zero (`fresh`) and shifts the old coordinates (`drop`); all
pairings and comparisons use that same ordering on both sides.

The source setting is presheaves on D and their dependent families. The target
is presheaves on C, with dependent families and paths over its represented
interval I_C=y_C(1). These have different substitution maps and different
represented intervals. This is a change of semantic setting, not reindexing a
context inside the existing model or renaming a carrier.

Restriction R is precomposition with iᵒᵖ:

```
(RX)(n) = X(n)                 (RX)(f) = X(i f)
(Rt)(n) = t(n)                 R(g ∘ f) = Rg ∘ Rf.
```

For a dependent family A over Γ, precompose with the functor
`El(RΓ) → El(Γ)` taking `(n,x)` to `(n,x)` and a C-substitution to its
D-substitution. Denote this family RΓA. It has exactly the same fiber sets at
each `(n,x)`. Its restriction maps are the old maps on fewer substitutions.
Every source section is a target section with the same values; every source
family map remains natural. Thus restriction is faithful on these maps and
sections: equality of all target components is equality of all source
components. This does not make every target natural map a source natural map.

Comprehension and dependent sums are pointwise dependent pairs. Consequently
`R(Γ.A) ≅ RΓ.(RΓA)` and the dependent-sum comparison are the identity on pairs,
with restriction maps agreeing by their formulas. Projection, pairing, generic
element, family substitution, and section substitution commute with these
comparisons. This is the construction behind the local definitions in
[Presheaf.lean](../../SquareKit/Internal/Cubical/Presheaf.lean) and
[TypeFormers.lean](../../SquareKit/Internal/Cubical/TypeFormers.lean), applied
to the second base category; their existing context-substitution theorems alone
do not prove this change of base.

## The interval obstruction and the path comparison

Do not identify J=R(y_D(1)) with I_C. There is a natural inclusion I_C→J,
but no endpoint-preserving natural map J→I_C. Indeed, J(1) contains the
reversal expression `¬x`. Its restrictions at 0 and 1 are 1 and 0. Naturality
and preservation of the two endpoints would send it to an element of
I_C(1) with those same restrictions. The only elements of I_C(1) are 0, 1,
and x, whose endpoint pairs are respectively (0,0), (1,1), and (0,1).
None has endpoints (1,0). This proves the claimed obstruction.

This natural-transformation argument goes beyond #405's failed translation
of connection syntax. It still does not prohibit a comparison of fibrant
types, or even preservation of path families by this restriction. The latter
has a different proof. For any D-presheaf X, Yoneda and the selected products
give natural bijections

```
R(X^(y_D 1))(n) ≅ X(n+1) ≅ ((RX)^(y_C 1))(n).
```

The first evaluates a natural map from `y_D(n) × y_D(1)` at its generic
(n+1)-cube; the second uses the corresponding Cartesian generic cube.
Their inverse takes a cube u and sends a pair of substitutions `(f,r)` to
`X(⟨f,r⟩)(u)`. Reindexing n along f becomes reindexing n+1 along f×id on
both sides. Endpoint evaluation becomes reindexing along `id×0` or `id×1`.
These equalities prove naturality and both endpoint laws. No general
exponential-preservation theorem is assumed.

The dependent version is equally explicit. For A over Γ, x∈Γ(n), and
sections a,b of A, a homogeneous path at x is a cube

```
u ∈ A(n+1, Γ(π)(x)),
u|₀ = a(n,x),    u|₁ = b(n,x),
```

where π:n+1→n drops the fresh coordinate. Evaluation at the generic cube
and the inverse formula just given identify the source path fiber with the
target path fiber of RΓA. A dependent path over a varying source family B
on Γ×I_D is handled by first pulling RB back along
`RΓ×I_C → RΓ×J`; its generic value has the same formula with the final
fresh coordinate supplied to B. This pullback matters: the two interval contexts
are not equal. The comparisons commute with base substitution, endpoint
evaluation and mapping a path through a family map, as each operation on u
is the same projection, face or component map in C and D.

This supplies an isomorphism κ of the homogeneous path families actually used
below. Iterating the generic-cube calculation supplies κ² for two-paths and
code-valued squares, evaluated at n+2. The retained bodies include their
interiors, not just four endpoints. The local implementation of source paths
in [Paths.lean](../../SquareKit/Internal/Cubical/Paths.lean) packages these
coherent generalized evaluations as `PiElement`; the generic-cube argument
explains why its interval-specific comparison is invertible.

## Constructing target contractible fibers

The decisive source interfaces are
`HomotopyContractible.center`, `HomotopyContractible.contraction`, and
`HomotopyEquivalence.fibers` in
[HomotopyEquivalences.lean](../../SquareKit/Internal/Cubical/HomotopyEquivalences.lean).
Contractibility is a center section and a homogeneous contraction over the
total family. It is not a proposition asserting existence of unspecified
contractions. Equivalence is contractibility of the actual generic fiber,
a dependent sum of an input and a path from its image to the generic output.

For f:A→B, the Sigma and κ comparisons construct a natural isomorphism

```
θ_f : R(Fib_D(f)) ≅ Fib_C(Rf)
```

over the identified target context `R(Γ.B)`. At each generalized point it
sends `(a,p)` to `(a,κp)`. The inverse uses κ⁻¹. The endpoint equations make
the pair well typed; naturality follows from the two constituent comparisons.

Given the actual source record E, construct E_C as follows:

1. Its center is θ_f applied to R(E.center).
2. For a generic target fiber element z, use θ_f⁻¹(z) as the input to the
   restricted source contraction. Apply κ to that contraction and map its
   values through θ_f. Its endpoints are the selected target center and z.

These formulas construct a contraction for **every** target generic fiber
element, since θ_f is invertible. They do not merely store an uninterpreted
source record or postulate the intended equivalence theorem. No target Kan
operation is needed for this transport of an already supplied contraction.
Every map in the construction is natural, so the formulas define target
sections, not unrelated pointwise choices.

The chosen center and contraction can also be recovered: apply θ_f⁻¹ and
κ⁻¹ to the output data at every cube. Faithfulness of restriction on sections
then recovers the original record. This recovery concerns records in the
image; it does not extend arbitrary target records to D-naturality.

The selected inverse from #554 is the first projection of the exact center.
Its right homotopy is the center's path; its left homotopy is the contraction
at `(a,refl)` followed by the first projection. The formulas for R, θ and κ
commute with these operations, deriving preservation of the selected inverse
and both whole homotopies. See
[SelectedInverse.lean](../../SquareKit/Internal/Cubical/SelectedInverse.lean).
The extra `selectedInverseEquivalence` is constructed in the source using
chosen fillers. Applying the same fiber construction to that completed
record gives an equivalence of its target inverse. This does not prove that
an independently filled target construction chooses the same record.

## Frozen univalence and dependent-package data

Use the source universe U=`smallFamilyCodes` and its actual decoder El.
The target code presheaf is RU with decoder REl under the comprehension
comparison. Every supplied source code and decoding map has a target image.
We do not identify RU with a classifier of all Cartesian fibrant families,
nor construct ua for target equivalences that have no supplied source lift.

Freeze the following source data with their exact endpoints:

- a,b,c, f:A→B, g:B→C, and their full E,D equivalence records;
- `compositeEquivalence a b c f E g D`, rather than an unrelated equivalence
  for the same composite map;
- the universe-selected `inverseMap`, `inverseEquivalence`, `inverseLeft`
  and `inverseRight` from
  [CompositionalUnivalence.lean](../../SquareKit/Internal/Cubical/CompositionalUnivalence.lean);
- `NaturalUnivalenceLaws.composition` and its full
  `NativeUnivalence.comparisonSquare` body, together with the identity and
  inverse comparisons;
- separately, #554's center-selected inverse and its left/right paths. The
  two inverse recipes are not asserted equal to one another.

Apply κ to the ua and concatenation paths, θ to the selected composite and
inverse equivalences, and κ² to the selected public comparisons. The source
composition square's sides remain a and c. Its bottom is the image of
`ua(f≫g, compositeEquivalence …)` and its top the image of the selected
concatenation of `ua(f,E)` and `ua(g,D)`. These are complete target two-paths
in RU, with exactly the retained source choices. The boundary equations follow
from κ's face laws and the four source `comparisonSquare_*` theorems in
[NativeUniverseSquares.lean](../../SquareKit/Internal/Cubical/NativeUniverseSquares.lean).
Applying the inverse comparisons recovers the source two-path at fixed
endpoints; source `comparisonSquare_injective` then recovers the original
comparison. No pentagon or selected triple recomputation law follows.

The concrete square is `FiniteUniverseLoops.swapComposition`: its a,b,c
are the same `code (Fin 3)`, and f,g are `nativeMap swap01` and
`nativeMap swap12` with their actual `nativeEquivalence` records. Retain
that source `compositeEquivalence`, its contraction, and
`comparisonSquare swapComposition` under θ and κ². At a generalized point,
both routes around the body-preservation square evaluate the source comparison
at the base weakened by two drops and the two fresh coordinates. Its four
faces are the original source code, target code, composite ua and selected
concatenation. This instantiates the generic proof with the public chosen
square, not an arbitrary replacement path between the same endpoints.

The dependent client is the actual five-field `package A` and its
`filledPackage` section from
[CubicalStatePackageFamily.lean](../../Examples/CubicalStatePackageFamily.lean),
over the ua carrier line used by
[CubicalStatePackageUa.lean](../../Examples/CubicalStatePackageUa.lean).
Retain initial state, endomorphism, invariant, initial-validity witness and
invariant-preservation witness. The invariant proof family depends on the
selected state; it is not a constant bare carrier comparison.

There are two distinct package statements. The entire section of the
**restricted source package family** is retained pointwise, including its
PiElement data. To interpret it as a package assembled from target Sigma/Pi,
use the canonical dependent-product comparison
`R(Π_A B) → Π_(RA)(RB)`: evaluate a source generalized function on the
included Cartesian substitutions. This is natural and commutes with
application and abstraction by direct evaluation. Combine it with the Sigma
comparison recursively through the five fields. The result is an actual
target dependent package and the image of the selected filled section.
At each generalized point, its five readouts agree with the source readouts,
because each readout applies a function at the identity substitution.

No invertibility of this general Pi comparison is established. Therefore
whole restricted-source-section recovery is an exact claim; recovery of
all generalized source PiElement data from an arbitrary target package is
unsupported. This does not obstruct θ_f, which uses only Sigma and paths.

For the concrete Fin3/Phase instance, retain `machine`, `presentation`,
`machineTransported` and all five fields from
[CubicalFiniteStateIdentity.lean](../../Examples/CubicalFiniteStateIdentity.lean).
More precisely, put `f = (codeIso presentation).hom` and
`E = nativeEquivalence`, take `A = admittedLine f E` and
`e = admittedPresentation f E`, and freeze the actual section

```
s = filledPackage A e (machine.conjugate (admittedCarrier f E)).
```

This is `CubicalStructuredState.transported f E machine`, whose endpoint
readout defines `machineTransported`. Restrict this section and pull it back
along `I_C → R(I_D)` before applying the forward package comparison. Its
selected source filler is `(package A).toNative.filling`; no target filler
is substituted. The preservation square at every Cartesian generalized point
x and each of the five fields is

```
readOut_C(x, packageComparison(Rs)(x)) = readOut_D(x, s(x)),
```

where on the right x includes the interval through the specified map. For
initial state this is the first projection. For step and invariant it is
evaluation at `(id,a)` on both sides. For initial validity it is the same
PLift proof value. For preservation it is the same evaluation at `(id,a)`
followed by application to the invariant proof. These computations prove
the whole five-field square; they do not rely only on its numeric consequence.
The image still has next-state observation 1, is valid at ready and invalid
at failed. `wrongPresentation` still fails transition preservation even though
it preserves the initial state: that contradiction already occurs at a
closed readout. The target comparison cannot turn this failure into success.

## Composition and separating controls

Let O be the subcategory with the same cubes generated by endpoint insertion
and coordinate omission, without diagonals, reversal or connections. Its
inclusion into C gives a second restriction S. For every source family,
map, section and retained fiber record, restriction along O→C→D agrees with
restriction along O→D, component by component. For paths and square bodies
from the source image, evaluate successively at the generic added coordinates:
both routes return the same source u at n+1 or n+2. These are retained
parameterized bodies with their endpoints, not a claim that O's arbitrary
presheaves have Cartesian path-exponential semantics. This tests composition
of the selected restriction interpretation on actual witnesses without
postulating a higher coherence law.

For f,g, direct restriction also sends the actual composite map to
`Rg ∘ Rf`. Apply θ to its selected source compositeEquivalence and κ² to
its selected composition square. Their endpoints and bodies are the ones
just frozen; no replacement equivalence witness is chosen by the test.

The Boolean identity and negation loops remain distinct: κ is invertible
and their transported true observations are true and false. At Fin3, the
two noncommuting swaps still send 0 to 2 and 0 to 1 in opposite orders.
These values and the source loop separation are the checked controls in
[FiniteUniverseLoops.lean](../../Examples/FiniteUniverseLoops.lean) and
[CubicalInterpretationObservations.lean](../../Examples/CubicalInterpretationObservations.lean).
Restriction retains their selected paths and full comparisons as above;
the value checks supplement that witness argument rather than replace it.
The closed no-two-path controls also transfer. In both categories the zero
cube represents the terminal presheaf, so a closed section of a restricted
presheaf is determined by its zero-cube element. For the iterated path
families with these fixed closed endpoints, κ² identifies that element with
the corresponding source element. A putative closed target two-path would
therefore yield a source two-path, contradicting `booleanLoops_no_two_path`
or `compositeLoops_no_two_path`. This uses representability of the closed
context; faithfulness alone would not exclude new target sections over an
arbitrary context.

## Preservation inventory

| Component | Contract of this route | Boundary |
|---|---|---|
| Contexts, families, maps, sections | Exact component values and included restriction maps | No extension of arbitrary target maps |
| Comprehension and Sigma | Natural isomorphism, identity on dependent pairs | Presentation casts still explicit |
| Codes/El | Exact restricted codes and decoder | No target universe classification or general univalence |
| Native paths and two-paths | Natural isomorphism κ and κ²; recover full selected bodies | Not an interval isomorphism J≅I_C |
| General dependent Pi | Canonical comparison preserving selected application | No general inverse or reflection claim |
| Actual package | Exact restricted source section; five matching target-package readouts | Target-Pi reconstruction of all source data unsupported |
| Full equivalence fibers | θ and κ construct complete target centers and contractions | Only supplied source records, not arbitrary target ua |
| Selected inverse and homotopies | Exact after the specified comparisons | No equality of different source inverse recipes |
| Composite record and public square | Complete image of the actual selected data | No recomputation with independent target fillers |
| Chosen filling | Restricted selected filled sections and their faces | No filler for every Cartesian box |
| Composition | Equality of the two restriction routes on retained data | No pentagon or triple-choice recomputation |
| Execution | None | Mathematical semantics, not an evaluator |

## Architecture decision and construction work

The [three-perspective design challenge](design-challenges/2026-11-16/second-cubical-setting/synthesis.md)
supports direct route laws followed by a small derived interface. Its reports
and synthesis record the relative-interval and package corrections, the
closed-path reflection argument and the limits of independent target
recomputation. The construction needs a small number of primitive comparisons;
the selected fiber/inverse and square laws are derived consequences, not
interface inputs. A broader model morphism would add obligations unnecessary
for these selected clients. This decision adopts a research route, not an
unimplemented library interface.

Remaining construction has separate acceptance boundaries:

1. Formalize C, i, restriction, the dependent-family comparison, κ and θ;
   prove whole selected-record and square recovery on the frozen clients.
   Include the interval-map rejection and composition test. This would turn
the research proof into checked library capability.
2. Construct or transport an actual Cartesian chosen Kan structure for the
   selected decoded families, accounting for its cofibrations. Only then
   compare recomputation of composite/inverse witnesses. A chosen native
   comparison can suffice; equality of independently chosen fillers is not
   automatically required.
3. For a target univalence claim, construct the target classifier and a
   comparison of decoding and selected ua operations. State its domain of
   equivalences explicitly. Existing source univalence and the existence of
   a published Cartesian model do not discharge this step.

The broader residual owner is #235 in coordination with #36. #554 already
supplies the needed source inverse capability; it needs no duplicate issue.
#405's syntax obstruction remains valid but does not close these semantic
construction tasks. #446 supplies the method of deriving whole comparisons
from primitive coherent squares, not an imported cubical theorem. #528–#532
remain available with their original direct clients and stronger native
contracts. No production #489 interface is adopted here.

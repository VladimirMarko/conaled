# Second cubical setting: challenge brief

Assess the proposed bounded interpretation for [#574](https://github.com/VladimirMarko/conaled/issues/574).
Local source is `fae1621cae2d44c788f65400392820d942dabccd`. This brief is an
uncommitted research input, not an approved result. The issue version is
2026-11-15T11:16:12Z, including its comment about completed #554.

## Required capability

Move beyond #532's bijection observations to a genuinely different semantic
setting retaining selected contractible-fiber witnesses, inverse homotopies,
and the public code-valued comparison-square body. Freeze an actual dependent
package, Bool separation and Fin3 order. Derive a bounded comparison from
primitive operations; do not assume the final preservation theorem. A precise
separating obstruction is also an allowed result, with residual construction
work. No new kernel, universal framework or runtime evaluator is requested.

## Candidate construction to test

Let D be the existing formal De Morgan cube category. Let C have finite cubes
and substitutions whose coordinates are variables or 0/1, allowing repetition
and omission. The identity-on-objects inclusion i:C→D induces restriction
R: Set^(D op)→Set^(C op). This changes the base category, unlike context
substitution or carrier renaming. Categories and maps are explicit mathematical
constructions here; no new Lean implementation has yet been made.

For a source context Γ, restrict a family by precomposition with the functor
between categories of elements sending (n,x) to (n,x) and each Cartesian
substitution to its De Morgan image. Sections and maps keep their components.
Comprehension, dependent sums, substitution and their selected sections should
then agree pointwise. The target interval is I_C=y_C(1), not J=R(y_D(1)).

The proposed path comparison uses Yoneda and finite products:
R(X^(y_D 1))(n)=X(n+1)=(RX)^(y_C 1)(n).
Its dependent version fixes the base at Γ(projection)(x) and fixes endpoints;
check the precise naturality and endpoint maps. Iteration should retain square
bodies at n+2. This is not justified by assuming R preserves arbitrary powers
or dependent products.

Inspect the actual source record: HomotopyContractible is a center section and
a contraction path over the total family. HomotopyEquivalence supplies that
record for the generic Sigma/path fiber. Thus comprehension, Sigma and relative
path comparisons may suffice to construct a full target equivalence without
an arbitrary Pi isomorphism. SelectedInverse projects that exact center and
contraction. Map the already constructed composite/inverse equivalence and
public square through these comparisons. Distinguish this from recomputing
them with independently chosen target fillers.

Target codes would be R(smallFamilyCodes) with the restricted decoder. This is
not yet a classifier of all target fibrant families, nor a proof of target
univalence for arbitrary target equivalences. General Cartesian filling,
diagonal cofibrations and reconstruction of a univalent universe remain
separate questions. A source-selected filled section can still be restricted;
that alone is not a filler operation for arbitrary target boxes.

Two proposed controls need scrutiny. First, no endpoint-preserving natural
map J→I_C exists: the De Morgan reversal cube has endpoint values 1 then 0,
while I_C(1) contains only 0, 1 and the variable. This is stronger than a syntax
translation objection, but does not contradict the path-power comparison.
Second, full selected data must remain distinguishable without claiming
injectivity of an arbitrary dependent-product comparison.

## Sources and observations

Read the actual issue and these local sources at the pinned revision:

- `docs/research/cubical-judgment-compatibility.md` (#405): connection-syntax
  obstruction and explicitly open semantic comparison.
- `docs/research/univalence-interpretation-observations.md` (#532), including
  its preservation inventory and design challenge.
- `docs/research/compositional-univalence.md` (#528),
  `docs/research/cubical-structure-identity.md` (#530),
  `Examples/FiniteUniverseLoops.lean` (#531), and
  `docs/research/selected-native-inverses.md` (#554).
- `SquareKit/Internal/Cubical/{Dimensions,Presheaf,Interval,Paths,HomotopyEquivalences,SelectedInverse,NativeUniverseSquares,NaturalUnivalenceLaws}.lean`.
- `Examples/CubicalStatePackageFamily.lean`: five-field package, genuinely
  dependent invariant proofs and actual filledPackage section.
- `Examples/CubicalFiniteStateIdentity.lean`: Fin3/Phase machine and rejection
  of the wrong bijection despite matching initial state.
- #446: derive generated comparison from primitive coherent squares; its
  ordinary-groupoid J theorem is not a cubical model morphism.

External primary starting points: CCHM arXiv:1611.02108v1, §§8.1–8.3;
Angiuli–Hou–Harper CSL2018 doi:10.4230/LIPIcs.CSL.2018.6; and the Cartesian
cubical model manuscript at https://www.cs.cmu.edu/~rwh/papers/uniform/uniform.pdf.
Verify precise hypotheses before relying on them. A paper construction is not
a checked Lean implementation, and external model existence alone supplies
no chosen comparison with this library.

## Independent questions

1. **Contract and foundations:** Are the relative path and fiber comparisons
   valid? Do they construct the claimed full witnesses, or only retain opaque
   source records? Find a separating case for any overclaim.
2. **Implementation and use:** Freeze exact public consumers, including the
   package and selected square. Compare direct route laws with a small derived
   interface and broader model morphism. Which obligations fall on builders
   and which on callers? What can be implemented next without circular fields?
3. **Alternatives and generality:** Compare restriction with Cartesian fibrant
   reconstruction and other credible settings. Is strict recomputation needed,
   or would a specified native weak comparison suffice? Audit the interval
   obstruction without inferring impossibility of a semantic route.

These lenses target mathematical validity, practical use, and unnecessary
architectural assumptions. Each reviewer receives the same brief and works
independently, without other assessments or coordinator conclusions. Record
source evidence, hypotheses, untested claims and missing construction. Do not
edit repository files, create issues or launch another challenge. Return a
Markdown report in the assigned external task path. The coordinator preserves
the initial reports and synthesizes them only after all three are complete.
Research review does not replace the eventual Standards/Spec acceptance loop.

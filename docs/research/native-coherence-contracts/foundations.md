# Foundations assessment of the finite native coherence contract

This is the independent foundations perspective for #697, against source commit
`f0cac600a954fae4f340a9262ad732f6fbb30cc7`. The relevant Lean sources in the working
tree have no diff from that commit. I had no prior involvement in #687 and did
not read the other #697 perspective reports. Prior exposure consists of the
shared brief, issue text, repository guidance, the existing structure-identity
report and #687's retained attempt report. This report distinguishes inspected
declarations from proposed constructions; no new Lean proof or build was run.

Retain the supplied-witness interface and selected total correspondence. The
finite extension should derive associativity comparisons, units, and native
3-paths for triangle and pentagon boundaries. Do not require callers to supply
those final laws. The missing work is reusable path composition/whiskering and
truncation transport, rather than evidence that the requested laws require new
mathematical assumptions. Keep the original direct constructions available.

The strongest evidence is that `Equivalence.native` keeps the complete supplied
carrier equivalence, `explicitMap` is a native homotopy equivalence with both
recovery homotopies, and preservation over a set target is already a native
proposition. These are the ingredients needed to control whole paths without
replacing complete witnesses by host equality or by their forward maps.

## Source facts and the dimension boundary

Both [original coherence](../../../SquareKit/Internal/Cubical/NativeStructureCoherence.lean)
and [Cartesian coherence](../../../SquareKit/Internal/Cubical/CartesianNativeStructureCoherence.lean)
define `Equivalence` with a map, its entire `HomotopyEquivalence`, a point path,
and a path between the encoded endomorphism maps. `compWith` stores its supplied
composite witness verbatim; its point and step fields are constructed before
selecting any structure path. `Coded.path` applies `UaComparison.explicitMap`
to `e.native`. `Coded.carrier_path` identifies its carrier projection with the
selected `ua` for exactly `e.map` and `e.witness`.

Write `Path X x y` for the family `homogeneousPath X x y`; every displayed
inhabitant below is a `Term` of that family. With

```
O = objects description Γ
Xi = objectOf description ai si.fields
Pij = Path O Xi Xj
```

`Coded.composition` has type `Path P02 p02 (p01 ⋆ p12)`. It is a native
2-path in `O`, not an equality of equivalence records and not a native 3-path.
Here `⋆` is `homogeneousConcat` using `objectsFilling`; concatenations of
2-paths use the induced filling of `Pij`. Cartesian reversal also takes the
appropriate lawful filling. Suppressing those parameters in diagrams must not
erase them from the eventual declarations.

`wholeComparison` lifts a carrier-path comparison to a whole-path comparison
using `equivalenceFieldsIsProp`, carrier univalence, and both recovery paths.
Its input carrier comparison remains necessary: native sethood of the target
carrier does not say that all carrier equivalences are the same. Nor does it
say that `O`, which contains the universe of carriers, is a set.

The [selected recovery declarations](../../../SquareKit/Internal/Cubical/NativeStructureUaComparison.lean)
`explicitEquivalence`, `explicitInverse`, `explicitRightInverseAt`, and
`explicitLeftInverseAt` retain whole native paths. The corresponding Cartesian
file has the same contract. A path in the whole-path family is the right
dimension for an associator here. A path between two such associators has
type

```
Term (Path (Path P03 p q) H K)
```

and is a native 3-path in `O`. Host equality `H = K` would be a different and
stronger selection claim, unnecessary for the finite contract.

## Three supplied equivalences and two composites

Let `e : Equivalence s0 s1`, `f : Equivalence s1 s2`, and
`g : Equivalence s2 s3`. Fix lawful fillings of decoded carriers. Supply
independently:

```
w01_12 : HomotopyEquivalence (e.map ≫ f.map)
w12_23 : HomotopyEquivalence (f.map ≫ g.map)
wL     : HomotopyEquivalence ((e.map ≫ f.map) ≫ g.map)
wR     : HomotopyEquivalence (e.map ≫ (f.map ≫ g.map))

E02 = e.compWith f w01_12
E13 = f.compWith g w12_23
EL  = E02.compWith g wL
ER  = e.compWith E13 wR
```

Fillings in these abbreviations are precisely the source and target fillings
of each `compWith`. Retain `wL` and `wR` separately even when carrier-map
associativity makes their types definitionally or propositionally align.
No equality between those witnesses is an input or conclusion.

The first proposed declaration is

```
A(e,f,g,w01_12,w12_23,wL,wR) :
  Term (Path P03 (Coded.path EL) (Coded.path ER))
```

with target carrier sethood. A construction is available on paper: use
`Category.assoc` to give a constant map homotopy between the two composite
maps; lift it with `EquivalencePaths.ofHomotopy`, retaining both supplied
complete witnesses; lift through `equivalencePath` using target sethood;
apply `homogeneousPathMap explicitMap`. This uses the full native equivalence
records at both ends. It does not require a prior associativity theorem for
their point or step homotopies. In the Cartesian model the analogous
complete-equivalence homotopy machinery is used by native univalence; its
specialized wrapper and exact endpoint conversions still need implementation.

Let `p=Coded.path e`, `q=Coded.path f`, `r=Coded.path g`, and let `μ` denote
the existing composition comparison with its named supplied witness. Write
`H · K` for vertical concatenation of 2-paths, `H ▷ r` for right whiskering
by a whole path, and `p ◁ H` for left whiskering. The next required paths are

```
L = μ(E02,g,wL) · (μ(e,f,w01_12) ▷ r)
    : Path P03 (Coded.path EL) ((p ⋆ q) ⋆ r)

R = μ(e,E13,wR) · (p ◁ μ(f,g,w12_23))
    : Path P03 (Coded.path ER) (p ⋆ (q ⋆ r))
```

These formulas expose why merely naming `A` does not yet compare the paths
obtained by composing #687's comparisons. The finite contract should also
construct `L` and `R`, including their exact whole-path endpoints. In this
form `L` needs sethood of carrier 2 as well as carrier 3 because it invokes
`μ(e,f,...)`. All set witnesses for the finite chain can be supplied by the
client; minimizing those assumptions through equivalence transport is a
separate derivation, not a reason to silently omit an intermediate requirement.

If `a(p,q,r) : Path P03 ((p ⋆ q) ⋆ r) (p ⋆ (q ⋆ r))` is a direct
concatenation associator, the coherence comparison is exactly

```
Term (Path
  (Path P03 (Coded.path EL) (p ⋆ (q ⋆ r)))
  (L · a(p,q,r))
  (A(e,f,g,...) · R))
```

This is a 3-path. Conversely, the selected data already define a bounded
associator `reverse L · A · R` on these three selected paths once whiskering
exists. A general direct associator would make a useful shared operation and
avoid choosing equivalence witnesses to concatenate paths. It must be derived
from lawful filling, not inserted as a new caller law. Equality with the
selected associator is not required; the displayed 3-path is the appropriate
comparison.

## Derivability and missing reusable lemmas

The following is a proposed proof decomposition, not an executed Lean proof.
It identifies a smaller prerequisite than new associator or pentagon fields.

1. `EquivalenceFamilies.maps A B` is a native set when `B` is a native set,
   by `HomotopyLevels.piIsSet`. The source requires lawful filling, not an
   independent sethood assumption.
2. The complete equivalence-witness family is a native proposition. In the
   original model, `EquivalencePaths.substitutedWitnessContractible` already
   proves that every inhabited substitution of `isEquiv f` is contractible.
   Apply it over the generic witness and abstract its contraction to obtain
   the proposition witness. This proof must cover substituted witnesses even
   when the original map has no global equivalence witness, as the existing
   declaration explicitly does.
3. A dependent total over a native set with proposition fibers is a native
   set. Implement this closure lemma, or its precise equivalence-family
   specialization, using `PropositionExtension.pathEquivalence` and
   proposition transport through a native equivalence. A product-only
   sethood lemma does not suffice for the dependent witness family.
4. Apply that result twice: first to complete carrier equivalences over maps,
   then to `Native.equivalences D s t` over carrier equivalences using the
   existing `equivalenceFieldsIsProp`.
5. Transport sethood across `explicitEquivalence` to obtain
   `Term (isSet (Path (objects D Γ) (objectOf D a s) (objectOf D b t)))`
   from target carrier sethood. Existing `mapProp` and `pathCongr` handle
   strict family isomorphisms; a homotopy-equivalence version requires a
   proof using the selected inverse and its homotopies. Do not replace
   `explicitEquivalence` by an assumed strict isomorphism.
6. `pathIsPropAt` applied to that whole-path sethood yields proposition data
   for each 2-path family. `HomotopyLevels.path` then supplies the 3-path
   between any two already constructed parallel comparisons, retaining those
   comparisons as exact endpoints.

The building blocks are in
[HomotopyLevels](../../../SquareKit/Internal/Cubical/HomotopyLevels.lean),
[EquivalencePaths](../../../SquareKit/Internal/Cubical/EquivalencePaths.lean),
[PropositionExtension](../../../SquareKit/Internal/Cubical/PropositionExtension.lean),
and [NativeStructurePreservation](../../../SquareKit/Internal/Cubical/NativeStructurePreservation.lean).
The analogous Cartesian truncation library has `piIsSet`, `propIsSet`, and
`pathContractible`. The proposed closure/transport lemmas must be established
in both models; this report does not claim that matching names alone provide
the missing proof.

The path-operation prerequisite is a uniform construction of left/right
whiskering of whole 2-paths, plus associativity and left/right units of the
existing filler-selected concatenation. Reindex the inputs into an interval
context, concatenate there using the reindexed filling, then abstract the
interval coordinate. Endpoint alignment and the concatenation reindex theorem
are proof obligations. The original `NativePathComposition` already proves
`homogeneousConcat_reindex`. The Cartesian construction uses a different
square filler, so copying a formula without its filler laws is insufficient.

This derivation predicts mathematical feasibility under the existing set and
filling assumptions. Missing helper lemmas and the recorded elaboration costs
are implementation work; they are not separating counterexamples. If this
derivation stalls, retain the exact failing helper and its hypotheses as the
bounded prerequisite, rather than adding a final coherence field.

## Units, triangle, and fourfold pentagon

Construct `I_s : Equivalence s s` with identity map, a supplied complete
identity witness, and reflexive point/step homotopies. Construct
`ν_s : Path Pss (Coded.path I_s) (homogeneousRefl Xs)` using identity
transport and whole comparison. Reflexivity of the forward map alone does
not establish equality of this selected whole path with reflexivity.

At the ordinary whole-path level let

```
λp : Path P01 (refl X0 ⋆ p) p
ρp : Path P01 (p ⋆ refl X1) p
```

be filler-derived native 2-paths. For `p : P01`, `q : P12`, the triangle
boundary consists of the parallel 2-paths

```
Tlong  = a(p,refl X1,q) · (p ◁ λq)
Tshort = ρp ▷ q

Tlong,Tshort : Path P02 ((p ⋆ refl X1) ⋆ q) (p ⋆ q)
```

and the triangle is `Term (Path (Path P02 ((p ⋆ refl X1) ⋆ q) (p ⋆ q))
Tlong Tshort)`, a 3-path in `O`. For supplied selected identity witnesses,
first use `μ` and `ν` to align their selected paths with the displayed
reflexive paths. Preserve those alignment faces; do not change the selected
identity path by definitional assertion.

For four composable whole paths `p,q,r,s`, name the five bracketings

```
B0 = ((p ⋆ q) ⋆ r) ⋆ s
B1 = (p ⋆ (q ⋆ r)) ⋆ s
B2 = p ⋆ ((q ⋆ r) ⋆ s)
B3 = p ⋆ (q ⋆ (r ⋆ s))
B4 = (p ⋆ q) ⋆ (r ⋆ s)

Plong  = ((a(p,q,r) ▷ s) · a(p,q ⋆ r,s)) · (p ◁ a(q,r,s))
Pshort = a(p ⋆ q,r,s) · a(p,q,r ⋆ s)
```

Both routes inhabit `Path P04 B0 B3`. The pentagon is
`Term (Path (Path P04 B0 B3) Plong Pshort)`, a native 3-path. The vertical
parentheses displayed above are part of the contract; no strict vertical
associativity is assumed.

For independently supplied witnesses, build a composite `E_T` for each tree
`T`, retaining each supplied internal witness. Recursively define
`N_T : Path Pij (Coded.path E_T) B_T` by `μ` and whiskering. A leaf uses
reflexivity. Each tree rotation `T → U` gives the selected-edge comparison
`N_T · edge(B_T,B_U) · reverse N_U`. The two selected pentagon routes therefore
start at `Coded.path E_B0` and end at `Coded.path E_B3`, with every intermediate
whole path and supplied witness fixed. Truncation gives their 3-path directly;
one need not cancel normalization paths by host equalities. Alternatively
compare independently constructed associator edges with these normalized
edges using the same 3-path mechanism.

This covers a finite triangle and pentagon, not an unbounded hierarchy or a
strictly natural choice of all higher cells. The target-set argument cannot be
exported to non-set carriers or proof-relevant preservation fields without
replacing its proposition-fiber premise. The current `Description` grammar
also does not provide arbitrary dependent structure fields.

## Integer client, substitution, and rejection

Use the actual admissions
`Examples.NativeLatticeTransport.Presheaf.admission ℤ` and its Cartesian
counterpart. The existing [client](../../../Examples/NativeStructureCoherence.lean)
defines the system `S_n` with point `n` and successor step, and
`move n k : S_n ≃ S_(n+k)` with a complete native witness constructed from
the admitted carrier isomorphism. The proposed triple is

```
e = move 0 1 : S0 → S1
f = move 1 2 : S1 → S3
g = move 3 3 : S3 → S6
h = move 6 4 : S6 → S10
```

The two triple witnesses may be obtained by nested `HomotopyEquivalence.comp`
at their corresponding bracketings and passed to `compWith` independently.
The resulting whole paths both have endpoints `X0` and `X6`; their mapped
initial point decodes to 6 and its next successor to 7. The fourfold
bracketings have endpoints `X0` and `X10`, with observations 10 and 11.
Every composite has its own point/step paths. A second specialization should
use complete witnesses from the corresponding composite carrier isomorphisms,
retaining those witnesses rather than normalizing both variants to one record.
This exercises witness independence without claiming that the two records are
provably unequal.

Extend the existing `rejects_unchanged` proof to reject a whole-transport
endpoint still at 0: a purported point path from 6 to 0, or 10 to 0, maps
through the admission's decoding to equality in the constant integer family,
which contradicts integer arithmetic. This distinguishes the retained
transport from a degenerate contract reporting only existence of comparable
paths. A second control checks `sigmaFst (E_T.native)` against
`equivSections ⟨E_T.map,E_T.witness⟩`; erasing or replacing the supplied
witness is unacceptable even if the forward integer map remains correct.
Translations commute, so this client alone cannot detect composition-order
reversal. Do not advertise it as an order-separating test.

For `σ = projection (interval Γ)`, reindex each supplied witness using
`w.reindex σ`. Allow independent lawful source/target fillers after
substitution, as the existing `composition_reindex` does. Let `ELσ, ERσ`
denote fresh composites after substitution and let

```
δL : Path P' (path ELσ) (reindexPath (path EL) σ)
δR : Path P' (path ERσ) (reindexPath (path ER) σ)
```

be whole endpoint comparisons constructed by `path_reindexWith`. Lift
`reindexPath` to 2-paths, naming the resulting `Rσ(A)`. The required
substitution comparison has exactly these parallel faces:

```
Aσ · δR,   δL · Rσ(A)
  : Path P' (path ELσ) (reindexPath (path ER) σ)
```

It is again a 3-path. Merely substituting a fixed `A` gives an exact substituted
cell, but does not compare it with a fresh selection `Aσ`. Package endpoints
and comparisons before specializing fillers, following the existing `PathData`
client and #687's [resource evidence](../native-structure-coherence/attempts.md).

## Separate cross-model prerequisite

Let `a` be the original integer admission and
`u = Presheaf.SmallUniverse.NativeUnivalence.ua a.code a.code shift1 E`.
Its decoded line is

```
Ldm = Presheaf.SmallUniverse.liftedDecode
        (Presheaf.SmallUniverse.codeOfPath u)
```

over the original interval context. The candidate Cartesian family is
`L = Cartesian.relativeFamily Ldm`, over the actual Cartesian interval
context. This distinction matters: `restrictFamily Ldm` is over the restricted
original interval, whereas `intervalContextInclusion` pulls it back to the
Cartesian interval. `intervalInclusion` is explicitly not an isomorphism.

The source [restriction](../../../SquareKit/Internal/Cubical/CartesianRestriction.lean),
[path](../../../SquareKit/Internal/Cubical/CartesianPaths.lean), and
[witness](../../../SquareKit/Internal/Cubical/CartesianWitnesses.lean) APIs
retain more than endpoint maps. `restrictEquivalence` retains complete
contractions and has an injectivity theorem; `twoPathIso` and `threePathIso`
recover iterated path data. They do not themselves produce a map from the
restricted original small universe to the independently selected Cartesian
small universe. In particular, restricted complete witness data in
`Cartesian.Equivalence` must be related to the native Cartesian
`HomotopyEquivalence` interface before applying Cartesian univalence.

The precise bounded prerequisite is to construct a Cartesian code `cL` for
this specific `L`, a decoding isomorphism `liftedDecode cL ≅ L`, and a lawful
Cartesian filling used by that admission. `LargeConstructors.construct`
requires a `SmallPresentation.Data L` and lawful filling. Then give endpoint
decoder comparisons to the independently admitted Cartesian integers and
compare the full transported equivalence witness with the independently
selected translation witness. Endpoint maps alone are insufficient. This
would make a selected Cartesian universe path comparison a well-typed next
task; it does not yet construct that comparison.

Nonidentity translation does not establish that this line lies outside the
common-host presented-family boundary. A line can admit a constant integer
presentation with different trivializations at its two ends and still encode
translation by 1. Test for such a presentation explicitly. If one exists,
retain the line as a decoder/witness interoperability test but do not count it
as the required beyond-common-host example. A bounded investigation should
return either the actual Cartesian admission and complete witness comparison,
or its precise failed prerequisite; separately it should exhibit a constant
presentation or an invariant ruling one out. This report proves neither
non-presentation nor impossibility of the candidate. Within-model coherence
does not depend on this branch.

## Recommendation and acceptance discriminator

Schedule the within-model work in two dependent parts: first the path
whiskering/unit/associativity and sethood-transport helpers, then the supplied
triple comparison, its comparison with composed `μ` paths, selected units,
triangle/pentagon 3-paths, and nonidentity substitution. The discriminator for
the prerequisite is a checked term of the whole-path sethood type in both
models from native target sethood alone, together with exact typed whiskering
boundaries. No constant-family presentation or final coherence-law parameter
may be added to that statement. If this fails, record the failed intermediate
lemma rather than claiming a mathematical obstruction.

Acceptance for the finite contract includes the actual admitted integer
triple/fourfold examples, all endpoint equations, the unchanged-point
rejections, retained complete supplied witnesses, and continued use of the
existing direct clients under their original assumptions. The generic theorem
must be checked with arbitrary coded native set targets; the integer examples
discharge its hypotheses but do not replace that theorem. Normal repository
Lean validation and independent implementation review remain to be performed
when these proposed declarations are implemented.

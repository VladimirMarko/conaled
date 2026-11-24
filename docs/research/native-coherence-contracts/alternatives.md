# Alternatives, generality and the cross-model boundary

Retain the selected total correspondence and derive the finite set-carrier
coherence through it. Add direct path associativity and whiskering only where
the displayed diagrams require those operations. Do not add associativity,
triangle or pentagon as fields of `Equivalence`. Keep the cross-model decoder
investigation separate. The integer selected-ua line is a useful comparison
test, but it has not been shown to escape a common constant presentation.

This is the initial alternatives perspective for #697. I previously coordinated
the independent #633 Standards/Spec review. That work concerned ordinary span
interpretation coherence, not this native construction. The host could not
start a third fresh thread, so this existing thread was reused. I read the
shared brief and issue specification, but no #697 peer report or coordinator
synthesis. This is a design assessment, not acceptance review.

Repository statements below refer to commit
`f0cac600a954fae4f340a9262ad732f6fbb30cc7`. Principal inspected source files were
compared against that commit and were unchanged. “Existing” means an inspected
Lean declaration, not a fresh execution in this assessment. “Paper” and
“proposed” claims have not been elaborated or kernel checked here. No Lean
probe or full build was run, and no implementation or tracker was changed.

## What the existing construction establishes

The strongest reason to retain the current interface is its information
boundary. In both models, `Equivalence` contains the map, its complete
contractible-fiber witness, the point path, and a homotopy of entire
endomorphism maps. `compWith` keeps the caller's composite witness and builds
preservation paths separately. `Coded.path` then applies the selected total
structure correspondence. `Coded.composition` compares this selected whole
path with actual concatenation; it does not replace the supplied witness by
an isomorphism witness. See
[original coherence](../../../SquareKit/Internal/Cubical/NativeStructureCoherence.lean)
and [Cartesian coherence](../../../SquareKit/Internal/Cubical/CartesianNativeStructureCoherence.lean).

`wholeComparison` already accepts arbitrary whole paths with fixed structured
endpoints. Given a comparison of their carrier paths and native sethood of the
target carrier, it recovers both complete structure paths through the selected
correspondence. It uses `equivalenceFieldsIsProp`, not a constant-family
presentation. The selected inverse and both recovery homotopies are concrete
inputs to its derivation. This is stronger than comparing decoded points and
weaker than asserting host equality of the paths.

`composition_reindex` retains the complete reindexed composite witness while
allowing fresh lawful fillers after substitution. Its current conclusion is a
native 2-path between whole paths. It does not compare two independently
constructed 2-paths, nor prove a strict equation between filler choices.
`Examples.NativeStructureCoherence.substitutionComparisonData` exercises the
interval projection with both paths retained as data. The existing direct
lattice transport and the sethood-based generic lattice comparison can stay
under their original assumptions.

## A finite contract with explicit dimensions

The following is proposed notation, not Lean declarations. Write
`P_X(x,y) = homogeneousPath X x y`, with inhabitants always obtained as `Term`.
Let `A_i = liftedDecode a_i`, `s_i` be pointed endomorphisms on `A_i`, and
`x_i = objectOf description a_i s_i.fields`. Assume lawful decoded fillings
and native sethood for every carrier used as a target of a comparison. Requiring
sethood of all four carriers is a simple sufficient finite contract; a theorem
may later expose only the witnesses its proof uses.

Take independent `e : Equivalence s₀ s₁`, `d : Equivalence s₁ s₂`, and
`k : Equivalence s₂ s₃`. Retain four supplied witnesses:

- `w₀₁₂ : HomotopyEquivalence (e.map ≫ d.map)`;
- `w₁₂₃ : HomotopyEquivalence (d.map ≫ k.map)`;
- `wL : HomotopyEquivalence ((e.map ≫ d.map) ≫ k.map)`;
- `wR : HomotopyEquivalence (e.map ≫ (d.map ≫ k.map))`.

Set `ed = compWith e d w₀₁₂`, `dk = compWith d k w₁₂₃`,
`L = compWith ed k wL`, and `R = compWith e dk wR`, supplying the named lawful
fillers at each call. Write `p = path e`, `q = path d`, `r = path k`,
`PL = path L`, and `PR = path R`. Both `PL` and `PR` inhabit
`Term (P_X(x₀,x₃))`, where `X = objects description Γ`.

The next selected associativity comparison has type

```text
alpha(e,d,k,w₀₁₂,w₁₂₃,wL,wR) :
  Term (P_(P_X(x₀,x₃))(PL,PR)).
```

This is a native 2-path. Category associativity identifies the underlying
composite maps in the host; it does not identify `wL` and `wR`. A paper route
uses a constant map homotopy after endpoint transport, lifts it to a native
path of complete equivalence records, lifts through proposition-valued
preservation, and applies `explicitMap`. `EquivalencePaths.ofHomotopy` and
`equivalencePath` provide the relevant existing operations. The witness
family's contractibility is the reason the supplied witnesses can be related,
not a reason to discard them or demand their host equality.

The existing composition comparisons also give routes

```text
betaL : PL -> path ed · r -> (p · q) · r
betaR : PR -> p · path dk -> p · (q · r)
```

in the path family `P_X(x₀,x₃)`. The second edges require whiskering a 2-path
by concatenation. A direct path associator has boundary
`a(p,q,r) : ((p·q)·r) -> (p·(q·r))`. An alternative in this bounded setting is
to lift the existing original-model carrier `NativeUnivalence.tripleComparison`
through `wholeComparison`, then build the Cartesian counterpart from its
transport comparisons. Neither option should be described as already proving
the following native 3-path:

```text
coherence : Path( alpha ·₂ betaR, betaL ·₂ a(p,q,r) ).
```

Both routes start at `PL` and end at `p·(q·r)`. The notation `·₂` means
concatenation in the whole-path family. Its parentheses must be fixed in the
implementation. This comparison should be a separate result, so merely
defining `alpha` from the right-hand route cannot masquerade as independent
compatibility of two constructions.

For units, define `id_s` from the identity map, an actual identity equivalence
witness, reflexive point path and reflexive step homotopy. Compare `path id_s`
with `refl x_s` by a 2-path; compare `path (compWith id_s e w)` and
`path (compWith e id_t w')` with `path e`, retaining `w,w'`. Let path unitors
have boundaries `lambda(q) : refl·q -> q` and `rho(p) : p·refl -> p`.
The triangle boundary is the pair of 2-paths

```text
((p·refl)·q) --a(p,refl,q)--> p·(refl·q) --p ◁ lambda(q)--> p·q
((p·refl)·q) ----------------rho(p) ▷ q------------------> p·q.
```

For a fourth independent equivalence with selected path `s`, the five
fourfold path bracketings are `(((p·q)·r)·s)`, `((p·q)·(r·s))`,
`((p·(q·r))·s)`, `(p·((q·r)·s))`, and `(p·(q·(r·s)))`.
The pentagon compares

```text
a(p·q,r,s) ·₂ a(p,q,r·s)
((a(p,q,r) ▷ s) ·₂ a(p,q·r,s)) ·₂ (p ◁ a(q,r,s)).
```

Each route has source `(((p·q)·r)·s)` and target `p·(q·(r·s))`.
Its witness is a native 3-path, not host equality of the two 2-path terms.
The selected-composite version must choose one complete nested composite at
each of its five vertices and retain that same choice on all incident edges;
separately supplied witnesses are permitted, but a shared vertex cannot change
silently between routes. Normalization routes from these selected vertices to
the displayed path bracketings and their 3-path compatibility are part of the
contract, not implicit identification of witness records.

Substitute the entire diagram along `σ = projection (interval Γ)`. Compare
freshly constructed and substituted 2-paths after inserting the existing
`path_reindex` endpoint comparisons. The result is a 3-path with fixed aligned
endpoints. Reindexing a 3-path itself yields a 3-path with reindexed boundary;
comparing that result with an independently rebuilt 3-path would be a 4-path
and need not be in the first contract. No demand for literal filler equality
is needed.

## Derivability versus added hypotheses

The finite set-carrier argument should first prove that the whole-path family
`P_X(x₀,x₃)` is a native set. Paper derivation: maps into the set carrier `A₃`
form a set; equivalence witnesses are proposition-valued; preservation fields
are proposition-valued by the existing theorem; therefore the complete
structured-equivalence family is a set; the selected total equivalence transfers
that level to the whole-path family. Consequently the family of 2-paths between
fixed whole paths is a proposition and any two such 2-paths have a 3-path.
This supplies triangle, pentagon and the compatibility above once their actual
routes are constructed.

This derivation is not already a single library theorem. The inspected
[homotopy-level API](../../../SquareKit/Internal/Cubical/HomotopyLevels.lean)
and its [Cartesian counterpart](../../../SquareKit/Internal/Cubical/CartesianHomotopyLevels.lean)
contain `piIsSet`, `pathIsPropAt`, `propIsSet`, and lawful path fillings.
The missing packaging includes dependent Sigma sethood over proposition
fibers, transfer of sethood along the supplied native homotopy equivalence,
and the resulting whole-path sethood theorem. The whole equivalence-witness
family must be handled over generalized maps, not only global equivalences;
`EquivalencePaths.substitutedWitnessContractible` illustrates this requirement.
These are proposed derived lemmas, not new client assumptions.

A generic direct path route has wider mathematical scope: ordinary path
associators and coherent unitors need not assume set carriers. It also costs
more here: both models need explicit path-family concatenation maps,
whiskering, endpoint equations and coherence of the chosen operations.
Cartesian reversal is itself filling-derived, unlike the original interval's
reversal operation. Neither equality of underlying maps nor the present
`wholeComparison` removes these implementation obligations.

For the first contract, use selected recovery to relate the independent
structure data and direct operations to state the finite diagrams. Do not
replace either existing presentation. The sethood argument provides 3-cells
for arbitrary displayed parallel 2-cells, a stronger uniqueness facility than
is available on unrestricted carriers. Outside sets, this automatic uniqueness
argument fails; particular coherent direct associators may still be derivable.
Dependent structure fields and proof-relevant laws require retaining and
transporting their path data, not reusing `equivalenceFieldsIsProp` without its
hypotheses.

The checked integer source supplies actual admissions in both models via
`Examples.NativeLatticeTransport.*.admission`. The finite next specialization
uses `move 0 1`, `move 1 2`, `move 3 3`, and then `move 6 4`. These preserve
successor, reach points 1, 3, 6 and 10, and use distinct nonidentity carrier maps.
Both bracketings must retain their own witnesses while recovering point 6
(10 for fourfold composition). Reuse the interval-projection substitution and
reject a path from the moved point back to 0 using discrete decoding, as the
existing `rejects_unchanged` proof does. This detects an erased nonidentity
composite. It does not detect swapping the order of integer translations,
which commute; a claim about order sensitivity needs a separate noncommuting
client. Do not overstate this client's discrimination.

## The proposed selected-ua line for #688

Choose the actual original admission `a` of integers and `f = shift a 1`, with
its supplied `HomotopyEquivalence.ofIso` witness `E`. Let
`pDM = Presheaf.SmallUniverse.NativeUnivalence.ua a.code a.code f.hom E` and
`uDM = SmallUniverse.codeOfPath pDM`. The exact candidate family is

```text
LDM = Presheaf.SmallUniverse.liftedDecode uDM
LC  = Cartesian.relativeFamily LDM
```

where `LC` lies over `total (Cartesian.interval (Cartesian.restrict Γ))`.
This uses `intervalElements Γ`, not an assumed isomorphism of interval
presheaves. `intervalInclusion` is expressly not an isomorphism in
[CartesianPaths](../../../SquareKit/Internal/Cubical/CartesianPaths.lean).

The existing restriction API supplies families, maps, sections, dependent
path isomorphisms and full witness restriction. In particular,
[CartesianWitnesses](../../../SquareKit/Internal/Cubical/CartesianWitnesses.lean)
contains `restrictEquivalence`, selected-inverse compatibility, and injectivity
on complete source equivalence witnesses. `twoPathIso` and
[threePathIso](../../../SquareKit/Internal/Cubical/CartesianSelectedComparison.lean)
retain higher paths. None of these declarations provides a map from the
original universe codes to Cartesian universe codes or identifies independent
selected ua lines. The finite nerve `realizedDecoderIso` in
[CartesianRealization](../../../SquareKit/Internal/Cubical/CartesianRealization.lean)
is specialized to that nerve, not such a map for arbitrary original codes.

To construct a Cartesian code for `LC`,
[LargeConstructors.construct](../../../SquareKit/Internal/Cubical/CartesianLargeFamilyConstructors.lean)
requires `SmallPresentation.Data LC`, an actual `Cartesian.Filling LC`, and
its `Lawful` proof. Fiber smallness is available in principle from the original
decoder's small presentation pulled through `intervalElements`; it is not an
assumption of finite cardinality. The missing operational evidence is a
Cartesian filler that handles arbitrary target subcontexts and variable source
graphs, including diagonal cases, uniformly under every target substitution.
An original `Filling` is indexed by its own cofibrations and fixed source end;
simply restricting its output does not accept an arbitrary Cartesian box.
Endpoint decoder isomorphisms and the complete transport-equivalence comparison
must then connect the admitted line to the independently chosen Cartesian ua.
Matching only the forward action on integers does not provide that comparison.

There is also a boundary problem with this particular example. `f` is a strict
isomorphism. In the source [Glue definition](../../../SquareKit/Internal/Cubical/Glue.lean),
a compatible element's face values are determined by its ambient value whenever
the face map is a strict isomorphism: explicitly take
`face(g,h) = e⁻¹(A.map g ambient)`. Naturality follows from the inverse map's
naturality, and the compatibility and inverse equations follow from the two
isomorphism laws. Thus, on paper, `compatibleUnglue` is then an isomorphism.
`familyIso` transports this to the strictified Glue family. The selected ua
charts use the translation and identity as their two boundary maps, so there
is a concrete route to a strict trivialization of the entire admitted line.
The chart gluing and decoder equations still need proving; this assessment
does not assert a checked global trivialization.

Therefore “a nonconstant selected code line” is not evidence that its decoder
has no common host presentation. The bounded first prerequisite should resolve
this exact case: construct the candidate, attempt the natural trivialization
with all endpoint charts, and either prove it or isolate the first failed
mathematical obligation. A timeout is only encoding evidence. If the
trivialization succeeds, retain the selected-line comparison as a useful
endpoint/alignment test and explicitly mark it as inside the presented-family
boundary. Do not close the beyond-common-host requirement with it.

A stronger concrete candidate is the restricted universal decoder

```text
U_DM = Presheaf.smallFamilyCodes.{u}
R = Cartesian.restrictFamily
      (Presheaf.SmallUniverse.liftedDecode (𝟙 U_DM))
    over Cartesian.restrict U_DM.
```

This candidate cannot have one fixed constant-host presentation if the actual
unit and Boolean admissions are included: evaluating such a presentation at
their zero-cube codes would give a bijection between a singleton and a
two-element type. This is a paper discriminator, not a checked rejection in
this assessment. It avoids choosing a representation that only looks variable.
It is a single specified family, but it includes all original codes; admitting
it is a substantive prerequisite, not a small corollary of the integer client.

The ready investigation is to establish or refute the required Cartesian
filling/admission contract for `R` under the repository's unchanged source
cofibration assumptions. Deliver a symbolic construction with uniformity and
all box laws, or an explicit failing target box/closure obligation. Begin with
variable-source diagonal boxes and retain their typed boundaries. Supply the
restricted small-presentation data and the unit/Boolean non-presentation
control. Only after that result is available should the successor construct
`κ : restrict U_DM ⟶ U_C`, its complete decoder isomorphism, and compare
`κ` applied to the restricted source ua line with independent Cartesian ua.
A full comparison must retain selected equivalence fibers and endpoint
alignment; decoder classification alone does not give selected-filler equality.
This investigation does not block within-model associativity.

## Primary-source checks and their limits

- The HoTT Book, repository revision `578b85c`,
  [identity/path algebra](https://raw.githubusercontent.com/HoTT/book/578b85c/basics.tex),
  Lemma 2.1.4 and its discussion, derives unit, inverse and associativity paths
  using identity elimination. Higher coherence is at the next path dimension.
  Its hypothesis is the identity eliminator with the relevant computation rule;
  it is not a theorem that any arbitrary binary operation on local Lean path
  terms satisfies those laws. The same chapter's structure examples retain
  associativity proof data on general carriers, explaining why proof-relevant
  laws cannot be dropped here.
- The same pinned book's
  [homotopy levels](https://raw.githubusercontent.com/HoTT/book/578b85c/hlevels.tex),
  section 7.1 (labels `h-level-retracts`, `ntypes-sigma`, `hlevel-prod`), proves
  closure of n-types under retracts/equivalences, Sigma with n-truncated base
  and fibers, and Pi with n-truncated fibers. Pi closure uses function
  extensionality. These support the paper sethood derivation; the repository
  still needs native versions with its filling/reindex data.
  [Equivalences](https://raw.githubusercontent.com/HoTT/book/578b85c/equivalences.tex),
  chapter 4, distinguishes contractible-fiber equivalence witnesses from raw
  quasi-inverse data, which need not be proposition-valued. This supports
  retaining the current witness definition.
- Cohen, Coquand, Huber and Mörtberg,
  [TYPES 2015 published paper, DOI 10.4230/LIPIcs.TYPES.2015.5](https://drops.dagstuhl.de/storage/00lipics/lipics-vol069-types2015/LIPIcs.TYPES.2015.5/LIPIcs.TYPES.2015.5.pdf),
  sections 4.5–4.6 and 9.1, derives Path operations using composition. It
  distinguishes Path from an identity type with judgmental computation:
  transport in a constant family need not be judgmentally identity. That
  distinction rules out silently importing host `Eq` path induction for the
  selected native fillers.
- Angiuli, Brunerie, Coquand, Harper, Hou and Licata,
  [author manuscript, Syntax and Models of Cartesian Cubical Type Theory](https://www.cs.cmu.edu/~rwh/papers/uniform/uniform.pdf),
  inspected 2026-11-24, SHA-256
  `ea235cf09eae29d3859f31976bc43a939a6565410ff4117addb99d0602c213a3`.
  Theorem 2 assumes a finite-product base, distinct interval endpoints and
  pointwise decidable cofibrations closed under interval equality, disjunction
  and interval quantification. It classifies families already equipped with
  diagonal Kan composition; it does not supply that operation for every
  restricted family. Section 3.4 converts endpoint to diagonal composition in
  a De Morgan setting with connections, reversal and diagonal cofibrations.
  Its universe-equivalence suggestion is stated prospectively. Neither that
  suggestion nor model existence proves the repository's change-of-cubes map
  or comparison of its independently selected universes.

## Recommended successor boundary

The feasible first implementation contract is the two model-local selected
associativity comparisons, their comparison with the existing composition
routes, unit comparisons, finite triangle/pentagon 3-paths, and aligned
nonidentity reindexing at the dimensions specified above. First derive native
sethood of the whole-path family and the necessary whiskering/normalization
lemmas. Retain full supplied witnesses at every vertex and use actual integer
admissions for the 0→1→3→6→10 client and rejecting endpoint test. Preserve the
direct APIs and lattice client. Integrated build/audit and statement review
must then establish the proposed declarations, including arbitrary contexts.

Schedule the selected-line trivialization and restricted-decoder admission
investigation separately for #688. A checked positive construction or explicit
contract obstruction is useful evidence; repeating the requirement as a field,
showing only decoded integer agreement, or waiting for another consumer is not.

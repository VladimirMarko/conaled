# Cubical model construction: source selection and milestones

[#321](https://github.com/VladimirMarko/conaled/issues/321) is an active
construction programme. This selection checkpoint chooses De Morgan cubical
presheaves, followed by constructed fibrant dependent families, for a specified
universe-free cubical fragment. It does **not** claim that the model or sound
interpretation is already constructed. Source checking, a constructed model,
and interpretation of an external derivation are separate obligations.

## Source evidence and first consumers

The inspected local baseline is
`5411b02384643285a00e45df9d27115b81c1ce9f`. The preserved
[archive inventory](../history/orbifold/agda-checkpoints/README.md) supplied
sources, not hypothetical future artifacts. The coordinator independently
reproduced both checks with Agda 2.8.0.2. Myers checked 357 project modules;
Kock checked 146. Both source hash maps match their supplied receipts. These
runs are reused here, not repeated or presented as Lean validation.

| Artifact | Immutable identity |
| --- | --- |
| Myers checkpoint 22 archive | SHA-256 `19e6f70f5c86856ccd98b6ffb96817f6ee4a58938aa76e5aef1d91b670ba6a53` |
| Kock archive | SHA-256 `7f615fa495853f64cf19ba53259ea01bc429ef631b2f119eef99eb1fca33bd69` |
| Myers fresh receipt | SHA-256 `57b6dbf046a550b1e8a7e3e604f06974fad69c287e64b3a983b4fb4bca735e66` |
| Kock fresh receipt | SHA-256 `38c4c05e33a1eed0238db7641720b348140d920de7f457b3a4f69b835646b85e` |
| Myers Cubical library | v0.9, commit `b150186d2544e7efeddd31e5d14a8b9ecbb100f7` |

The [source audit manifest](cubical-model-source-audit.json) traverses explicit
module imports from `Orbifolds.CubicalShells` and `SDG.Calculus.Slope`, recording
source hashes, resolved paths and edges. It finds 156 and 11 source files,
respectively, including library/compiler modules, with no unresolved imports.
This is a static import closure, not a minimal declaration dependency proof.
It strips nested block and line comments before finding imports. Compiler
builtin postulates are rule declarations requiring semantics, not newly
introduced user assumptions.

**First cubical consumer:** the preserved
`Orbifolds.CubicalShells.contract-cube`:

```text
Cube 0 X = X
Cube (n+1) X = I → Cube n X
contract-cube n c : constant-cube n (origin n c) ≡ c
contract-cube 0 c = refl
contract-cube (n+1) c j i = contract-cube n (c (i ∧ j)) j
```

Its first retained instance is `n=1`, whose contraction is `c(i ∧ j)`.
At `j=0` it is constant at `c(0)`; at `j=1` it is `c(i)`. These are source
conversion equations, not merely unrelated path witnesses. The declaration
uses interval abstraction/application, connection and endpoint equations,
ordinary functions, and natural-number recursion. Its type parameter is
schematic at a fixed universe level in the initial interpretation. Interpreting
the original polymorphic function *as an element of an internal universe* would
add a classifier obligation not discharged by that schematic interpretation.

The enclosing file also defines shells using Σ and paths and imports
microlinearity. The selected declaration does not refer to shell restriction,
crisp binders, ring/KL parameters, transport, Glue, HIT elimination or the
microlinearity module. Its imports nevertheless contain much of that material.
The checkpoint's safe/cohesion flags do not erase those distinctions. The
source status, paper inventory and correction notes remain relevant to any
later geometric consumer; no claim here imports the entire orbifold theorem.

**Intensional comparison consumer:** `SDG.Calculus.Slope.Results.slope-constant`
proves that the KL slope of a constant function is zero. The inspected term
uses `uniqueness`, ring zero/unit laws, `cong`, `sym` and `trans`. Its parameters
are `A : CRing ℓ` and `K : KockLawvere A`. `SDG.Prelude` defines intensional
identity operations by matching on reflexivity. This declaration needs neither
cubical dimensions nor function extensionality. It preserves the proof-bearing
infinitesimal `D`; it does not quotient its proof components. Its interpretation
can use a smaller intensional fragment once the ring and KL hypotheses are
interpreted. It does not require making Kock's `--safe --without-K` source
cubical or claiming an unconditional smooth model.

The required dependent higher consumer remains exactly
[#316's frozen memo](dependent-higher-identity.md): `w`, `apd-η(h)` under both
substitutions, and `β⁻¹ · ap_T(h) · β = h`, with a nonzero second-identity
observer and erasure rejection. The existing Agda `FrozenMemo`, `HigherWitness`
and `Monodromy` files are reused. The source `K(ℤ,2)` construction uses more
library features than the generic memo. A separately constructed cubical
parameter with the required pointed observations may instantiate the generic
memo, but would not amount to interpreting that entire external HIT construction.

## Alternatives considered before selection

**Source results.** CCHM §§8.1–8.3 constructs presheaves on substitutions into
free De Morgan algebras, then dependent families with uniform composition.
Theorem 14 establishes basic fibrant constructor closure; Theorem 17 handles
Glue under fibrancy and equivalence data. Definition 18 classifies small
fibrant families over representables. Theorem 23 gives judgment soundness,
using the substitution/naturality lemmas. Its universe interpretation assumes
nested Grothendieck universes. Section 9 treats strict identity and HITs
separately. These are mathematical constructions, not a Lean implementation.
[CCHM v1](https://arxiv.org/html/1611.02108v1)

Orton–Pitts Figure 1 assumes interval/cofibrancy/strictness structure.
Theorem 8.4 and Corollary 8.5 validate it for qualifying presheaves using
small finite products, a nontrivial connection algebra, decidability and
universe lifting. Section 7 does not internally construct a generic fibrant
universe. The associated Agda artifact proves constructions in a metalanguage
with postulates, rewriting, `primTrustMe`, and an impredicative module using
`--type-in-type`; those cannot be copied as accepted Lean foundations.
[Paper v4](https://arxiv.org/pdf/1712.04864v4),
[CAM.21675 artifact](https://doi.org/10.17863/CAM.21675)

The Cartesian cubical construction's Theorem 2 uses a finite-product cube
category and suitable decidable cofibrations, including diagonals, to construct
universes of diagonal-Kan families with Π, Σ, paths and Glue. The inspected
Agda implementation assumes its universe and strictification foundations.
Its interval syntax does not directly supply the selected De Morgan connection
and reversal equations. A translation would be extra mathematics.
[Author manuscript](https://www.cs.cmu.edu/~rwh/papers/uniform/uniform.pdf),
[cart-cube pin](https://github.com/dlicata335/cart-cube/tree/f80af5cf6638c85ffda2397a8e097b3e9decac1b)

Kapulkin–Lumsdaine Theorem 2.3.4 constructs type structure on a universal
simplicial Kan fibration under an inaccessible-cardinal hypothesis; a smaller
inaccessible supplies an internal universe. The univalence results do not
validate Agda's dimension or primitive computation rules.
[Simplicial model v5](https://arxiv.org/pdf/1211.2851v5)

| Route | Local construction and reuse assessment |
| --- | --- |
| De Morgan presheaves, then explicit composition | Selected. The first source term directly uses its dimension algebra. Begin with concrete quotients/substitutions, then dependent presheaves and chosen uniform fillers. No foundational model field is accepted merely by declaring it. |
| Internal Orton–Pitts construction | Useful proof organization, but first needs a constructed ambient topos, interval/cofibrancy and strictness. It does not avoid the external classifier obligation. |
| Cartesian cubical model | A genuine alternative, with a different cofibration strategy. Extra connection/source interpretation work precedes the chosen source consumer; no demonstrated local cost saving justifies it here. |
| Simplicial Kan model | Useful higher semantics, but adds a cubical-source interpretation and size bookkeeping before direct compatibility. Not rejected as impossible. |
| HoTTLean generic machinery | Conditional semantic constructions may be reused after a declaration audit and version adaptation. The concrete groupoid instance has discrete hom identities and fails the retained second-identity observer. |
| Existing local groupoid / #322 strict 2-groupoid route | Keep as independent intensional interpretations. Neither is a shortcut proof of cubical primitive computation. Share proved categorical facts where hypotheses match. |

The tracked Lake manifest contains Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` and tooling, not an integrated cubical
model. The earlier Cubical research pin
`c37782bb4e382dc41035e0970409a0c17b55e6ce` differs from the supplied checkpoint
pin and must not replace it. HoTTLean
[`31133dd5b25226ea897f8aa5e2e43b61392459eb`](https://github.com/sinhp/HoTTLean/tree/31133dd5b25226ea897f8aa5e2e43b61392459eb)
targets Lean 4.25.0-rc2. Its normal/uniform Hurewicz construction is conditional;
its concrete `Groupoids/Id.lean` uses discrete hom groupoids. The syntax checker
also contains injectivity axioms, so no wholesale import is proposed.

No external mechanization was rebuilt in this comparison. Cubical's MIT license
has file-specific exceptions; HoTTLean is Apache-2.0; the Orton–Pitts archive
metadata specifies CC-BY. No license file was located in the inspected
Cartesian tree. Mathematical reconstruction needs provenance; copying code
also needs permission and dependency/trust review. This programme currently
imports none of these codebases.

## Declared calculus and capability matrix

The selected construction target is a universe-free dependent fragment with
terminal/context extension, simultaneous substitutions, Π, Σ, natural numbers,
De Morgan dimensions, restricted contexts/compatible systems, dependent Path,
generalized `transp`, `hcomp`, and a strict intensional Id interpretation.
Families and their universe levels are metatheoretic parameters. The strict Id
part is required by the frozen memo and cannot be replaced by Path-J with only
propositional reflexive computation. This is a target specification, not a list
of assumed fields advertised as a model.

The versioned Agda manual distinguishes `transp` from CCHM composition.
`transp A r a` requires `A` judgmentally constant under `r=1`, where it computes
as identity. Systems must agree on overlaps; `hcomp` requires its base to
match the tube on the face. Ordinary constant-family transport and Path-J
compute only up to paths in general. The interval belongs to `IUniv` and is
not itself required to be fibrant. These distinctions enter the interpretation
contract and rejection cases.
[Agda 2.8.0.2 cubical rules](https://agda.readthedocs.io/en/v2.8.0.2/language/cubical.html)

| Feature | First cube contraction | Frozen memo / witness | Construction obligation and current status |
| --- | --- | --- | --- |
| Dimension substitution, endpoints, connections, reversal | Connection and endpoints used | Required by chosen cubical semantics | Equational dimension presentation and cube category constructed in M1; semantic universal property/remaining rules are not claimed |
| Face restrictions and compatible systems | No partial system in term | Needed for fibrancy | Face lattice, endpoint reflection, restrictions and compatible gluing constructed in M3 foundation |
| Dependent contexts, Π, Σ, substitution | Function parameter and Nat recursion | Both substitutions and genuinely varying families | Families/sections and comprehension constructed in M2a; Π/Σ/Nat operations and coherent substitution comparisons constructed in M2b |
| Path abstraction/application and endpoints | Essential | Higher semantic observations | Dependent Path families, abstraction/application, endpoint rules and substitution isomorphisms constructed in M2b |
| Generalized transport and homogeneous composition | Not used by this declaration | Needed for general dependent higher interpretation | Uniform semantic filling, Sigma/Path/Pi closure and restricted-constancy transp constructed; source rules pending |
| Strict intensional Id, contextual J | Not used | Essential, arbitrary motives and finite tails | Construct strict Id and prove β/substitution, not native Lean Eq; pending |
| Nontrivial higher parameter, nonconstant family | Not witnessed by contraction | Essential | Construct cubical parameter and detector; reuse exact memo after rule soundness |
| Internal universes, Glue, univalence | Imported but not used by declaration slice | Used by external `HigherWitness` construction, not generic memo | Not advertised in selected fragment; broader source reuse requires classifier/Glue proofs |
| HITs, truncations, circle/EM construction | Imported but not used by declaration slice | External chosen witness/monodromy use them | Not advertised; interpreting those artifacts unchanged remains a separate coverage obligation |
| Crisp contexts, cohesive/modal geometry | Enclosing source flag only | Not in generic memo | Additional model required for geometric reuse; no cubical-only claim |
| Kock ring/KL hypotheses | Absent | Separate intensional consumer | Interpret parameters explicitly; construct ambient smooth model under #36/#100 for unconditional geometry |

Object equality and natural-transformation equations in the Lean metatheory may
use Lean `Eq`. Interpreted Path and Id inhabitants must live as semantic data
in `Type`, with a detector that survives both substitutions. Proof irrelevance
must not collapse those data. No host axiom, unsafe declaration, audit exception
or special equality reflection is permitted.

## Milestone graph and acceptance tests

All cubical milestones are owned by #321; #322 owns its separate intensional
route. Arrows describe actual construction dependencies, not blanket scheduling
gates.

```text
M1 dimension algebra/cubes ─→ M2 dependent presheaves/Path ─→ M3 fibrancy
                                                               │
                                                               ▼
                                                  M4 strict Id + rule soundness
                                                               │
                          M5 concrete higher parameter ────────┤
                                                               ▼
                                         M6 frozen dependent higher consumer
```

| Milestone | Constructed output and test owned by #321 |
| --- | --- |
| M1 | Dimension algebra, substitution identity/associativity, cube category and endpoint/connection maps. Reject Boolean collapse with `i ∧ ¬i ≠ 0`; retain a distinction between independent dimensions. |
| M2 | Actual dependent presheaf families, sections, reindexing and comprehension, Π/Σ/Nat and Path operations. Interpret the selected contraction derivation, including both endpoints and naturality, first at `n=1`, then arbitrary `n`. Establish typing/substitution/conversion for the admitted judgment fragment. |
| M3 | Construct uniform composition/filling and closure, then the exact `transp`/`hcomp` rules. Test two substitutions, full-face computation, compatible boundaries and rejection without restricted constancy. An arbitrary chosen filler without naturality does not pass. |
| M4 | Strict Id construction and all-motive contextual J with finite dependent tails, β and stability. Interpret the generic frozen memo derivation through those rules. Coordinate #315's author boundary; no demand to retrofit existing annotations first. |
| M5 | Concrete cubical higher type with a nonzero selected second identity, a pointed decoder/observer, and a genuinely nonconstant dependent family. Investigate a cubical nerve/abelian construction; prove the fibrancy and identity comparisons needed for this route. A disconnected two-loop record fails this milestone. |
| M6 | Apply the unchanged #316 memo under both substitutions, retain transported `apd-η(h)` type and observed conjugate, prove nonzero observation and erasure rejection. The higher adoption gate remains closed until this passes. |

M6 promises an interpretation of the selected `FrozenMemo` judgments and their
source derivations, followed by independently constructed semantic instances.
The acceptance artifact must connect those derivations to the interpreted
`w-twice`, `apd-twice` and `PathFamily.observation`, with their full dependent
types, rather than independently prove only equal target values. `HigherWitness`
and `Monodromy` are currently external evidence for the specification. Their
unchanged source interpretation is not promised by this universe-free fragment;
it requires the additional rules above or a separately proved translation.

M5 can begin once M1–M3 specify its semantic inputs. It does not wait wholesale
for #322, a compiler, #310 or finished external geometry. A useful #322 theorem
may shorten a cubical nerve construction only after proving the bridge.

Broader source coverage remains owned: #321 must construct universe/Glue/HIT
closure before claiming those operations or unchanged `HigherWitness` reuse.
#36/#100 owns realizing smooth scalars, KL and cohesive/crisp principles;
#310 owns its mathematical comparison. A compiler or scoped translator must
preserve the selected source judgments and conversion before an unchanged Agda
artifact can be reused. A handwritten Lean consequence, source checker receipt
or assumed semantic interface is not that translation.

Each formal milestone uses EDD, statement review, positive/dependent/rejection
cases, README's committed candidate build and exhaustive audit, then independent
Standards/Spec review. The initial selection and any limited model leave the
programme open. Missing rules will remain named with owners and discriminating
tests, rather than being silently removed from the selected contract.

## M1 construction record

[Dimensions.lean](../../SquareKit/Internal/Cubical/Dimensions.lean) defines raw
expressions and the generated bounded distributive De Morgan congruence.
Substitution preserves that congruence. Cube morphisms are actual quotients of
finite simultaneous substitutions; identity and composition are defined, and
the category laws follow from expression substitution. Finite ordinal contexts
choose names canonically; no equivalence with an arbitrary source-name syntax
is claimed yet.

The selected source's dimension boundaries are retained as
`face_zero_connection` and `face_one_connection`. `reversal_twice` checks the
involution equation after passage to cube morphisms. These are conversion
facts about dimension substitutions, not interpreted higher identity proofs.

[DimensionModels.lean](../../SquareKit/Internal/Cubical/DimensionModels.lean)
constructs a four-element algebra on Boolean pairs, with coordinatewise lattice
operations and negation exchanging and complementing coordinates. `Four.sound`
proves every generating conversion sound in that algebra, and `eval_subst`
connects evaluation to simultaneous substitution. `dimension_not_boolean`
rejects `i ∧ ¬i = 0`; `dimensions_not_kleene` additionally rejects the Kleene
inequality on independent dimensions. `connection_complement_not_zero` retains
the first rejection in the actual quotient hom-set. The finite observer
therefore checks the quotient's mathematical meaning rather than just comparing
raw constructors.

Statement review: the congruence has precisely structural congruence and
bounded distributive De Morgan generators, with no complement-disjointness or
excluded-middle generator. Quotient equality is metatheoretic equality of
substitutions. Arbitrary simultaneous substitutions, including repeated and
constant dimensions, are admitted. Soundness in the concrete four-element
algebra establishes a nontrivial instance; it does not establish fibrancy or
a nonzero second identity. Those remain M3/M5 obligations. The endpoint cases
were chosen from `contract-cube` before encoding; neither a Boolean interval
nor mere raw-term equality would satisfy the retained cases.

Focused builds of both modules pass. Both are imported by the public entrypoint
for exhaustive acceptance auditing. Full committed validation and independent
review evidence are retained with the milestone handoff. M1 does not complete
the selected calculus or the programme.

## M2a dependent presheaf comprehension

[Presheaf.lean](../../SquareKit/Internal/Cubical/Presheaf.lean) constructs
contexts as `Cubeᵒᵖ ⥤ Type u`, families as functors from Mathlib's category of
elements into `Type u`, and terms using Mathlib's coherent sections. Contexts
are contravariant on cubes; a family's map follows the corresponding arrow in
the category of elements. Reindexing composes with the substitution's actual
`mapElements` functor. Identity and repeated reindexing are proved equal,
including dependent term types.

Comprehension is constructed pointwise from dependent pairs, with restriction
using the family functor's map. `totalMap_ofHom` relates that operation to
arbitrary element-category arrows and proves identity/composition without
postulating a comprehension law. `projection`, `generic` and `pair` satisfy
both projection equations and `pair_eta`, recovering every map into
comprehension from its two components. `pair_reindex` proves stability under
substitution. The terminal singleton presheaf has a constructed unique map
from every context.

[The retained cases](../../Examples/CubicalPresheaf.lean) use a finite family
with fiber `Fin (n+1)` and its coherent last-element section. Substituting
successor after doubling maps the input `2` to index `5`; the term is `5` in
`Fin 6`, through the general repeated-substitution theorem. The same inputs
exercise pairing and the generic component. Fibers at `0` and `1` are not
equivalent by cardinality, rejecting a constant-fiber interpretation. Separately,
the represented interval and its coordinate section exercise actual cube
restriction: the two faces of the connection retain respectively the zero line
and the identity line in both components of the comprehension context.

Statement review: all families in the stated universe are admitted as functors,
not only the finite example. The section condition quantifies over every
category-of-elements arrow. Context, fiber and term sizes use one declared Lean
universe; no internal classifier or resizing is inferred. Metatheoretic equality
proves these structure laws but does not stand for an interpreted identity type.
The finite example varies its fiber with its base value; it is not the required
higher monodromy example. M2a alone supplies no Π/Σ/Nat/Path constructor soundness, fibrancy, transport
or J. The next checkpoint supplies constructor operations and the selected
source recursion; fibrancy and M3–M6 remain open.

## M2b constructor and source-recursion checkpoint

This checkpoint constructs Π, Σ, Nat and dependent Path operations, coherent
isomorphisms for their substitution comparisons, and a checked realization of
the selected contraction recursion. The model is presented as families and
sections with semantic conversion laws, not a whole-syntax soundness theorem.
M3–M6 remain open.

[TypeFormers.lean](../../SquareKit/Internal/Cubical/TypeFormers.lean) constructs
Σ from dependent pairs, including introduction, projections, β/η, and equality
of the reindexed family with the sum of reindexed constituents. A Π value gives
a result for every arrow out of the current generalized element and every
argument at its target. Its coherence law relates those results under further
restriction. This quantification constructs the presheaf dependent product;
pointwise set functions would omit it. Abstraction and application are coherent
sections and satisfy β/η. `piReindex` is a natural comparison with the product
after substitution; `lam_reindex` and `app_reindex` prove their commuting rules.
Its inverse and both inverse laws are constructed in
[Substitution.lean](../../SquareKit/Internal/Cubical/Substitution.lean).

[Naturals.lean](../../SquareKit/Internal/Cubical/Naturals.lean) uses the constant
natural-number family, lifted to the family universe. Dependent elimination
constructs values by recursion and proves restriction coherence by induction.
The motive is an arbitrary family over `Γ.Nat`, not a constant codomain.
`NatStepTerm` gives the successor-method judgment in context `Γ,n,b` with result
`B[n+1]`. Its conversions to and from `NatStep` are inverse, so the latter record
is a representation of a typed method, not an assumed eliminator. Zero and
successor computation and substitution stability are proved. The
[finite-fiber cases](../../Examples/CubicalTypeFormers.lean) abstract a function
with result `Fin (n+1)`, evaluate it at `3`, and separately construct its last
element by dependent recursion. `countedLast_is_last` proves agreement for every
`n` through the recursor's public successor equation.

[Interval.lean](../../SquareKit/Internal/Cubical/Interval.lean) constructs the
represented interval family, endpoints and meet, retaining their cube action.
[Paths.lean](../../SquareKit/Internal/Cubical/Paths.lean) takes coherent interval
functions whose two endpoints agree with the supplied dependent sections at
every restriction. Path abstraction/application satisfy β/η and the two endpoint
equations. `pathReindex` and `pathLam_reindex` supply a forward substitution
comparison and its abstraction equation. `pathReindexIso` constructs its inverse
and proves both inverse laws. These constructions assume no filler, `transp`,
`hcomp`, Path-J or strict Id.

The substitution inverse uses a constructed equivalence between arrows out of
a generalized element and underlying cube restrictions. Every such restriction
has a unique lifted target and element value. `substitutionArrowEquiv` therefore
makes the induced arrow map bijective even when the context substitution is not
injective. `piInverseElement` extends function values along that equivalence;
lifting two successive arrows proves coherence. The Path inverse retains both
endpoint conditions under the same lift. Identity and composition equations
for the forward comparisons, together with both inverse laws, provide coherent
substitution isomorphisms. Dependent function and interpreted Path roundtrips
are retained in the examples.

### Selected source derivation

The archived `Orbifolds.CubicalShells` source defines `Cube 0 X = X` and
`Cube (n+1) X = I → Cube n X`. Its contraction has zero body `refl` and successor
body `contract-cube n (c (i ∧ j)) j`. Here `j` is the path binder and `i` is the
outer cube-function binder. The checked interpretation fixes an arbitrary
presheaf `X` externally. It does not interpret the source's universe-polymorphic
binder as an internal universe or claim a whole-Agda syntax soundness theorem.

[CubeContraction.lean](../../SquareKit/Internal/Cubical/CubeContraction.lean)
represents an `n`-cube by its action on generalized `n`-tuples of interval values,
including all cube restrictions. `cubeZeroIso` and `cubeSuccessorIso` prove the
zero and successor identifications with the source's types. The interval
exponential has constructed abstraction/application with β/η; `cubeLam_pi` and
`cubeApp_pi` relate those operations to the dependent Π operations. The natural
coordinate-scaling construction `contractCube` supplies both endpoint proofs.
It is not the sole evidence for interpretation of the recursive source.

[SourceContraction.lean](../../SquareKit/Internal/Cubical/SourceContraction.lean)
provides the recursion bridge:

| Source judgment or conversion | Constructed interpretation and checked connection |
|---|---|
| Fixed parameter `X`; `n : Nat` | `methodFamily X` is a Nat-indexed family of global natural contraction operations. Each operation has context `(c,j)` and returns a complete `n`-cube. |
| Zero branch `refl` | `sourceZero` projects off `j`; `sourceZero_contract` connects it to the zero-dimensional coordinate construction. |
| Successor body with `c,j,i` | `sourceStepBody` applies the lower method to `c.apply (meet i j)` and `j`; naturality is proved using interval meet and function application. |
| Abstraction of `i` and successor cube conversion | `sourceStep` uses `cubeLam` and `cubeUncurry`. `sourceStepBody_contract` is proved through the exact recursive equation `contractCube_apply`; `sourceStep_contract` uses abstraction/application β/η and the currying inverse law. |
| Dependent recursion on `n` | `sourceRecursion` calls the constructed `natElim`. `interpretedContraction_zero` and `interpretedContraction_successor` use its public computation rules. |
| Realization and Path introduction | `sourceRecursion_at` proves realization at any base cube agrees with the closed operation. `interpretedContraction_eq` identifies the interpreted recursion with coordinate scaling. `interpretedContractionPath` then uses `pathLam`; its equality to `cubeContraction` is proved. |

The recursion motive above is a family of **global semantic operations**,
followed by realization at each cube and application to `c,j`. It is not an
internal universe of types. This bridge checks the selected recursive
characterization, binding order and conversions at a fixed presheaf parameter;
it does not extend the admitted fragment to arbitrary source type-level
recursion. The Π/Path stability isomorphisms are separately proved for all
modeled families, rather than inferred from this source example.

[The source cases](../../Examples/CubicalContraction.lean) reach the `n=1`
connection through `interpretedContraction_eq`. The result at two independent
dimension variables is the actual quotient morphism `Cube.connection`.
`line_not_constant_origin` rejects replacing the contraction path by equality
of the line with its constant origin, using the finite De Morgan soundness
model. The arbitrary-dimensional endpoint cases consume `pathApp_zero` and
`pathApp_one` on the interpreted recursion's Path term. Two arbitrary context
substitutions retain that full term through the existing substitution theorem.

Statement review distinguishes metatheoretic equality of natural transformations
from the constructed Path inhabitant. All restriction quantifiers are retained;
the interval is not a two-point set. The source case is not the mandatory
nonzero higher-identity consumer from M5/M6. Stable fibrancy, strict Id/J and the frozen memo interpretation remain
explicit obligations of #321. The constructor comparisons are coherent natural
isomorphisms; this checkpoint does not claim they are definitional equalities
of family representations or supply a separate strictification theorem for an
uninterpreted source syntax.

### M2b conversion contract and remaining rule soundness

The M2b conversion contract has two distinct parts. For terms already in
the same semantic family, the Π/Σ/Path β/η and Nat computation theorems prove
Lean equality of the constructed sections. For type formation under context
substitution, Π and Path use the chosen natural isomorphisms
`piReindexIso` and `pathReindexIso`; their forward maps obey identity and
composition, and both inverse laws are proved. The successor source cube type
also uses `cubeSuccessorIso`. These are explicit semantic comparisons, not
literal equality or definitional equality of the family representations.

Accordingly this is a **partial M2 milestone**, even though the constructor and
substitution operations and the selected recursive realization check. There is
no theorem interpreting every typing, substitution and judgmental-conversion
derivation of the advertised source fragment. The selected source bridge
checks the stated recursive characterization through the Nat recursor and
function/Path operations; it does not imply that general judgment theorem.

The #321 implementation owner must complete that rule layer before claiming
selected-fragment acceptance: either construct a split interpretation with the
required strict equalities, or define conversion by the stated comparisons and
prove source-rule soundness, including independence from conversion derivations
and compatibility with substitution. The present isomorphisms supply data for
that work; they are not a strictification proof. M4 must preserve this boundary:
strict Id, arbitrary-motive J and its computation/substitution rules must be
connected to the admitted source judgments. Metatheoretic equality of existing
sections cannot replace the required interpreted Id/J data or discharge the
frozen memo's strict identity rules. M6 still requires that source-rule bridge
alongside its constructed higher parameter and dependent observation.


## M2 normalization checkpoint: literal family conversion

This increment constructs equalities for Π/Path formation under arbitrary
context substitution. It preserves the existing guarded theory's interpretation
of equality as literal equality. It does not reinterpret that judgment as an
arbitrary isomorphism.

[Localization.lean](../../SquareKit/Internal/Cubical/Localization.lean) restricts
an element `x : Γ.Elements` along the category `Under x.obj` of arrows from its
underlying cube. This indexing category does not depend on the context values.
`localize_substitution` proves equality of the localized element diagrams after
substitution. `localize_forget` proves that forgetting an element arrow and
lifting its underlying cube arrow recovers its target diagram.

[LocalProducts.lean](../../SquareKit/Internal/Cubical/LocalProducts.lean)
represents a dependent function as a natural section of the localized display
map `Σ A B → A`. The base, total diagram, and projection commute with
substitution by equality, so their section types are equal. `localPiEquiv`
constructs both directions to the existing `PiElement` and proves both inverse
laws. Its reconstruction proves naturality for arbitrary dependent fibers;
it does not retain only closed values or endpoint samples.

[NormalizedProducts.lean](../../SquareKit/Internal/Cubical/NormalizedProducts.lean)
constructs the whole family, including its restriction action.
`normalizedPiIso` retains the old family in both directions, while
`normalizedPi_reindex` proves **equality of families**, including maps, under
arbitrary context substitution. These are different claims: the isomorphism
compares the old and new representations; the equality establishes stability
of the new representation.

[NormalizedPaths.lean](../../SquareKit/Internal/Cubical/NormalizedPaths.lean)
restricts the normalized product to the image of endpoint-constrained old Path
elements. Membership contains only a proposition. Reconstruction uses the
underlying product and proves its endpoints from membership; it does not choose
an arbitrary witness. `normalizedPathIso` proves both inverse laws, and
`normalizedPath_reindex` proves whole-family equality under substitution.
Thus all old paths, their restriction values, and endpoint constraints survive.

[Conversion.lean](../../SquareKit/Internal/Cubical/Conversion.lean) transports
sections along family equality. It proves identity, composition, independence
from the proof of that equality, and compatibility with context substitution.
Normalized Π abstraction/application retain β/η and commute with substitution
using this equality transport.
[PathConversion.lean](../../SquareKit/Internal/Cubical/PathConversion.lean)
provides the corresponding Path β/η, endpoint, and substitution laws. The old
Σ and Nat representations already have literal formation/substitution laws;
they need no replacement in this increment.

[The dependent example](../../Examples/CubicalConversion.lean) has domain
`Fin(n+1)` and result `Fin(a.val+1)`. Successor substitution changes the context
index; literal conversion followed by application at `n=2, a=2` gives the last
element of `Fin 3`. A second, doubling substitution consumes the conversion
transport law. [The Path example](../../Examples/CubicalPathConversion.lean)
selects the represented line in the already interpreted recursive contraction.
After literal family conversion, application still computes the two-variable
connection. Its endpoints are proved distinct through the earlier finite
De Morgan discriminator, excluding replacement by a constant path.

Statement review distinguishes proof independence for **semantic equality
transport** from independence of arbitrary **source conversion derivations**.
The former is now proved; the latter requires the general source-derivation
interpreter, which is still absent. This is therefore another partial M2
checkpoint. It supplies strictly stable Π/Path representations and checked
rules for their semantic operations, not a theorem interpreting every source
typing/substitution/conversion derivation. The successor cube comparison and
fixed-external-`X` recursion bridge retain their previously stated scope.
The #321 implementation owner still owes that general interpreter and its rule
soundness before M2 acceptance. M3 uniform fibrancy and exact primitive side
conditions, M4 strict Id/J, and M5/M6's higher parameter and exact frozen memo
consumer remain required in dependency order. No checkpoint closes #321.

## Source-rule construction in progress

The structural and Π fragment now has an independently specified guarded
source theory and a constructed tagged presheaf algebra in
[Judgments](../../SquareKit/Internal/Cubical/Judgments/ProductsTheory.lean).
The structural rules reuse the annotation-free comprehension signature.
The Π rules specify formation, abstraction, generic application, β/η, and
substitution, with explicit typing premises. Their validity proofs recover
arbitrary dependent families and sections from those premises. Semantic
validity is not a premise of the source rules.

`interpret` handles arbitrary derivations of this fragment. `typed_result`
recovers a coherent section in the declared family. `familyEquality` extracts
literal family equality from a derived source equality, and
`conversion_independent` proves that two such derivations transport every
section identically. Schematic substitution of raw names is separate from
the validated object-context operations `subTy` and `subTm`.

[Source examples](../../Examples/CubicalSourceProducts.lean) derive Π β and
formation/substitution as source judgments, then interpret those derivations.
The varying `Fin(n+1)`/`Fin(a.val+1)` example uses the resulting family equality
to transport a section after successor substitution. A rejection example
proves that a context tag cannot serve as a function type in a closed typing
derivation. These checks cover the structural and Π fragment only.

The dependent sum extension constructs natural packing/unpacking maps between
`Γ.A.B` and `Γ.(Σ A B)`, proves both inverse laws, and validates guarded
formation, packing, unpacking, cancellation, formation/substitution, and
arbitrary-motive elimination with its β rule.
The semantic eliminator accepts an arbitrary motive over the sum context.
[Its example](../../Examples/CubicalSourceSums.lean) derives cancellation in
the source theory and uses an interpreted elimination β derivation to recover
a body in a motive whose fiber depends on the second component.
Packing and unpacking now have validated source substitution rules. The Nat extension
validates formation, zero, successor, arbitrary-motive elimination, and both
computation rules. Its successor method is a typed section in `Γ,n,b` with
result `B(n+1)`. [The finite-motive example](../../Examples/CubicalSourceNaturals.lean)
interprets the source successor derivation and evaluates it at two, retaining
the `Fin(n+1)` result family. Nat constructor substitution is also validated, including both lifted
binders in the successor method. The interval extension evaluates arbitrary
De Morgan expressions by actual cube substitutions and validates typing,
syntactic conversion, dimension composition, and context substitution.
[Its source example](../../Examples/CubicalSourceIntervals.lean) interprets
double reversal at the generic interval variable. The dependent Path extension validates formation, abstraction with both
endpoint equations, generic application, β/η, endpoints, and all constructor
substitution rules using literal family equality.
[The source endpoint example](../../Examples/CubicalSourcePaths.lean) interprets
a source derivation on the nonconstant contraction path and retains distinct
selected endpoints.

[The recursive source example](../../Examples/CubicalSourceContraction.lean)
now interprets guarded Nat zero/successor derivations at `methodFamily X`.
The typing premises are proved for the constructed zero and successor sections.
Their interpreted computation equations imply the unique recursive operation
`contractCube X n` for every `n`.
[The binding interface](../../SquareKit/Internal/Cubical/SourceBinding.lean)
checks the successor body through normalized Π application and abstraction:
`c(i ∧ j)` uses the De Morgan expression evaluator and a paired context
substitution; the recursive parameter takes that cube argument, then `j`.
The first application uses literal Π substitution conversion before the second.
`sourceStep_normalized` identifies the resulting abstraction over `i` with
the successor operation through the proved cube curry/uncurry comparison.
This gives a checked recursive-characterization bridge, including the first
interval body, rather than assigning an unexplained successor operation to the
Nat rule.

The boundary is fixed external `X`, with recursion in a family of global natural
operations. The guarded source judgment interpreter covers the independently
specified structural, Π, Σ, Nat, De Morgan, and dependent Path schemas above.
It interprets schematic derivation substitution and the explicit object-context
substitution rules separately. It interprets conversion by literal tagged
semantic equality and transports sections independently of the equality proof.
The archived binding expression is compared with these constructed operations;
there is no Agda parser, internal universe interpretation, or claim that cube
representation isomorphisms themselves are source judgmental equality. Extending
this source interface with the remaining selected transport/composition and
strict identity rules is still required. M3–M6 retain all obligations listed
above, including stable fibrancy, strict Id/J and the exact frozen memo with a
dependent higher observer. This checkpoint does not complete #321.


## M3 foundation: faces, systems and discrete filling

The face construction follows CCHM §§4.1 and 8.1: paired endpoint generators
are disjoint; finite meets and joins describe faces; cube substitutions act on
them. [CCHM v1](https://arxiv.org/html/1611.02108v1)
[Faces.lean](../../SquareKit/Internal/Cubical/Faces.lean) represents faces by
upward-closed Boolean predicates on finite partial endpoint assignments.
The unspecified value retains the interior: the interval boundary is not the
full face. This auxiliary ternary evaluation does not change the free De Morgan
dimension quotient or its four-valued rejection tests.
[FaceFormulas.lean](../../SquareKit/Internal/Cubical/FaceFormulas.lean) constructs
a finite endpoint formula for every such predicate and proves that its evaluation
recovers the predicate. An abstract free-lattice universal property is not yet
proved; the operational representation, generating formulas and substitution
laws are checked.

[FaceEndpoints.lean](../../SquareKit/Internal/Cubical/FaceEndpoints.lean) proves
that a full endpoint face means literal equality to the corresponding dimension
endpoint. The reflection proof returns a derivation in `Expr.Conv`; it does not
infer dimension equality from arbitrary equality of ternary valuations.
[FaceContexts.lean](../../SquareKit/Internal/Cubical/FaceContexts.lean) constructs
the face presheaf, natural face maps, restricted contexts and their inclusions.
[PartialSections.lean](../../SquareKit/Internal/Cubical/PartialSections.lean)
identifies partial sections with actual sections of restricted families, glues
two sections that agree on their overlap, and proves substitution stability.
[The face examples](../../Examples/CubicalFaces.lean) retain the generic
interior, both endpoint restrictions and their union, and reject conflicting
values on a full overlap.

The first filling instance is constructed for discrete coefficients, then for
families `S(q)` selected by an arbitrary natural index section `q`.
[IntervalExtension.lean](../../SquareKit/Internal/Cubical/IntervalExtension.lean)
constructs a fresh dimension over each generalized base element and its
specializations. Naturality along these maps proves that a section with discrete
coefficients is constant along the added interval, including on arbitrary faces
pulled back from the base. [DiscreteFilling.lean](../../SquareKit/Internal/Cubical/DiscreteFilling.lean)
and [DiscreteFamilies.lean](../../SquareKit/Internal/Cubical/DiscreteFamilies.lean)
use that result to construct a filler from the starting cap and prove agreement
with the entire compatible tube. Its far endpoint supplies homogeneous
composition; filling and composition commute with arbitrary substitution.
[The dependent example](../../Examples/CubicalDiscreteFilling.lean) retains
`Fin(n+1)` fibers, computes `5 : Fin 6` after two nonidentity substitutions, and
rejects an incompatible starting cap. The fibers at zero and one are proved
inequivalent.

This is a partial M3 construction. It does not supply a general fibrant-family
model or closure under Π, Σ and dependent Path, and it does not yet interpret
the guarded source `transp`/`hcomp` rules. Generalized transport still needs the
exact restricted-constancy side condition and its computation at `r=1`.
The discrete filler is not the nonzero higher instance required by M5.
Strict Id/J, the dependent higher parameter and the unchanged frozen memo in
M4–M6 remain mandatory. No partial model is offered as completion of #321.

## Representation-law transport (#334)

The pinned Mathlib already supplies `Functor.copyObj` and `Functor.isoCopyObj`
in `Mathlib/CategoryTheory/NatIso.lean`. Given an existing functor and a
pointwise isomorphism to a new object presentation, these construct the new
maps by conjugation and prove the functor laws and natural isomorphism.
`normalizedPi` and `normalizedPath` now use these constructors directly.
Products reuse the existing `localPiEquiv`; paths use `localPathEquiv`, whose
maps retain the endpoint-constrained subtype and whose inverse laws reuse the
existing round-trip results.

Previously each presentation supplied identity and composition proofs, two
naturality proofs, and two inverse proofs at the functor level. Both callers
now supply only their pointwise equivalence. Its inverse laws remain necessary;
no final functor law or additional adapter hypothesis has been moved into the
caller interface. The original native facades and term operations remain.

This transport does not prove strict substitution compatibility. The separate
`toLocal_substitution` and `pathToLocal_substitution` proofs still establish
compatibility of the chosen representations with the original substitution
comparisons. `normalizedPi_reindex` and `normalizedPath_reindex` retain their
original hypotheses and proofs. Their term conversion and source soundness
consumers continue to use those literal equalities.

`Examples/CubicalPresentationTransport.lean` checks identity and sequential
presentation changes through the reused Mathlib constructor. A Boolean diagram
on the ordered naturals supplies a nonidentity representation change: its map
from 0 to 1 changes from identity to negation. The changed diagram does not
agree with the old presentation even after the identity substitution. Thus
arbitrary pointwise isomorphisms cannot justify a claim of strict substitution
compatibility. Existing dependent Pi examples retain their two substitutions;
the Path example checks a further arbitrary substitution after selecting the
nonconstant line, while its existing endpoint and connection observations
remain. Source dimension equality is unchanged, including the Boolean and
Kleene counterexamples.

These changes discharge representation-law duplication only. General fibrant
closure, strict Id/J, the higher type, and the frozen dependent memo remain
construction obligations under #321.


## M3 dependent filling and restricted transport

`Filling` separates chosen operations from their correctness and uniformity
laws. It supplies a section filling an open box over each context path, with
an arbitrary actual face and compatible starting cap. `Filling.Lawful` requires
agreement with that cap and the entire tube, and commutation with arbitrary
context substitutions. This uses whole fillers as primitive data. CCHM
Definition 13 instead specifies far-face composition; the connection
construction below now derives whole filling from it.

`discreteFilling` constructs an instance for every `S(q)`, with a natural
constant-coefficient index `q`. Its proof now allows the index to be supplied
over the entire interval extension. Interval rigidity identifies its values
with those on the starting face; the filler transports the cap through that
identification. The operation and its laws are proved, not supplied as new
model fields. `Examples/CubicalDependentFilling.lean` recovers the earlier
selected filler and the result `5 : Fin 6` after two substitutions.

`sigmaFilling` constructs dependent sum closure. It first fills the first
component, then fills the second family along that selected first filler.
Partial second projections are sections over the actual restricted context;
their types follow the first component. Both cap/tube agreement and uniformity
are proved. The substitution argument transports the first filler together
with its correctness proof before applying uniformity of the second filler.
`Examples/CubicalSumFilling.lean` retains the selected pair
`(6, 6 : Fin 7)` after two substitutions and rejects erasing its second
component. The construction applies to arbitrary lawful input fillings, not
just these discrete instances.

`Filling.comp` observes the far endpoint, and `Filling.hcomp` specializes it
to a family pulled back from the base. Their whole-face computation and
substitution laws follow from the chosen filler. Generalized transport uses
`RestrictedConstancy`: equality of the family and its starting-endpoint
pullback over the face-restricted interval context. This equality constructs
the constant tube used by `Filling.transp`. The full-face computation theorem
identifies the endpoint fibers and proves equality after that explicit cast.
Constancy, the tube, and transport all commute with substitution. A source
parameter `r` selects the face `Cofibration.endpoint r true`; this is the
semantic boundary corresponding to Agda's `r=1` side condition.

The transport examples retain the varying finite result after two
substitutions. A second family has an inhabitant at interval zero and none at
interval one. Lean proves that this family cannot satisfy full-face
constancy. This rejects omitting the transport side condition; it does not
claim that the counterexample family is fibrant. Empty-face transport is not
assumed to compute as identity in every constant family.

These are semantic constructions. The guarded source interpretation still
needs chosen filling data with stable substitution, Pi and Path filling
closure, and the admitted primitive computation rules. Existence of some
filler would not justify picking unrelated fillers after substitution. Strict
Id and finite-tail J, the nonzero higher parameter, and the exact frozen memo
remain required by M4–M6. The source Agda artifact is not reinterpreted merely
by these semantic operations.

Primary rule boundary: [Agda 2.8.0 transport documentation](https://agda.readthedocs.io/en/v2.8.0/language/cubical.html#transport)
and [CCHM v1 Definition 13](https://arxiv.org/html/1611.02108v1).


## M3 dependent Path filling

`pathFilling` constructs lawful filling of `path B a₀ a₁` from lawful filling
of `B`. It exchanges the filling and path coordinates, evaluates the original
partial paths, and adjoins both path endpoint faces to the tube. The endpoint
sections are actual sections of the restricted family. Compatibility follows
from the original path endpoint equations; the two opposing endpoint faces
are disjoint. Gluing, endpoint restriction, and coordinate exchange commute
with substitution.

The body filler therefore keeps both path endpoints throughout the filling
dimension. Path abstraction returns its result through the full
`pathReindexIso`; no restriction values are omitted. The starting-cap law,
agreement with the original tube, and uniformity under arbitrary substitutions
are proved. The callers supply only the existing lawful body filler and the
two endpoint terms. The closure does not request the resulting path laws as
additional inputs.

`Examples/CubicalPathFilling.lean` uses the constructed discrete dependent
body family `Fin(n+1)`. Even with an empty original tube, the added endpoint
faces retain the selected path. The checked instance commutes with two
substitutions, yields `5 : Fin 6` at a free interval coordinate, and rejects
erasure to zero. This is a dependent discrete specialization of the general
closure theorem, not the nontrivial higher witness required by M5.

The construction follows the Path case of
[CCHM v1 section 4.5](https://arxiv.org/html/1611.02108v1). Pi filling, the
stable chosen-filling source interpretation, strict Id/J, and the exact higher
memo remain pending. The following construction supplies the shared
connection argument for Pi closure.


## M3 composition supplies whole filling

`Composition` stores only far-face composition, with boundary agreement and
substitution uniformity in a separate `Lawful` proposition. `Filling.toComposition`
observes the far face. Conversely, `Composition.toFilling` implements the
connection construction of [CCHM v1 section 4.4](https://arxiv.org/html/1611.02108v1):
replace the filling coordinate `i` by `i ∧ j`, add the face `i = 0`, and compose
in `j`. The added face carries the original cap. `ScaledBox` proves agreement
on overlaps and retains the dependent fibers through endpoint sections.

`Composition.toFilling_lawful` proves the original cap equation, agreement with
the entire original tube, and uniformity under arbitrary context substitution.
Both directions therefore construct lawful operations. This does not claim
that the conversions are inverse on selected operations: an arbitrary filler
may contain choices beyond its far face, and no such round-trip law is used.

`Examples.CubicalCompositionFilling` reconstructs a filler for `Fin(n+1)` from
its endpoint composition. With an empty original tube, the resulting section
retains the selected cap, commutes with two substitutions, and yields
`5 : Fin 6` at a free interval coordinate. Erasure to zero is rejected. This
checks a satisfiable instance of the construction; Pi closure and the remaining
source and higher-client obligations are still pending.


## M3 dependent function filling

`FunctionComposition` constructs composition for dependent functions. It uses
`Filling.backwards` to extend the generic far-endpoint argument, applies the
original function tube and cap along that extension, and composes the dependent
result. Interval reversal preserves dimension substitution and interchanges
endpoints. The argument at the far endpoint is exactly the supplied argument;
no regularity assumption on empty-face transport is needed. This follows the
function construction in [CCHM v1 section 4.5](https://arxiv.org/html/1611.02108v1).

`piComposition_lawful` proves agreement with the original tube and arbitrary
substitution uniformity. `piFilling` then uses the already constructed
composition-to-filling operation. Its callers provide lawful fillers for the
domain and dependent result family; the resulting function laws are derived.
The proof retains the generic arguments at every cube restriction through the
full dependent-product substitution isomorphism.

`Examples.CubicalFunctionFilling` instantiates the construction with a natural
argument and result `Fin(argument+1)`. The filled function retains its selected
last element, including `6 : Fin 7`, after two substitutions. The negative case
rejects erasing that result. Statement review checks the universal boundary and
substitution quantifiers, the genuinely dependent result family, and the
constructed lawful inputs. This completes the Pi closure obligation, while
source `hcomp`/`transp`, strict Id/J, and the higher memo remain open.

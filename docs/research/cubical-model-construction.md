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
| Face restrictions and compatible systems | No partial system in term | Needed for fibrancy | Construct face lattice/restriction semantics; pending |
| Dependent contexts, Π, Σ, substitution | Function parameter and Nat recursion | Both substitutions and genuinely varying families | Families/sections, reindexing and comprehension constructed in M2a; constructor closure remains M2b |
| Path abstraction/application and endpoints | Essential | Higher semantic observations | Construct Path families and conversion interpretation; pending |
| Generalized transport and homogeneous composition | Not used by this declaration | Needed for general dependent higher interpretation | Construct uniform operations with side conditions and boundaries; pending |
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
higher monodromy example. M2a supplies no Π/Σ/Nat/Path constructor soundness,
fibrancy, transport or J. M2b, M3–M6 and the source-derivation interpretation
therefore remain open.

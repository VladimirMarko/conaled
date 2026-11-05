# Strict two-groupoid construction checkpoint

These are construction checkpoints for [#322](https://github.com/VladimirMarko/conaled/issues/322).
The dependent higher adoption gate remains closed. The
[frozen test](dependent-higher-identity.md) and its memo are unchanged.

`SquareKit.Internal.PathTransport.TwoGroupoidPath` constructs the concrete
total-space discriminator. `Base` reuses the existing Mathlib bicategory
double delooping at `Multiplicative ℤ`. The path fiber is the one-object
integer groupoid. `fiberAction m` is a natural transformation of its identity
functor, preserving zero and addition.

The total space has one object, integer arrows, and cells retaining an integer
base component with boundary `a = b + m`. `Cell.fiber_boundary` connects this
equation to composition with the actual fiber transformation. The hom-category
is a groupoid, the total bicategory is strict, and integer negation gives
strict inverses for its arrows. Whiskering retains the base component.
All bicategory laws, including interchange, are proved. Parallel cells in
this particular total space are unique because their base component must be
`a - b`; this does not identify the distinct second identities in the base.
The integer hom-groupoid instance is scoped to avoid assigning that category
structure to ordinary integer clients globally.

`coherentContraction` is a Mathlib strong transformation from the identity
endofunctor to the constant-zero endofunctor. Its naturality comparison has
base component `a`. The unit, composition and 2-cell naturality pastings are
equalities of actual cells. The comparison is invertible, so its reverse
orientation is available without claiming strict naturality. A strict
contraction with any component `c` would require `c = a + c` for every integer
`a`. `no_strict_contraction` refutes this using `a = 1`.

This checkpoint constructs the concrete total bicategory directly. It has not
yet constructed a general higher-family interface or a Grothendieck operation
whose specialization produces that bicategory. The fiber action and boundary
connection constrain that next construction; they do not replace it.

## General hom-categories and reindexing

`TwoGroupoidHom` now constructs the hom-category for extension endpoints from
an arbitrary category `C`, strict bicategory `B`, evaluation functor `E : C ⥤ B`,
and target object `b`. Objects are pairs `(c,f)` with `f : E(c) → b`.
An arrow consists of `α : c → d` and a genuine fiber 2-cell
`ρ : f ⇒ E(α) · g`. In its intended application, `C` is a base hom-category,
so these objects and arrows are the total context's 1-cells and 2-cells.

The construction restricts bicategorical Yoneda along `E` and uses Mathlib's
contravariant Grothendieck construction. That construction can be reused for
each hom-category even though its locally discrete base prevents directly
using it as the whole higher context extension. Reindexing along any functor
`D ⥤ C` preserves the fiber cell, and its identity and composition laws are
proved as equalities of functors. When `C` is groupoidal and every hom-category
of `B` is groupoidal, the total hom-category is groupoidal. The inverse is
constructed from the inverse base cell, strict base cancellation and the
whiskered inverse fiber cell; both inverse equations are proved.

`StrictTwoTransformation.Trans` supplies the next family-action component:
a strict natural transformation between strict higher functors, with its
arrow equation and fiber 2-cell naturality. Its conversion to a Mathlib strong
transformation derives the unit and composition coherences. These are
structural transformation laws, not assumed elimination laws. The integer
action gives a concrete inhabitant with its component preserved by conversion.

`Examples.TwoGroupoidHom` connects the integer-boundary cells to the general
construction by mutually inverse encoding and decoding. A separate example
uses `B²ℤ` as the fiber and a discrete base. Its integer-one fiber 2-cell is
distinguished from zero, rejecting a general locally discrete fiber shortcut.
The reindexing and inverse cases consume the generic construction's theorems.
No third cell data is introduced at this layer; equalities establish the
ordinary hom-category laws. This is not yet a proof that all dependent type
constructors preserve the finite-dimensional restriction.

## Statement review and retained cases

Every new cell operation preserves its stated boundary. Equality of cells
uses uniqueness after retaining the base component, rather than erasing it.
`Cell.base_eq` quantifies over every cell and derives the forced difference
from its boundary. `comparison` supplies such a cell for every pair of
integers, preventing a vacuous uniqueness argument. No assumptions about
contextual J or general family closure occur in these proofs.

The four named results in `Examples.TwoGroupoidPath` check the oriented
calculation `3 = -2 + 5`, the integer-one component of the actual strong
transformation, rejection of base-component erasure, and failure of the
strict shortcut for an arbitrary contraction component. They consume the
public comparison, component and rejection results.

The strict-contraction failure is mathematical. Initial Lean failures while
constructing the checkpoint concerned alias reduction for integer arithmetic,
category instance inference and explicitly typing categorical composition;
they did not show a failure of finite-dimensional closure. Those errors were
resolved without changing the independently chosen boundary or contraction.

For the general layer, statement review checked the direction of the
contravariant Grothendieck boundary and inverse pasting, arbitrary functor
quantification in reindexing, and both input hypotheses of groupoid closure.
The generic layer does not assume locally discrete fibers. Its positive
integer fiber case witnesses that distinction. Encoding and decoding recover
the complete concrete cells, including their base components; equality of
decoded labels alone is not used as a claim of a general extension equivalence.

## Strict transformation composition and evaluation

`StrictTwoTransformation` now constructs identity and composition of strict
transformations and derives the category laws from equality of components.
Composition's 2-cell naturality follows by pasting Mathlib strong
transformations and reducing the strict associators. The category retains
arbitrary target 2-cells through the naturality equation; it does not require
a locally discrete target. Evaluation at a fiber object is a functor into the
target fiber, and a fiber arrow induces a natural transformation between the
two evaluation functors.

`integerAction` supplies a functor from the integer base hom-groupoid into
this category of strict higher functors. `integerTrans_comp` proves that
composition adds the integer components. `integerAction_evaluation` identifies
its evaluated functor with the independently defined path evaluation used
by the general hom construction. Thus the nonzero base action comes from
higher transformations, not just a separately supplied ordinary functor.

Statement review checked arbitrary strict source and target bicategories,
component equality versus equality of target 2-cells, and the direction of
evaluation naturality. The integer case proves the action laws without an
assumed eliminator or model law. An initial specialization failed because
`SingleObj` composition reverses multiplication order. The corrected proof
uses commutativity of integer addition explicitly; the general composition
construction assumes no commutativity. Earlier proof-elaboration failures
needed expansion of Mathlib's strong-transformation constructors and strict
unitors. They did not change the mathematical statements.

This supplies the transformation category and evaluation needed for the next
family layer. It does not yet impose or construct horizontal family action,
assemble total 1-arrow composition, or establish contextual elimination.

## General higher-family target and extension operations

`StrictTwoCategory` constructs the strict 2-category of strict 2-categories,
strict higher functors and strict transformations. Left and right whiskering
retain the 2-cell naturality equation; interchange uses transformation
naturality, and the pentagon and triangle are proved. The coherence
isomorphisms of a strict higher functor are determined by its underlying
action. No elimination or model law is introduced as a field.

`TwoFamily.Family` is a strict functor into this constructed target. Its
base 2-cell action therefore has vertical and horizontal laws. Evaluation
constructs each extension hom-category from the previous Grothendieck layer.
The extension objects, identity and composition form an ordinary category;
its laws reuse Mathlib's ordinary Grothendieck construction by an injective
map on arrows. This reuse is limited to laws of total 1-arrows. The extension
hom-categories still retain their genuine fiber 2-cells. Both total whiskering
operations are constructed with explicit object boundaries and naturality.
Their complete bicategory coherence laws remain to be proved.

`Examples.TwoFamily.pathFamily` supplies the integer path family with all
horizontal action laws. Its cells retain the original boundary, general
extension composition adds integers, and both whiskerings preserve the
integer-one base component. This connects the original discriminator to the
general family interface, without claiming that the whole memo is interpreted.

Statement review checked that the generic target admits non-discrete fiber
2-cells, that transport composition acts on the earlier fiber arrow, and that
both total whiskerings use the supplied fiber 2-cell with its typed boundary.
Proof-elaboration failures required explicit component rewrites for transported
strict-functor equalities. They did not justify replacing fiber 2-cells by host
equality. The finite groupoid restriction, general section/identity families
and contextual J still need construction and closure proofs.

`TwoFamilyReindex` additionally constructs the total reindexing functor and
its exact projection equation. When base and fiber 1-arrows are strictly
invertible, the total 1-arrows are strictly invertible, using Mathlib's actual
Grothendieck isomorphism construction. Locally groupoidal bases and fibers
also give groupoidal total hom-categories. The integer specialization applies
the derived inverse and retains the selected arrow under identity substitution.
These closure results concern extension only, not yet Sigma or open identity.

`TwoIdentityTransport` constructs the hom-groupoid transport functor,
inverse endpoint mates, and the natural transformation obtained from two
endpoint comparison cells and a strict higher transformation. Naturality at
every original fiber 2-cell follows from that transformation's 2-cell law
and Mathlib's whiskering/associator natural transformations. Its identity law
is proved. A strict 2-functor embeds ordinary categories in the higher-family
target using locally discrete 2-categories, preserving all ordinary arrows.

The double-delooping examples retain an arbitrary integer fiber cell through
hom transport and compute the endpoint comparison as `n - m`. The embedded
identity fiber retains the same integer arrow. Statement review distinguishes
this locally discrete identity fiber from erasure of the original fiber's
2-cells: those 2-cells become its 1-arrows. The generic endpoint comparison now preserves vertical composition. Strict
inverse 1-arrows supply constructed adjunctions. The inverse endpoint mate
is proved equal to Mathlib's mate correspondence, so `mateEquiv_vcomp`
proves its pasting law. Two naturality squares and interchange then prove
`homComparison_comp`. The integer example applies the general mate-pasting
law to arbitrary integer cells. Statement review checks that the hypotheses
retain arbitrary locally groupoidal fiber 2-cells and that the comparison
law uses the pasted endpoint cells, not equality of those cells.

The earlier failed direct simplification is retained in orchestration evidence.
Its mate and interchange obligations are now discharged; horizontal compatibility of the comparison with transport composition,
substitution and assembly into the full open identity family still remain.
`homTransport_comp` proves composition of the transport functors themselves,
including their maps on genuine 2-cells; `homTransport_id` proves their unit
law. The integer specialization applies the general functor composition law.

`TwoFamilyEndpoints` constructs the product of each fiber with itself and its
full higher action. It commutes with reindexing and preserves strict and local
groupoid structure. The examples retain the selected base integer in both
endpoints and retain two independent integer fiber 2-cells. Statement review
checks that this is an endpoint context family, not yet its identity family or
a proof of Sigma closure. The focused 857-target endpoint build and 568-root,
15-module proof audit pass, with only the three permitted axioms.

The endpoint family also has diagonal and two projection transformations;
composing the diagonal with either projection is the identity transformation.
`TwoOpenIdentity` constructs the actual ordinary functor from the total
endpoint context to hom-categories, with proved identity and composition
laws. It assigns a natural hom comparison to every genuine total 2-cell.
The integer example computes its action on the selected path `k` under
endpoint arrows `m,n` as `-m + k + n`, through this general context functor.

Statement review separates this constructed ordinary functor and its 2-cell
operation from the still-pending full higher-family laws. It does not yet
supply reflexivity, contraction or J. Focused validation passes 859 build
targets and the 621-root, 17-module audit, with only the permitted axioms.

The independent construction of `TwoFamilyCoherence` now supplies actual
`Bicategory` and `Strict` instances for every total family. All unit,
associativity and interchange laws are proved from the input family. The
non-discrete integer-fiber example applies interchange through that instance.
`TwoFamilyHigher` supplies the strict higher projection and the local groupoid
and reindexed-fiber closure instances. The integrated focused audit passes
740 declarations in 23 modules.

`TwoFamilyMap` constructs the ordinary total functor induced by an arbitrary
strong family transformation, its genuine 2-cell operation and identity law.
The vertical composition law is now proved, yielding a functor on every
complete hom-category. Its proof uses the naturality of the strong comparison,
not subsingleton elimination of fiber 2-cells. The checked integer-path example
specializes the law to two arbitrary consecutive comparisons. Statement review:
`map₂_comp` quantifies over every strong transformation and every composable pair
of total cells; no identity-comparison hypothesis restricts it. The auxiliary
conjugation lemma changes only equal typed whiskering boundaries.

The focused `Examples.TwoFamilyMap` build passes 852 targets. The corresponding
focused audit passes 745 kernel-safe declarations (570 theorem declarations) in
23 project modules, with only the three permitted foundational axioms. The
failed cast-heavy draft remains in the orchestration evidence; replacing its
implicit dependent boundaries with an explicit typed goal allowed the same
mathematical pasting proof to check. Both horizontal compatibility laws are now proved. `StrongMap.toHigher` is an
actual strict pseudofunctor, constructed from the arbitrary strong comparison;
right whiskering uses its full 2-cell naturality. The universal-family example
checks that this higher map preserves every selected integer fiber cell.

`reindexHigher` now supplies the complete strict substitution functor, with an
exact projection equation. Its nested-extension example uses projection as the
substitution and preserves distinct integer cells and both whiskerings.

`Section` uses a strict higher lift into the total context over identity. It is
not restricted to a transformation out of a terminal family: that shortcut
would force equality in place of a general section's genuine fiber 2-cell.
`variableSection` constructs the generic variable in the projected family;
its two-dimensional component is the supplied fiber cell itself. The checked
integer example distinguishes cells 1 and 0 through this section.
Statement review: the section record defines structural data, while the generic
section and the total-map/reindex laws are constructed. No field assumes J,
contraction, or interpretation of the frozen memo. General section substitution,
the complete open identity family and contextual J remain pending.
The integrated focused audit passes 816 kernel-safe declarations (615 theorem
declarations) in 27 project modules, with only the three permitted axioms.

## Remaining construction

1. Specify the general small strict 2-groupoids and higher family collection,
   reusing Mathlib bicategories and strict functors where appropriate. Families
   must retain transformation action on base 2-cells; sections need their own
   coherent 2-cell data. Construct reindexing and Grothendieck extension,
   then connect this concrete example to that operation. The hom-category,
   its strict reindexing and vertical inverses are constructed. What remains
   is the admitted higher-family collection with its horizontal action laws,
   coherent sections and substitution of the complete extension. The general
   total horizontal composition and all bicategory laws are now constructed. The cell correspondence above
   does not supply those missing constructions.
2. Prove closure of the proposed dimension restriction under extension,
   reindexing, Sigma and open identity. Construct reflexivity and contraction
   in general. Do not replace non-discrete fiber 2-cells by host equality.
   Preserve a counterexample if the chosen restriction fails.
3. Construct J for every admitted motive and finite dependent tail. Prove
   section coherence, reflexive computation and substitution. If Pi is used,
   construct its closure too. Transporting objects alone does not meet this
   obligation.
4. Interpret the specified judgments and retained generic argument, including
   both substitutions of the dependent pair and transported `apd` source.
   Construct the endpoint conjugation and integer observer in that same
   interpretation. Retain nonconstant transport and lower-truncated clients.

[Warren's primary source](https://mawarren.net/papers/crmp1295.pdf), especially
the transformation definitions, Grothendieck cell boundaries, elimination
naturality cells and Theorem 7.1, supplies the construction reference. Its
omega-dimensional soundness result is not a proved finite restriction here.
The separate #321 cubical programme is unchanged.

## Validation boundary

The focused Lake builds check both construction layers and their retained examples.
The repository audit implementation, with its entrypoint replaced by that
focused import, checks all declarations in their project import closure.
This is development evidence. Full candidate acceptance, the integrated
exhaustive audit and independent Standards/Spec review remain pending before
integration or any issue-completion claim. No new axioms or audit exceptions
are introduced.

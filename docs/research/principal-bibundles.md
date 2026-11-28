# Principal bibundles and tensor composition

The selected calculus uses represented sheaf groupoids on a fixed site `J`.
For `C : Type u` with morphisms in `Type v`, its object and arrow sheaves
take values in `Type (max u v)`; its parameter category uses the same bounds.
A bibundle from `G` to `H` is a principal right `H`-bundle over `G.objects`
with a commuting primitive left `G`-action. Its morphisms are all
biequivariant maps; their inverses are derived from right principality.

## Balanced product

The product of a right `H`-bundle and an `H`–`K` bibundle is constructed by
effective descent along the first bundle's locally surjective projection.
Its connector gives the unique `H`-arrow relating two lifts. The second
bundle's primitive left action transports along this connector and satisfies
the descent laws. The descended sheaf carries the residual right `K` action;
its local existence and principality are proved.

The quotient map coequalizes the balancing relation. The generic
`SplitSheafDescent.Quotient.quotientHomEquiv` identifies maps out with all
balanced maps to an arbitrary sheaf, including uniqueness. Cover pullback
stability and the actual tensor base-change comparison retain arbitrary
parameters. No tensor product, quotient universal property or associator is
assumed as an input.

For two bibundles the residual left action makes this a bibundle. Tensoring
maps is functorial. The unitors and associator are constructed by local
pair evaluation and descent, with naturality, triangle and pentagon laws.
The existing `SheafGroupoid` type carries the Mathlib `Bicategory`; its arrows
and whiskering are these actual bibundles and maps. Its underlying operations
and laws remain separate interfaces.

## Full stack mapping comparison

A transformation from the presented groupoid to the target bundle stack
recovers a bibundle by evaluation at the generic object and arrow. The
primitive left action is derived, and modifications recover exactly the
biequivariant maps. The completion universal property then gives the full
mapping equivalence between bibundles and transformations of completed
stacks.

`concreteStackEquivalence` has the actual tensor transformation as its object
map. Reconstruction is compared with the residual tensor action; the proved
comparison transports the map action using Mathlib `Functor.copyObj`.
`tensorStackUnit` and `tensorStackComp` compare the actual identity and tensor
with the stack identity and composition.

Functor-induced bibundles recover `Bundle.completeMap` and its regular unit.
Atlas specializations recover the established identity, composition,
substitution and common-refinement modifications, rather than only giving
an equivalence between their endpoints.

## Invertibility and concrete applications

`LeftPrincipal P` says that the left action has a unique connector between
any two points over the same right anchor, and that this anchor is locally
surjective. The opposite bibundle swaps anchors and uses inverse actions.
The two evaluation maps on balanced products construct its tensor inverse.
Conversely, a tensor inverse makes the source functor fully faithful at every
sheaf parameter. Regular-bundle maps and sheafified representables then recover
the unique left connectors; the second evaluation gives the anchor cover.
This argument does not assume the site is subcanonical.

`leftPrincipal_iff_tensorInverse`, `leftPrincipal_iff_stackEquivalence` and
`leftPrincipal_iff_bicategoryEquivalence` relate the primitive condition to
actual tensor inverses, equivalences of bundle stacks and Mathlib bicategorical
equivalences. Their forward maps are the supplied bibundle and its actual tensor
transformation. Adjointification supplies triangle coherence from the constructed
inverse data.

The C4 example starts with the existing clutching torsor on the doubled-origin
base. It passes through the bibundles induced by the diagonal inclusion
C4 → C4 × C4 and the first projection. Their balanced composite is compared with
the identity bibundle, and its action on this nontrivial input recovers the
original torsor. The decoded output still has no global section. A triple
composite uses the constructed associator on this same input. This example uses
actual effective gluing; the doubled-origin base is not a Hausdorff manifold.

The BC4 → 1 control uses the actual functor-induced bibundle. The chart functor
induces an equivalence on orbit classes at every sheaf parameter, but identifies
distinct C4 loops. Its bibundle is not left principal, has no tensor inverse and
induces no stack equivalence. This orbit statement concerns chart objects, not
the isomorphism classes of all global torsors. Noncommuting S3 loops supply a
separate composition-order control through the bibundle map.

## Geometric and site boundaries

The categorical construction supports all represented groupoids with laws
at the existing sheaf-universe bounds on fixed `J`. It does not claim that
every such bibundle or balanced quotient has a smooth-manifold
representative. Smooth representability, ordinary geometric closure,
properness/étaleness transport and anafunctor comparison need their stated
hypotheses and further consumers. Original-site arbitrary-cover comparison
remains with #732; sheaf-parameter singleton-cover completion alone does not
supply its joint and empty covers. Internal Myers properness remains #724.


The remaining geometric work is to select a site and represented geometric
subclass, prove that its allowed anchors and balanced quotients stay in that
subclass, and derive the corresponding properness and étaleness hypotheses.
The anafunctor comparison must construct both directions and compare actual
composites, units and mapping categories. These are further contracts under
#722, rather than assumptions supplied to this sheaf-level construction.

## Source comparison

Meyer–Zhu, [*Groupoids in categories with pretopology*, TAC 30 (2015), no. 55](https://tac.mta.ca/tac/volumes/30/55/30-55abs.html),
is the comparison source. In the published version, Theorem 7.15 prints
Assumptions 2.8 and 7.2; Theorem 7.31 and the start of Section 8 use 2.8 and
7.3. The distinction concerns all covering Čech-groupoid actions versus the
paper's sheaf actions. This development proves the needed sheaf descent and
quotient properties directly. It does not import the paper's geometric
existence hypotheses or assert smooth representability from them.

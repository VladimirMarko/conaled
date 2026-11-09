# Restricted access with dependent higher transport

The bounded construction for [#425](https://github.com/VladimirMarko/conaled/issues/425)
supports restricted context access and a retained second-identity observation
in the same dependent family. Its nonidentity key changes that family's action
on higher cells. Omitting the pullback changes the answer. This is a new paper
construction, not a checked joint Lean model or an interpretation of full MTT.

The inspected code baseline is `d7debd4e0d510a1a5f8d18513a1fb80e69e51410`.
The recommendation is a small formalization of the explicit diagram below,
reusing higher-family reindexing where useful. Neither an incumbent adapter nor
an existing consumer is a prerequisite. A full modal calculus, general modal
right adjoints, and smooth/cohesive geometry remain separate work.

## Independent operation and access policy

Consider a dependent path observer which receives a permitted second path and
returns its induced first path in a dependent fiber. Changing the access key
must reindex both the family and the path. An ordinary Boolean `y` in the full
context must remain unavailable after locking. The required observation is the
returned fiber arrow, including its label; its endpoints alone do not suffice.

We deliberately choose a small algebraic access policy, not a claim about
physical security, cohesion, or crisp variables. Let `G` range over small
abelian groups, with group homomorphisms as permitted changes of parameters.
There are three locked views `u`, `v`, `w`, with keys directed on environments
as `u ← v ← w`. The first key applies the group endomorphism `[2]:g ↦ 2g`,
the second applies `[3]`, and the composite applies `[6]`. This specifies the
policy before choosing a selected input or its output. Multiplication by an
integer is available uniformly for abelian groups and commutes with every
permitted homomorphism. In particular, this policy does not admit arbitrary
functions on labels or functions consulting `y`.

Each locked view has higher context `A_G = B²G`; the full context is
`A_G × Disc(Bool)`. Its views at `w`, `v`, `u` are respectively projection,
`[3]` after projection, and `[6]` after projection. Thus the view maps commute
with the keys, on objects, arrows and cells. The diagram is thin: one key for
each comparable pair, with the stated identities and composition. A key here
is a semantic substitution between locked environments. We have not extended
it to all lock words or shown that it is a full MTT mode interpretation.

The contract asks for:

- dependent transport of a selected second path through these views;
- agreement of successive keys, their composite, and admissible substitutions;
- retention of the actual resulting fiber arrow;
- independence from the unavailable Boolean in the full context.

An equivalent presentation satisfying these conditions is admissible. There
is no requirement to use integers as the representation, no universal claim
that modal access must rescale paths, and no requirement for a second client.
The integer case below supplies a separating observation for this policy.

## Primary sources and the unclaimed combination theorem

[Gratzer, Kavvos, Nuyts and Birkedal, *Multimodal Dependent Type Theory*,
v2](https://arxiv.org/pdf/2011.15021v2), Figure 2 and §§4–5, distinguish access
cells from object-language identity. A cell between modalities induces a key
substitution in the opposite direction. Definition 5.1 requires a strict
2-functor from the reversed mode theory to context categories. Theorem 7.1
requires an MLTT natural model at each mode, a size-preserving dependent right
adjoint for every modality, natural transformations for mode cells, and
2-functorial choices. These are sufficient hypotheses for a full MTT model;
a pair of separately accepted modal and higher models does not discharge them.
Our diagram supplies no modal type former or DRA. Consequently we do not apply
that theorem or infer a full modal type theory from the diagram.

[Warren, *The Strict ω-Groupoid Interpretation of Type Theory*](https://mawarren.net/papers/crmp1295.pdf),
§§3, 5–6 and Theorem 7.1, constructs dependent extension, open identity and
elimination before stating soundness for the specified intensional theory with
Σ, Π and identity. Its contexts are small strict ω-groupoids and its types are
functors into the specified higher groupoid category; terms retain section
data. This is a construction with those hypotheses, not a theorem that any
collection of groupoids plus locks is a model. We use its hom-family perspective
as motivation. The finite formulas below establish only their stated
transport fragment; no appeal to the theorem supplies missing modal or J laws.

The newer [computational-HoTT synthesis](computational-hott-research.md)
keeps universe/Glue construction, source compatibility and retained computation
separate. The [cubical construction](cubical-model-construction.md) supplies a
universe-free annotated fragment with higher observations, not automatically
our keys. Its filling and dimension-substitution laws would require a separate
joint construction. Neither univalence nor a cubical universe is needed for
the chosen finite-dimensional operation. Their absence here is not evidence
against a cubical route.

## Constructing the higher family

All formulas in this section are paper derivations. Composition of labels is
written additively. `A_G = B²G` has one object `*`, one 1-arrow `e`, and 2-cells
`g:e⇒e` indexed by `G`. Both compositions of 2-cells are addition; identity is
zero and inverse is negation. Interchange follows from commutativity of `G`.
This abelian hypothesis is essential for this particular one-object,
one-arrow construction.

Let `BG` have one object `o` and arrows indexed by `G`, with addition as
composition. Regard it as a locally discrete strict 2-groupoid: there is a
2-cell between its arrows only when their labels are equal. Define the
covariant higher family

```text
F_G : A_G → Gpd
F_G(*) = BG
F_G(e) = identity functor
F_G(g) = natural transformation identity ⇒ identity with component g.
```

This is the rooted hom family `Hom_A(*,−)`. Naturality of its component at a
fiber arrow `r` is `r+g=g+r`. Vertical and horizontal preservation are both
`F_G(g+h)=F_G(g)F_G(h)`, with the selected component `g+h`; units and inverses
are zero and negation. These equations construct a strict 2-functor, rather
than assume a law named after the desired observation. Although its object
fibers have the same carrier, the family is not constant as a higher family:
the constant family would send every 2-cell to component zero.

Write `K_d:A_G→A_G` for the strict 2-functor that fixes `*` and `e` and sends
`g` to `dg`. Additivity gives both composition laws, zero gives the identity
law, and `K_d K_c=K_(dc)` holds in every dimension. The pulled family
`F_d = K_d*F_G` has component `dg` on a base 2-cell `g`. Thus the required
semantic operation on `h:p⇒q` and `z:F_d(x)` is the natural-transformation
component

```text
act_d(h,z) : F_d(p)(z) → F_d(q)(z)
act_d(g,o) = dg : o → o in BG.
```

This is dependent transport's action on a second path. It is not an unrelated
integer attached to a result. At the semantic level it is evaluation of the
actual family action. No source term obtained by arbitrary-motive J is claimed
here. The local higher model's general J is a possible later connection, not
an unproved premise of this calculation.

For open changes of the path endpoints, let `a:p⇒p'`, `b:q⇒q'` and
`h':p'⇒q'` obey `h'+a=b+h`. Applying the family yields
`d h'+d a=d b+d h`, exactly the square relating the two transported arrows.
Changing the fiber input along any `r` gives `r+dh=dh+r`. These checks include
open boundary comparisons, not only the closed loop chosen for observation.

## Dependent extension and key compatibility

The Grothendieck total context `E_d = ∫F_d` can be written explicitly. It has
one object, 1-arrows labelled `a∈G`, and a 2-cell labelled `g:a⇒b` precisely
when

```text
a = b + dg.
```

The convention agrees with the boundary `a = F_d(g); b`. Identity cells use
zero. If `a=b+dg` and `b=c+dh`, their composite is labelled `g+h` and satisfies
`a=c+d(g+h)`. Horizontal composition adds both arrow labels and both cell
labels; its boundary follows by distributivity and commutativity. Negatives
supply inverses. The projection sends the sole object to `*`, every arrow to
`e`, and the cell `g` to the base cell `g`. Hence this is a constructed strict
2-groupoid over `A_G`.

The key extension over `K_c` is

```text
L_c : E_(dc) → E_d
object ↦ object; fiber arrow a ↦ a; base cell g ↦ cg.
```

Its boundary is valid because `a=b+(dc)g` becomes `a=b+d(cg)`.
All composition laws follow from additivity, and the projection equation
`π L_c = K_c π` holds in all three dimensions. Successive lifts retain the
same fiber arrow and multiply the base cell successively; therefore
`L_c L_b=L_(cb)` with the corresponding family indices. This is the
comprehension/key interaction, including the dependent component.

This square is also the strict pullback of `E_d→A_G` along `K_c`. Given strict
functors `T:Z→E_d`, `S:Z→A_G` with `πT=K_c S` in all dimensions, the unique
lift sends each arrow to its fiber label in `T` and each cell to its base label
in `S`. The equality supplies exactly `a=b+dcg`. Preservation laws follow
from those of `T,S`; uniqueness holds on objects, arrows and cells. Equality
of object maps alone would not establish this universal property.

For every group homomorphism `f:G→H`, construct `A_f:A_G→A_H` on
2-cells by `f`. Pulling `F_d` over `A_H` back along `A_f` gives a family over
`A_G` whose fiber is still `BH` and whose action is `d f(g)`. Its total context
has arrows `a∈H` and cells `g∈G` with boundary `a=b+d f(g)`. The substitution
lift keeps the fiber arrow `a` and maps the base cell to `f(g)`. It therefore
lands in `E_d` over `A_H`, with exactly its required boundary. Identities,
composition and projection follow as for `L_c` above.

The equality `f(cg)=c f(g)` proves that admissible base substitution commutes
with a key, on every cell. Repeated pullback retains the final target fiber:
for `f:G→H` and `j:H→J`, the sequential family and the composite family both
have fiber `BJ` and action `d j(f(g))`. Their total lifts keep each supplied
fiber arrow. This supplies a uniform class of admissible substitutions, with
dependent action and extension, rather than selecting a witness separately
for each input. Replacing the pulled fiber `BH` by `BG` would be an error;
a functor `BG→BH` induced by `f` is a separate family comparison, not the
substitution lift.

For a concrete two-stage substitution on `G=H=J=ℤ`, use `f(n)=2n` and
`j(n)=3n`. For every `n`, the reindexed action is `6dn`, whether substitution
is successive or by `j∘f`. Two keys `K_2,K_3` are particular substitutions:
they change `F_1` to `F_6` and yield `6n`. In both cases the total lift preserves
the supplied fiber arrow while changing its base cell. This distinguishes
reindexing the family from arbitrarily applying a label map to its payload.

## Positive and negative controls

Take `G=ℤ`, the selected second path `h=1`, and the sole fiber object `o`.
Before the key the dependent action is arrow `1`. After `K_2`, it is arrow
`2`. After `K_3` and `K_2` it is arrow `6`. These are inputs in the locked views themselves; a full-context input `1`
maps to `1,3,6` in views `w,v,u`. Reflexive input `0` produces `0`
at every stage. The observer is the arrow label in the fiber `Bℤ`, with fixed
endpoints and framing. It is not an invariant of arbitrary changes of that
framing: the open square above describes those changes instead.

Using the original family without pulling it back along `K_2` returns `1`
where the contract requires `2`. Resetting the retained second path to
reflexivity returns `0`. Quotienting the fiber to its one object also loses the
observation: arrows `0` and `2` have the same endpoints but different labels,
and no 2-cell in the locally discrete fiber equates them. These failures do
not depend on a preference for this representation. They contradict the
independently specified dependent action and its observable arrow.

The total context exposes the same failure without a label-only test. In
`E_2`, there is a cell `1:2⇒0`, since `2=0+2·1`. A purported key lift which
keeps that base cell `1` in `E_1` would require `2=0+1`, which is false.
The correct lift sends it to cell `2:2⇒0`. A product with a constant fiber
would require `a=b` for a cell and cannot supply this comparison. Thus the
construction exercises a higher dependent interaction; the full context's
product with a hidden Boolean is only the access control, not the whole model.

For access, enlarge any locked input telescope by the discrete Boolean and
pull its families back along the projection. Allowed locked operations factor
through that projection on objects, arrows and cells. Consequently replacing
`false` by `true` leaves the selected path, its dependent family, every boundary
comparison, and the returned arrow unchanged. Two full assignments with the
same selected `h=1` and different `y` refute recovery of `y`: they have identical
locked assignments and unequal requested Boolean outputs. The same argument
applies to a substitution trying to choose `h=0` or `h=1` according to `y`.
This is a semantic noninterference result for the declared factorization
policy, not a syntax-completeness or cryptographic-security theorem.

## Scope and equality audit

The nontrivial retained input is a 2-cell of `B²ℤ`; the output is a 1-arrow
of its dependent hom fiber. There are no nonidentity cells above dimension
two. Integer equality is external equality of cell labels, not a replacement
of these cells by proof-irrelevant Lean equality. Functor, projection and
substitution equations here are strict mathematical equalities on all stated
data. The equations do not assert judgmental reduction in Lean or a source
calculus, nor do they identify a cubical Path with an intensional Id.

The construction is uniform for every small abelian group, integer multiplier,
and group homomorphism in its declared class. The integer controls do not
prove the uniform equations; the displayed additive derivations do. Intermediate
forms include changed path boundaries, fiber arrows, pulled families and
Grothendieck cells with their boundary equation. All were included above.
There is no induction over arbitrary modal syntax, dependent tails or motives.
In particular, this report supplies semantic dependent transport, not general
Id elimination, Π closure, a classifier, arbitrary interleaved modal declarations,
or parallel proof-relevant keys. Those are omitted obligations, not assumed
laws hidden behind a model record.

## Direct construction versus current optional interfaces

The existing results remain distinct:

| Route | Reusable evidence and work under this report's contract |
| --- | --- |
| Direct construction above | Group addition proves the family, keys, total context, action and their commuting laws. It needs no full source calculus or modal right adjoint. Formalizing it would still require checked structures and preservation proofs. |
| [ModalAccess.Fragment](../../SquareKit/Internal/ModalAccess/Fragment.lean) and [Comprehension](../../SquareKit/Internal/ModalAccess/Comprehension.lean) | `Cell` is `Prop`-valued reachability; `Env.key` and `keyExtension` construct restricted Boolean environments and family pullback. `type_substitution_key` and `term_substitution_key` provide a useful law shape. Their `Ty` is a Lean family on a carrier; neither identity proofs nor thin keys supply the required higher family action. The rescaling diagram is also not an instance already constructed for their fixed word policy. |
| [TwoFamily](../../SquareKit/Internal/PathTransport/TwoFamily.lean) and [higher reindexing](../../SquareKit/Internal/PathTransport/TwoFamilyHigherReindex.lean) | `Family`, `evaluation`, `Total`, `reindex` and `reindexHigher` retain the needed objects, arrows and cells. A future adapter can supply `B²G`, `F_d`, the key diagram and its admissibility proof; these generic laws can replace repeated total/reindexing proofs. The higher model alone does not enforce the hidden-coordinate policy. |
| [Full higher model](../../SquareKit/Internal/PathTransport/TwoFamilyFullModel.lean) | `fullModel` and `fullSigma` construct the stronger contextual-J/Sigma interpretation described in the [accepted checkpoint](strict-two-groupoid-checkpoint.md). Connecting the new locked operation to its actual source evaluation is additional work, unnecessary for this paper fragment but necessary before claiming that stronger reuse. |

Encoding the selected integer as an ordinary `Type` payload in ModalAccess
could retain its numerical value. That would not itself interpret its role as
a second identity or reconstruct the dependent total boundary. Conversely,
replacing the fixed Boolean access implementation is eligible if a higher
context diagram offers the simpler joint interface. Retain #375/#384's existing
access and varying-fiber contracts as separate regressions during any replacement.
The [earlier comparison](modal-context-higher-identity-comparison.md) and
[dependent extension report](modal-dependent-comprehension.md) describe those
contracts; this report does not retroactively enlarge them.

The direct route establishes the selected operation with fewer capabilities
than a full MTT adapter. The optional higher interface offers already proved
all-cell reindexing, at the cost of supplying its strict-functor presentation
and family casts. No implementation-size, elapsed-time or author-productivity
comparison was conducted. A blanket savings claim would exceed the evidence.

## Bounded follow-up and coherence connection

Recommend a successor under #289, coordinated with #235/#36, to formalize the
`B²G`, `F_d`, `E_d` diagram and the all-cell key/substitution equations. Retain
the positive observations `1,2,6`, the reflexive control, the invalid total-cell
boundary, and forbidden Boolean-dependent substitution. Compare a direct
implementation with reuse of `TwoFamily` on this same contract. No prerequisite
incumbent adapter, second client, full MTT framework or new frontend is needed.
If source reuse is selected, add one explicit dependent-transport expression
and prove its evaluation is the constructed action; do not call a fresh
arithmetic equality a source interpretation.

The contemporaneous #424 local-universes investigation uses FinSet and dependent
Σ elimination. It can explain how weakly stable choices become strictly stable
under its own fullness and LF hypotheses; it does not construct this higher
family or preserve its second cells. A future weak presentation of the joint
model would first need its higher comprehension and all key/transport
comparisons, then appropriate local-universes hypotheses and a theorem retaining
those comparisons. This report's explicit strict diagram has no demonstrated
need for that conversion. The useful connection is the precise prospective
coherence obligation, not an inference of higher savings from FinSet.

The combined-client trigger in the
[architecture disposition](architecture-scaling-study/disposition.md) is now
met at the paper-operation level. Its earlier deferral is no longer a reason
to postpone this bounded experiment. General modal/higher foundations remain
with #289/#36; smooth/cohesive instantiation remains with #100. The accepted
#321 and #322/#336 contracts and #359's original source/computational observer
requirements remain unchanged. No #102/#103 gate is bypassed; #107/#108 are not
activated.

## Evidence and validation

Established local code was inspected at the stated baseline; its prior build
and audit evidence is not rerun or claimed as validation of this new diagram.
The equations, controls and scope audit above are new paper derivations.
There are no new Lean declarations or checked experiments in this report.
Full MTT integration, general modal J compatibility and savings from coherence
strictification are unestablished extensions.

Acceptance checks for this Markdown change are whitespace and local-link
validation on the committed candidate, plus the enclosing independent Standards
and Spec reviews. No Lean build or proof audit is required for this artifact.

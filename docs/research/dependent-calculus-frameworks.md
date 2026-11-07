# Reusable metatheory for independently specified dependent fragments

Issue [#342](https://github.com/VladimirMarko/conaled/issues/342), under #289 and
#290. This report recommends **investigating a boundary-checked presentation
layer**, using BHL's existing syntax-changing theory maps together with an HB-style
contextual boundary discipline as the first formalization candidate.
Retain #339 for its present clients. The evidence does not yet justify replacing
the guarded engine, but an adapter to that engine is not a prerequisite for
investigating a replacement.

The contribution at #342 was a worked paper comparison: independently specified
pair fragments, a dependent client, two successive interpretation steps, and a
countermodel. Those proposed constructions were not Lean-checked at that
research baseline. The subsequent [#344 implementation report](dependent-theory-maps.md)
records checked constructions and their limits. The specification below remains
the independent acceptance case; it is not an ADR or an adoption of one
universal calculus.

## Starting point and primary-source results

At baseline `b8731310f05efdac29f994706fbc1f32eb77de20`,
[#326](reference-dependent-calculus.md) supplies independent typed derivations
and a forward translation into a named guarded extension.
[#332](finitary-type-theories.md) already analyzes contextual/context-free
presentations and their hypotheses. [#339](compositional-specification-experiment.md)
supplies same-signature rule certificates, whole-derivation transport, and exact
model reduct composition. It does not generate typed presentations or prove their
acceptability. The comparison below asks what recurring work another framework
could actually remove.

Source numbering is pinned to the following versions; the cited statements and
proofs were read, rather than inferred from abstracts.

**Bauer, Haselwarter and Lumsdaine (BHL), v1.** Definitions 3.8 and 4.36 give
signatures and raw theories. Definition 5.12 requires tightness, presuppositivity,
empty conclusion contexts, and congruence closure for acceptability. Definition
6.20 additionally organizes boundary evidence over predecessor rules. Theorem
5.15 needs weak presuppositivity; 5.22 needs substitutivity and congruity.
For uniqueness/inversion (5.23/5.27), use the sufficient acceptable-theory
hypotheses here. Section 6.5 assumes sequential contexts, rules and boundaries. Definitions
6.22/6.24 give expression-template syntax maps and theory maps carrying
primitive-rule derivations. Propositions 6.23/6.25 give categories and functorial
actions on expressions and derivations. This needs raw theory maps, not
acceptability. These are syntactic results, not model-existence theorems.
Appendix A distinguishes partial Coq coverage; it lists uniqueness and inversion
as unformalized in that version.
[BHL, §§3–6 and Appendix A](https://arxiv.org/html/2009.05539v1).

**Haselwarter and Bauer (HB), v1.** Definition 2.18 requires a well-founded rule
order and predecessor derivations of each premise context and conclusion
boundary. Definition 2.20 adds a unique symbol rule per symbol. Raw-theory
substitution (3.8) and instantiation (3.13) retain their typing premises; equal
instantiation (3.17) additionally needs well-formed contexts. Presuppositivity
(3.18) requires well-formed metavariable and variable contexts. Finitarity
supports economic rule application/congruence (3.19–3.22); standardness supports
inversion/unique typing (3.24–3.26). Contextual/context-free correspondence
(6.5/6.10) has suitability/labeling hypotheses. It is not an arbitrary
change-of-calculus translation theorem.
[HB, §§2–3 and §6](https://arxiv.org/html/2112.00539v1).

The remainder gives this report's constructions and hypothesis mapping. They
are not examples claimed to appear in either paper.

## Frozen fragments and client

Before choosing between frameworks, fix the following test. No raw guarded
judgment occurs in its definition. Expressions have explicit type arguments;
alpha-equivalent binders may be implemented by shared verified syntax machinery.
Variable contexts are finite telescopes. The judgments are context formation,
`Γ ⊢ A type`, `Γ ⊢ a:A`, `Γ ⊢ A ≡ B`, and `Γ ⊢ a ≡ b:A`.
Equality is typed judgmental equality. There is no object identity constructor,
J, equality reflection, or normalization requirement in this test.

For each fragment separately, derivability is the least closure of its rule
table under variable lookup, weakening, typed reflexivity/symmetry/transitivity,
type/term conversion, and congruence for every primitive constructor. Substitution
is capture-avoiding metasyntactic replacement, not an extra object constructor.
Typed substitution is a theorem to establish. General raw assumptions and
untyped equality are not admitted. Fresh declared symbols require ordered,
already formed argument telescopes and result boundaries; declaration equations
require formed endpoints. This policy permits the client constants below.

Here are the complete pair-specific object rules, written with ordinary
variable contexts. Every row includes `Γ ctx`; each displayed premise must be
derived. All type arguments shown in a constructor are retained in raw syntax.

| Constructor | Premises | Conclusion |
|---|---|---|
| `P(A,B)` | `Γ ⊢ A type`; `Γ,x:A ⊢ B(x) type` | `Γ ⊢ P(A,B) type` |
| `pair(A,B,a,b)` | preceding family premises; `Γ ⊢ a:A`; `Γ ⊢ b:B(a)` | `Γ ⊢ pair(a,b):P(A,B)` |
| `fst(A,B,p)` | family premises; `Γ ⊢ p:P(A,B)` | `Γ ⊢ fst(p):A` |
| `snd(A,B,p)` | family premises; `Γ ⊢ p:P(A,B)` | `Γ ⊢ snd(p):B(fst(p))` |

For **Pβ**, add just the equations `fst(pair(a,b)) ≡ a:A` and
`snd(pair(a,b)) ≡ b:B(a)`, with the same formed family/component premises.
The latter uses the former to convert its left operand's type. Order the first
beta equation before the second when certifying rule boundaries.

For **Pη**, specify a separate inference system with that entire table and both
beta equations, and also `pair(fst(p),snd(p)) ≡ p:P(A,B)` for a typed p.
Pη derivability is not defined as Pβ derivability plus semantic truth or as
engine derivability. The duplicated presentation has a literal inclusion map,
which is proved after both systems have been defined.

These are projection-based dependent-pair specifications. Pβ deliberately does
not provide arbitrary dependent elimination. It is therefore **not** a new name
for the repository's `PrimitiveSigma` contract. Pη can derive dependent
elimination using its eta law, as calculated below. This difference is precisely
one of the costs a specification must expose.

The common client uses ordered declarations

```text
N type
n:N                 ⊢ B(n) type
n:N, y:B(n)         ⊢ C(n,y) type
m:N                 ⊢ s(m):N
k:N                 ⊢ d(k):N
m:N                 ⊢ t(m):B(s(m))
m:N                 ⊢ u(m):C(s(m),t(m))
```

These are declared symbols with the indicated argument telescopes, not claims
that every fiber is inhabited. In context `Γ = (n:N,y:B(n),z:C(n,y))`, set
`q = pair(N,B,n,y)`. Beta and conversion give

```text
fst(q) ≡ n : N
snd(q) ≡ y : B(n)
C(n,snd(q)) ≡ C(n,y)
z : C(n,snd(q)).
```

The final selected term is **z**, retyped by conversion. Merely producing some
inhabitant of its fiber would fail this client. The last family depends on the
previous selected component. Eta is not needed by the shared proof.

The failure test is fixed too: a syntax-fixing interpretation Pη → Pβ must be
rejected. A failed proof search does not count as rejection; the model below
provides the obstruction.

## A second interpretation step that expands syntax

Define a third presentation **Eη**, with a fresh pair type symbol `S`, constructor
`pack`, and primitive dependent `split`. Its family and constructor rules have
the same shapes as Pη's first two rows. The eliminator premises are

```text
Γ ⊢ A type                     Γ,x:A ⊢ B(x) type
Γ,p:S(A,B) ⊢ D(p) type          Γ,x:A,y:B(x) ⊢ e(x,y):D(pack(x,y))
Γ ⊢ p:S(A,B)
---------------------------------------------------------------
Γ ⊢ split(D,e,p):D(p).
```

Include constructor beta `split(D,e,pack(a,b)) ≡ e(a,b):D(pack(a,b))`.
Derive macros

```text
first(p)  = split((λp. A), (λx y. x), p)
second(p) = split((λp. B(first(p))), (λx y. y), p).
```

These lambdas denote binding in rule syntax, not a required function type.
The second branch checks because first-beta converts `B(first(pack(x,y)))`
to `B(x)`. Lastly add the equation
`pack(first(p),second(p)) ≡ p:S(A,B)`. Its macro-expanded endpoints are
well-typed using the earlier split rule and beta, so its boundary does not
require the equation being introduced. Eη has its own least derivability
relation, not one defined via Pη.

Let `F:Pβ → Pη` preserve syntax and replay rules. Let `G:Pη → Eη` send P/pair
to S/pack, fst to first, and snd to second; it fixes client declarations and
acts recursively beneath binders. Formation is preserved by the displayed
rules. Each beta certificate is a split-beta derivation followed by conversion;
the eta certificate is Eη's last equation. These are certificates for primitive
rules, not a supplied field asserting correctness of every source proof.

For the shared client, G turns `snd(pair(n,y)) ≡ y` into the split-beta argument
for `second(pack(n,y)) ≡ y`. Congruence for C and conversion retain exactly z.
No witness search enters either step.

A useful reverse presentation map `H:Eη → Pη` sends S/pack to P/pair and
expands split as `e(fst(p),snd(p))`. The substituted branch initially has type
`D(pair(fst(p),snd(p)))`; Pη eta converts it to `D(p)`. Split beta follows by
the two projection beta equations. Its eta equation is preserved by those
same computations and Pη eta. Thus the stronger projection contract supplies
full dependent elimination in this paper test; the weaker one does not.
We do not claim that G/H return identical raw terms or identical proof trees,
or prove a general round-trip theorem here. This is distinct from functoriality
of translation along a composite map, which BHL Proposition 6.25 supplies in its
own derivation representation.

## Two substitutions and selected semantic data

Define a typed substitution `σ:(m:N) → Γ` by

```text
n ↦ s(m),  y ↦ t(m),  z ↦ u(m).
```

Its second and third components are checked at the types obtained by the earlier
components, exactly as their declarations specify. Let
`τ:(k:N) → (m:N)` send m to d(k). Substitution in the client yields

```text
σ:    u(m)    : C(s(m),second(pack(s(m),t(m))))
σ∘τ: u(d(k)) : C(s(d(k)),second(pack(s(d(k)),t(d(k))))).
```

These display the Eη images; before translation the same expressions use
snd/pair. Beta converts their types to `C(s(m),t(m))` and
`C(s(d(k)),t(d(k)))`. The terms remain u(m) and u(d(k)).
Capture-avoiding recursion shows
`G(a[σ])[Gτ] = G(a[σ∘τ])` modulo the chosen alpha representation: G expands
constructors into fixed binding templates, with no free variables beyond their
arguments. The same induction applies to type expressions and every component
of a telescope. This is an expression calculation, not a claim that translated
proof trees are definitionally equal.

For a nonvacuous set-family interpretation, take

```text
N = Nat;  B(n) = Fin(n+2);  C(n,i) = Fin(i.val+2)
s(m) = m+1;  d(k) = 2*k
t(m) = the element m+1 of Fin(m+3)
u(m) = the element m+2 of Fin(m+3).
```

Interpret pairs by ordinary dependent pairs and split by dependent pattern
matching. All displayed inequalities are immediate strict successor bounds;
all pair laws hold. At k=2 the twice-substituted argument is n=5, selected y=5
in Fin 7, and selected z=6 in Fin 7. Both interpretation steps retain those
values. Replacing z by zero would satisfy inhabitation but fail selected-term
preservation. These are paper evaluations, not additional checked examples.

## Countermodel and the semantic boundary

Interpret contexts by sets, types by arbitrary set families, and terms by
sections. Use ordinary context extension and substitution. Interpret Pβ by

```text
P(A,B)(γ) = { (a,b,ε) | a∈A(γ), b∈B(γ,a), ε∈Bool }
pair(a,b) = (a,b,false)
fst(a,b,ε) = a;       snd(a,b,ε) = b.
```

Typed equality is equality of these interpreted values. Reindexing is
precomposition, so it preserves every operation exactly. Congruence and
conversion are valid. Both beta equations hold for every family B; no constant-
family restriction is used. This gives soundness of all Pβ rules by induction
on derivations. For A and B singleton families, p=(*,*,true) violates eta:
repacking has flag false. If a syntax-fixing Pη → Pβ interpretation existed,
its eta certificate would be valid here, a contradiction.

The omission of dependent elimination is substantive. Choose a family D on the
flagged pair whose fiber is a singleton at false and empty at true. There is a
branch at every constructed pair but no section at every p. Hence this model
cannot validate Eη's split rule. This explains why it is not a countermodel to
the existing primitive-eliminator interface. Its sharper all-family conclusion
comes from testing a weaker projection-only specification.

This countermodel does not disqualify an implementation with redundant bits.
If its semantic interface forgets ε and interprets equality by equality of the
underlying dependent pairs, it may realize Pη. That changes the equality
interpretation used in the countermodel. The failed map fixed both syntax and
the specified judgmental equality. [#341](https://github.com/VladimirMarko/conaled/issues/341)
owns enforcement of the corresponding semantic-client boundary.

## Mapping this test to framework obligations

The following is the hypothesis audit for these particular presentations.
It is a paper construction of the required evidence, not a claim that our
current Lean declarations already inhabit the authors' definitions.

| Obligation | Evidence or work for Pβ, Pη and Eη |
|---|---|
| Raw signature and binding arities | Separate type/term classes. P binds one variable in B; split binds p in D and x,y in e. Explicit A/B/D arguments remain in terms, including arguments unused by evaluation. Each rule premise metavariable is introduced once. |
| Ordered premise boundaries | A precedes B; a precedes b; in split, A/B precede D and D precedes e. A repeated premise uses an existing metavariable, never redeclares it. Context notation in the tables must be compiled to abstracted metavariable premises and an empty conclusion context. |
| Rule boundary derivations | Pair formation before pair; pair and fst formation before snd; first beta before second beta's common-type conversion; all formation and beta before eta. Eη's split boundary uses D(p), its beta uses e(a,b), and its eta uses previously derived first/second macros. |
| Tightness and symbol rules | Include every syntactic argument's formation/typing premise. One object rule per primitive symbol. Add the associated congruence rules. Equations introduce no extra object symbol. Macro first/second are expanded, not assigned a second symbol rule. |
| Well-founded rule order | The finite order just listed, with the client declarations in their displayed dependency order. More precisely, rule-boundary checking may assume its premise metavariables; it cannot assume the new conclusion or an unintroduced symbol. This is the predecessor discipline in BHL 6.20 / HB 2.18. |
| Structural reuse | HB raw closure already supports weakening, typed substitution and metavariable instantiation. Boundary evidence permits economic application; BHL's admissible elimination of explicit substitution applies after its substitutive/congruous checks. Neither result gives normalization. |
| Presuppositions and typing | HB's well-formed variable/metavariable contexts must be carried with each derivation before using 3.18. Standardness then applies to these explicit-argument terms. In BHL use the acceptable package, not just an arbitrary rule list. |
| Local interpretation certificates | BHL 6.22/6.24: F uses generic symbol applications and replayed rules; G uses the displayed first/second templates and split-beta/eta derivations; H uses projection templates and eta conversion. Images of constructor congruence rules follow by target congruence induction on the templates. The maps fix variables and preserve syntactic classes and argument binding scopes. These are additional input certificates; acceptability cannot invent them. |
| Generic map composition | BHL 6.23/6.25 applies after encoding these sequential presentations and certificates. It derives the full expression/derivation action, identity, composition and functoriality. No semantic model, normalization or acceptability hypothesis is required for this raw-map result. |
| Semantic interpretation | Set-family operations and validity of each primitive rule, including congruence and substitution compatibility. This is a separately supplied model construction. Neither syntactic framework supplies all-model existence, selected representatives, or an arbitrary CwF soundness theorem merely from finitarity. |

There is a concrete subtlety in the rule order: the dependent second beta's
boundary needs first beta, not just formation rules. Likewise G's definition of
second needs beta to type its branch. A generic presentation layer must allow
boundary derivations using preceding **equations**, rather than restricting all
equations to a final phase after every object boundary has been fixed.

## Existing local-to-global transport and remaining work

BHL already provides the syntax-changing generalization of #339's proof pattern.
In Definition 6.22, a symbol S maps to an expression of its result class over the
target signature extended by S's argument metavariables, at empty external
scope. Recursion instantiates this template with translated arguments, preserving
variables and extending trivially over metavariables. Definition 6.24 additionally
supplies a derivation of each translated specific rule. The section's sequential
context/rule/boundary convention applies; acceptability and well-presentation
are not additional hypotheses of this raw-map construction.

For F, the templates are generic applications of the unchanged symbols. For G,
they are S/pack and the displayed first/second expansions. For H, the split
template is the substituted branch `e(fst(p),snd(p))`. Their rule certificates
were calculated above; target congruence applied recursively to each template
handles the images of the associated constructor congruence rules. Thus these
are proposed instances of the **existing** raw theory map definition, once the
paper presentations are encoded in BHL's syntax. Their semantic validity is not
being substituted for the required syntactic derivations.

Proposition 6.23 gives identity and composition of syntax maps and functorial
expression action. Proposition 6.25 derives the action on whole derivations:
structural rules translate structurally; a specific-rule instance uses the
translated local certificate, instantiates it, and grafts in translated premise
derivations. Its proof uses compatibility of syntax-map action with instantiation,
the property needed for this report's dependent substitution calculation. The
composite sends each rule certificate through the second map. The proposition
also states `(J ∘ I)₊ D = J₊(I₊ D)` for derivations, not merely equality of final
judgments. Identity and associativity come with its category `RawTh`.
[BHL §6.5, Definitions 6.22/6.24 and Propositions 6.23/6.25](https://arxiv.org/html/2009.05539v1#S6.SS5).

Accordingly, arbitrary proof-tree coherence is not an unspecified missing
mathematical ingredient of that source construction. A Lean port must establish
the stated functoriality for its chosen representation, or relate that
representation to the source's. It cannot infer equality of existing guarded
Lean derivation trees from the paper. Nor does functorial composition establish
G/H inverse maps or a round-trip theorem for all source terms.

What remains additional is semantic interpretation. A target set-family model
can be reduced by evaluating the translated templates; soundness of the local
certificates establishes source rule validity. Expression evaluation induction
and substitution prove agreement between the semantics of a composite and two
successive reducts. This is our paper construction, not a semantic-model theorem
asserted by Propositions 6.23/6.25. The selected values calculated above are
retained because these particular evaluations preserve the chosen terms. A
comparison of arbitrary dependent models must separately supply its action on
types, terms and witnesses, substitution compatibility, and required coherence.
Raw theory maps alone do not construct such comparisons or selected sections.

The new infrastructure work is therefore a **port or adaptation of existing
syntactic machinery**, plus the semantic connection required by our clients.
Using HB's presentation rather than BHL's requires a proved adaptation of the
map construction and its structural cases; HB's context-free correspondence is
not that bridge. [#340](https://github.com/VladimirMarko/conaled/issues/340)
owns changes of underlying logic and the broader satisfaction/computation
interface; this test keeps its judgmental logic fixed.

| Claim | Established scope in this report |
|---|---|
| Judgment preservation | F/G/H certificates are paper calculations. BHL 6.25 provides generic derivation transport once they are encoded as its raw theory maps. No Lean instantiation is supplied here. |
| Semantic soundness | Paper set-family interpretation, exact selected client evaluation, and flag countermodel. |
| Reconstruction | No general engine-to-calculus reconstruction. HB's annotated-presentation reconstruction has its own hypotheses. |
| Conservativity/reflection | No general claim. The syntax-fixing Pη-to-Pβ map is disproved. Nothing here rules out other encodings. |
| Round trips | No identity claim for all G/H proof trees, and no global round trip with the guarded engine. |
| Ordering of fragments | Pβ includes into Pη; named interpretations compose. This gives a small directed diagram. Interpretability does not establish antisymmetry, canonical joins/meets, or a lattice of calculi. |

## Recurring obligations and recommendation

The actual comparison is against
[RuleInterpretation](../../SquareKit/GuardedRuleInterpretation.lean),
[ReferenceSignature](../../SquareKit/Internal/DependentJudgments/ReferenceSignature.lean),
and [ReferenceSubstitution](../../SquareKit/Internal/DependentJudgments/ReferenceSubstitution.lean).
The current reference boundary already separates derivability from models and
checks ordered declarations. Its object contexts/substitutions are explicit
expressions; schematic leaf replacement is a different substitution theorem.
No syntactic identification with the binding calculus above is assumed.

| Cost or capability | Current checked approach | Proposed framework experiment |
|---|---|---|
| Adding a dependent constructor | Extend reference judgments/rules and their constructor inductions where required; discharge guarded validation. | Supply explicit binding arity, ordered boundary evidence and primitive laws; instantiate generic structural results. |
| Reusing source proofs | #339 derives transport/cut from per-rule certificates over one signature. | BHL 6.22–6.25 already derives syntax-changing transport and functorial composition from templates/certificates. Port that construction, or prove its HB adaptation, once at infrastructure level. |
| Typing presuppositions | Reference constructors and dedicated presupposition lemmas; source equality formation can require explicit endpoint work. | Generic theorem and economic rule forms after boundary certificates; no removal of legitimate formation obligations. |
| Changing equality/pair requirements | Existing separate capabilities and adapters. | Separate presentations and equations; failed interpretation still requires an obstruction. Neither framework makes incompatible contracts equivalent. |
| Semantic models and witnesses | Existing Type-family, restricted separators and higher providers; concrete selected clients checked. | Not supplied by finitarity. Rebuild/relate required interpretations and preserve actual term/witness data. |
| First-use cost | Existing code can be reused now. | Implement binding syntax and boundary judgments; port generic metatheory and BHL theory maps, proving any presentation adaptation. |
| Repeated-use cost | Some constructor-specific induction and conversion work remains. | Boundary evidence persists, but generic structural inductions should disappear from each new fragment. This is a testable prediction, not measured productivity. |

**Adopt now:** keep independent source specifications and explicit pair-law
requirements; use #339 for existing same-signature proof reuse. Record the
projection-only/eliminator distinction whenever reusing this report's model.

**Investigate:** reuse BHL's raw syntax/theory map construction as the transport
foundation, paired with a bounded contextual boundary discipline. HB remains a
candidate for that discipline because its explicit predecessor-boundary
certificates directly match the test and support economic rule application.
This revises the initial HB-first recommendation: BHL is a source of the desired
generic transport and composition, not just an acceptability comparison. Before
choosing an HB adaptation, compare its bridge obligations with a direct BHL
sequential/well-presented encoding of Pβ/Pη/Eη. Prefer the direct encoding if
adaptation adds duplicate structural proofs. The first experiment should settle
that choice; no claim of HB superiority or final architecture follows.

**Defer:** the context-free frontend and its annotation/assumption-set machinery
until an authoring consumer needs it. Also defer an executable translator as
already recorded under #339/#290. This report adds no normalization or runtime
claim. **Reject as a premise:** one strongest calculus, a presumed lattice, or
a general reverse compiler. None is needed to derive the reusable operations
shown here.

The next formalization should first encode the displayed rule boundaries in
BHL's sequential syntax and compare them with the HB encoding. Record any
additional bridge lemmas before choosing the implementation presentation. Port
BHL 6.22–6.25 directly or prove the chosen adaptation, including functoriality on
derivations, alongside generic substitution/presupposition results. Then
independently instantiate Pβ and Pη, followed by Eη and F/G. Its acceptance tests are the displayed
selected client under σ and τ, the full set-family flag separator, and an
extension whose second beta cannot be admitted before first beta. Derive
whole-proof transport from local templates/certificates; do not accept a record
whose principal field is that final transport theorem. Check the source's functorial derivation-action law for the chosen Lean
representation, as well as composition on judgments and selected terms. Keep
semantic-model coherence and G/H round trips separate from this syntactic law.

Compare setup effort separately from adding Eη after Pβ/Pη: count newly authored
structural induction proofs, explicit boundary certificates, repairs, and agent
resources under matched obligations. A successful replacement experiment removes
per-constructor structural inductions while retaining these contracts. If it only
renames the current manual obligations, report that failure. Only after this
comparison should we choose a guarded-engine adapter, a larger replacement, or
continued coexistence. Existing checked higher-witness and Id/J clients remain
migration requirements before any broad adoption; the no-Id test here cannot
establish their coverage. #289/#290 and orchestration #235 own that scoped
formalization proposal; #338 owns joint conversion-changing extensions.

## Validation and limits

This change adds only this research report. Source statements were checked
against the primary texts linked above; the new calculations were reviewed on
paper. Repository-relative links and whitespace are checked at the committed
candidate. The enclosing #337–#342 orchestration owns independent Standards and
Spec review. No Lean build or proof audit can certify the new paper arguments;
no formal source changed. Existing checked results remain at the linked scope.
#107 remains paused and #108 remains unselected.

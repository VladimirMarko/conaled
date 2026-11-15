# Finitary type theories and independent source calculi

Haselwarter and Bauer supply a useful reference for an independently specified
structural/Id/J calculus and a reusable method for comparing presentations.
Their context-free calculus retains typing and assumption information in syntax;
it is not the repository's annotation-free guarded engine. Use their boundary
and translation obligations to test a bounded correspondence before considering
a framework implementation. Retain the existing engine, represented-family
interface, strict maps and strong Sigma capability while conducting that test.

This report addresses [#332](https://github.com/VladimirMarko/conaled/issues/332)
under [#235](https://github.com/VladimirMarko/conaled/issues/235), informing
[#326](https://github.com/VladimirMarko/conaled/issues/326) and the related
#324–#328 investigations. Recommendations below are architectural justification,
not adopted ADR decisions. The combined discussion has concluded and bounded
investigations are authorized; it did not select a universal calculus framework.

## Sources and evidence boundary

The primary text is Philipp G. Haselwarter and Andrej Bauer,
[*Finitary type theories with and without contexts*, arXiv:2112.00539v1,
1 December 2021](https://arxiv.org/abs/2112.00539v1).
References below use that version's numbering. The
[PDF](https://arxiv.org/pdf/2112.00539v1),
[HTML](https://arxiv.org/html/2112.00539v1) and
[TeX source](https://arxiv.org/src/2112.00539v1) provide the primary text.
The analysis follows §§2–6 and the relevant proofs in Appendices A.1–A.3,
especially the translation inductions and boundary conversion.

Repository claims refer to integration baseline
`5411b02384643285a00e45df9d27115b81c1ce9f`. Linked definitions and proofs were
inspected, including the selected clients below. No new formal theorem,
translation, separating model or higher-model completion is claimed here.
The worked examples are mathematical reconstructions, not Lean-checked files.
The related [architecture reassessment](dependent-architecture-reassessment.md),
[judgment experiment](dependent-judgment-representation.md),
[constructor study](dependent-constructor-admission.md), and
[#323 evaluation](../../experiments/guarded-j-retest/trial/evaluation.md)
retain the prior evidence and its limits.

## Two presentations of a type theory

In the contextual presentation, abbreviated **tt**, a judgment is
`Θ; Γ ⊢ J`. The metavariable context Θ is a finite ordered list of declarations
`M : B`, where B is a boundary, possibly abstracted over several term variables.
The variable context Γ is a finite ordered dependent list `a₁:A₁,…,aₙ:Aₙ`.
The four judgment theses are `A type`, `t:A`, `A ≡ B`, and `s ≡ t:A`.
An abstracted judgment `{x:A} J` binds an object variable; it is not a function
type. Bound and free variables are separate syntactic classes. A boundary
replaces the head of a judgment by a hole, for example `□:A` or
`s ≡ t:A by □`. Equality heads are dummy values in tt, not identity proofs.
See §2.1, Figures 2.1–2.3.

A signature records each symbol's result class and the classes and binder
counts of its arguments. A metavariable instead has a class and a number of
term arguments. For example a family metavariable can have boundary
`{x:A} □ type`, and an instance supplies an abstracted family. Thus replacing
metavariables by expressions and replacing object variables by terms are
different operations. A rule packages its premises as ordered metavariable
boundaries and its conclusion in that metavariable context with no free object
variables. Instantiating a raw rule requires its instantiated premises **and
the instantiated conclusion boundary**. Congruence rules retain the typing
premises needed to compare dependent arguments (§§2.1.5, 2.3).

There are three levels of theory, with different available theorems:

| Level | Required discipline |
|---|---|
| Raw | Well-scoped syntax, correct arities and ordered metavariable declarations; structural, rule-instance and congruence closure as specified in §2.3. Raw derivability alone does not certify well-formed contexts. |
| Finitary | Definition 2.18: a well-founded order on rules, with each rule's premise context and conclusion boundary derivable using predecessor rules. This certifies presuppositions without circular justification. The collection of rules may be infinite; individual arities/premise lists are finite. |
| Standard | Definition 2.20: finitary, every specific object rule a symbol rule, and exactly one such rule for each symbol. Symbol rules retain their prescribed arguments. Equality rules remain available. |

In the **context-free** presentation, abbreviated **cf**, judgments omit Θ and
Γ. A free variable is the pair `a^A` of a name and a type annotation; a
metavariable is `M^B` with a boundary annotation. Annotations contain further
annotated variables. The same bare name with different annotations denotes
different variables. Type annotations have no exposed bound variables;
metavariable boundary annotations are closed with respect to free object
variables. Bound variables and explicit abstractions remain (§4.1).

An equality is `A ≡ B by α` or `s ≡ t:A by α`, where α is a finite assumption
set. It records variables and metavariables used to establish the equation that
may disappear from its operands and type. This matters, for example, if a theory
includes equality reflection: deriving `s ≡ t:A` from `p:Id(A,s,t)` must retain
p even though p is absent from the equation's boundary (Example 4.2). Reflection
is an example the framework permits, not a rule required of an intensional
Id/J fragment.

Conversion constructs `κ(t,β)` rather than leaving t unchanged. Given `t:A`
and `A ≡ B by α`, its rule requires
`asm(t,A,B,α) = asm(t,B,β)` and concludes `κ(t,β):B` (Figure 4.7).
Here `asm` collects occurrences including annotations. The node records
assumptions, not an equality derivation or an object identity proof. Equality
closure rules similarly preserve the union of premise assumptions in the
conclusion. Minimal sets are allowed but not required: minimality is unstable
under instantiation, whereas the stated equality of assumption sets is stable.
Definition 4.1 also requires every premise metavariable to occur in the
conclusion, possibly through annotations or assumption sets.

Abstraction must proceed in reverse dependency order. One cannot replace
`a^A` by a bound x while a remaining free variable's annotation still refers
to `a^A`. Substitution for a bound variable changes an assumption-set member x
into all assumptions of the substituting term. Instantiation of metavariables
also transforms annotations and therefore can change the identity of free
variables (§§4.1.4, 4.1.6). These are substantive requirements for a reusable
implementation, not merely printing conventions.

The cf variable rule can derive `a^A:A` without proving A is a type.
Definition 4.12 separately requires every occurring free-variable annotation
to be a derivable type and every metavariable annotation to be a derivable
boundary. Cf finitarity and standardness impose the corresponding ordered-rule
conditions (Definitions 4.13–4.14). Dropping contexts does not remove assumption
well-formedness obligations.

## Metatheorems and their hypotheses

These statements concern the paper's deductive systems, not an arbitrary
implementation with similarly named operations.

| Result in v1 | Hypotheses and conclusion relevant here |
|---|---|
| Proposition 3.2, weakening | In a raw tt theory, insertion of a fresh variable or metavariable declaration into a syntactically valid context preserves a derivable judgment or boundary. This alone does not establish well-formedness of the enlarged context. |
| Theorem 3.8, substitution | In a raw tt theory, the rules of Figure 3.1 are admissible: from `{x:A} J` and `t:A`, derive `J[t/x]`, likewise boundaries. Equal substitution also requires both `s:A`, `t:A` and `s ≡ t:A`; dependent remaining abstractions are reindexed along s. Abstraction conversion requires `B type` and `A ≡ B`. |
| Theorems 3.13 and 3.17, instantiation | A derivable instantiation I of Ξ over `Θ;Γ` preserves derivable judgments `Ξ;Γ ⊢ J` and boundaries. For equal instantiations I,J and an object judgment, 3.17 also requires well-formed Ξ and Γ; it derives equality of the instantiated heads at the I-instantiated boundary. Equality means component equalities at the earlier I-instantiated object boundaries; equation premises are not proof terms to compare. |
| Theorem 3.18, presuppositivity | In a **raw** tt theory, well-formed Θ, well-formed Γ over Θ, and `Θ;Γ ⊢ B[e]` imply `Θ;Γ ⊢ B`. In particular typed equality has well-typed operands in a common boundary. Finitarity is not an extra hypothesis here. |
| Propositions 3.19–3.22, economic rules | Derivable rule boundaries allow omission of redundant boundary premises; finitarity supplies these derivations. Economic congruence 3.22 additionally works over well-formed Θ and Γ. Omission is justified by a theorem, not by deleting guards from arbitrary raw rules. |
| Theorems 3.24 and 3.26 | In a **standard** tt theory, inversion recovers a final variable, metavariable, symbol or abstraction rule, or a conversion from the term's natural type. If the same term has types A and B, derive `A ≡ B`. For uniqueness from two term-equality judgments, 3.26 also requires well-formed contexts. No normalization or decidable equality follows. |
| Theorems 5.4, 5.5 and 5.8 | Raw cf substitution is admissible for abstracted judgments/boundaries and a term of the declared type. Cf presuppositivity additionally requires well-typed annotations of the judgment. Cf instantiation additionally requires well-typed annotations, a derivable instantiation I, and coverage of all occurring metavariables by I. |
| Theorem 5.15 | In a standard cf theory, `t:A` and `t:B` imply `A ≡ B by α`, with α contained in `asm(t)` and computable from the judgments. The equality-judgment version additionally assumes well-typed variables. |
| Theorem 5.16 | In a raw cf theory, from `{ys:Bs}{x:A} J` with x absent from the bound-variable occurrences of J, derive `{ys:Bs} J`. Occurrences include assumption sets. This is strengthening of this annotated judgment, not permission to discard hidden equality assumptions from a tt derivation. |
| Lemma 5.17 | In a raw cf theory, derivable boundaries B₁,B₂, a derivable filling `B₁[e₁]`, and equal erasures of the boundaries give a filling `B₂[e₂]` with the same erased head and `asm(e₂) ⊆ asm(B₁[e₁])`. It repairs conversions while controlling assumptions. |

Lemma 5.6 makes the dependent equality-substitution obligation explicit. Given
a derivable `{xs:As} J` with well-typed annotations, sequences s and t each
typed over their own earlier components, and equalities `sᵢ ≡ t′ᵢ` at the
s-instantiated types with `|t′ᵢ| = |tᵢ|`, it constructs equality after substitution.
For a term judgment with remaining tail `{ys:Bs} u:C`, the result is
`{ys:Bs[s/xs]} u[s/xs] ≡ u′:C[s/xs]`, where `|u′| = |u[t/xs]|`.
The assumptions of the constructed right side and equality, abstracted over
the remaining ys, are contained in those of the input judgment, sequences and
component equalities. The right side need not be the unconverted `u[t/xs]`.
Theorem 5.7 packages this construction as admissible equality-substitution
rules with conversion and suitable assumption sets.

The proof mechanisms explain why these hypotheses matter. Theorem 3.8 uses
induction through substitution and equality substitution with a dependent tail;
Lemma 3.7 explicitly tracks equalities of the tail's reindexed types. The
instantiation-equality argument bootstraps component typing at common
boundaries (Lemmas 3.15–3.16). The presupposition proof recovers variable typing
from context formation, while a specific raw-rule instance already has its
boundary as a premise (Appendix A.1). The cf proof instead uses well-typed
annotations and the corresponding explicit boundary premises (Appendix A.2).

For Lemma 5.17, equal-erasure term boundaries give a type equality by cf
reflexivity, which itself requires both types to be derivable. Insert a
conversion at that boundary. At an abstracted boundary, choose a fresh variable,
convert it between the binder types, substitute, apply the induction hypothesis,
and reabstract. A raw erasure comparison without the two boundary derivations
would not justify this construction. This lemma is central to the reverse
translation, where independently translated premises rarely have identical
conversion syntax.

## Section 6: what the translations establish

**Erasure from cf to tt.** Ordinary erasure `|e|` removes conversion nodes and
replaces assumption sets by dummy equality heads. It leaves an annotated
variable as an atomic *name* in tt. It commutes with object substitution by
structural induction. A suitable context assigns `a^A` the type `|A|` and
`M^B` the boundary `|B|`, and contains every occurring dependency (Definition
6.1). Lemma 6.2 constructs such finite contexts by ordering the transitive
annotation dependencies. Suitability by itself is a syntactic condition.

Theorem 6.5 states three mutually proved results:

1. Rulewise erasure sends a finitary cf theory T to a finitary tt theory Ttt.
2. Given T and Ttt finitary, a well-formed tt metavariable context Θ and variable
   context Γ over Θ in Ttt, a derivable cf judgment J, and suitability of `Θ;Γ`
   for J, derive `Θ;Γ ⊢ |J|` in Ttt.
3. The same assertion holds for boundaries.

The apparent repetition of Ttt finitarity in parts 2–3 supports the mutual
induction; part 1 supplies it. Corollary 6.6 preserves standardness. Corollary
6.7 supplies suitable **well-formed** contexts when a derivable cf judgment
has well-typed annotations. Thus it is not legitimate to erase `a^A:A` at an
arbitrarily ill-formed A and invoke the theorem in an empty context.

Appendix A.3 proves the theory clause by induction over the well-founded rule
order and the other clauses by derivation induction. In rule and congruence
cases, recording all premises in the conclusion ensures that a suitable
context for the conclusion contains the dependencies of the premises. Erasure
commuting with substitution handles metavariable application. Conversion
becomes ordinary tt conversion. Discarding assumption sets *before* collecting
the context would invalidate this proof.

**Reconstruction from tt to cf.** Double erasure `||e||` additionally removes
variable annotations. Eligible labelings θ and γ assign annotations whose
double erasures are precisely the declared tt boundaries/types, with consistent
labels on every occurrence (Definition 6.8). An eligible cf theory has the same
signature and indexed rules as the tt theory, with each rule satisfying these
conditions (Definition 6.9).

Theorem 6.10 has five clauses. For any **standard** tt theory T, there exists
an eligible standard cf theory T′. For such T,T′, a well-formed Θ admits an
eligible labeling θ with derivable boundary annotations. Given such θ, a
well-formed Γ over Θ admits an eligible γ with derivable type annotations.
Given these theories, contexts and eligible well-typed labelings, every
derivable tt boundary, respectively judgment, has an eligible derivable cf
boundary, respectively judgment. Eligibility requires exact double erasure of
the returned syntax, not merely equality in an interpretation.

The construction inspects derivations. A conversion step supplies information
that the final tt term does not record; equality steps determine which
assumptions must survive. The simultaneous induction first constructs rule
boundaries and labels using predecessor rules. Standardness lets it reconstruct
the required symbol or equality rule from that boundary. When translating a
rule instance, earlier translated arguments determine the next argument's
boundary; Lemma 5.17 adjusts the independently translated premise to that
boundary. Transitivity must similarly align two translated middle terms and
their types up to erasure before applying cf transitivity. This is more work
than recursively adding type labels to a final judgment.

The precise correspondence has several distinct strengths:

| Claim | Established scope or remaining obligation |
|---|---|
| Forward preservation | 6.5 preserves derivability into the translated theory with suitable well-formed contexts. |
| Reverse reconstruction | 6.10 constructs some eligible annotated derivation from a tt derivation under standardness and the stated labeling conditions. It does not require a stored originating cf proof. |
| Syntax recovery | The returned cf judgment double-erases to the input tt judgment. Starting from cf and returning can change conversions/assumption sets; this is not literal identity of cf syntax or proof trees. |
| Equality at a fixed boundary | Cf reflexivity and 5.17 can compare/repair same-erasure expressions when the relevant typings/boundaries are derivable. This does not identify arbitrary differently annotated variables. |
| Reflection for our engine | Neither theorem concerns `GuardedTheory.Derivation`. Reflection from arbitrary admitted guarded derivations must be proved separately, with a declared admissibility domain. |
| Semantic or witness round trips | Section 6 does not supply the repository's model comparisons or preservation of a chosen J witness. A source correspondence must be connected to those interpretations. |

Section 6.3 demonstrates reuse beyond equivalence language: Proposition 6.11
transports instantiation equality through tt, then reconstructs cf equalities
with controlled assumption sets and prescribed erased heads. The proof chooses
a minimal suitable context to prevent spurious assumptions. This is a concrete
reusable construction pattern, but its standardness, derivability and annotation
hypotheses remain part of the result.

## Worked dependent examples

These examples use the paper's judgment forms, with abbreviations for repeated
annotations. They illustrate how to check a proposed implementation.

Take a signature with `Nat` and `Vec`, where the Vec symbol rule requires
`n:Nat` and concludes `Vec(n) type`. In tt, form
`Γ = n:Nat, v:Vec(n)`. Variable and abstraction rules give

```text
Γ ⊢ v : Vec(n)
n:Nat ⊢ {y:Vec(n)} y : Vec(n)
· ⊢ {x:Nat}{y:Vec(x)} y : Vec(x).
```

In cf the first judgment is
`⊢ v^(Vec(n^Nat)) : Vec(n^Nat)`. Its variable annotations are well-typed using
the Nat and Vec formation rules. Abstract v first, obtaining
`⊢ {y:Vec(n^Nat)} y:Vec(n^Nat)`; only then abstract n to obtain the last displayed
judgment. Abstracting n first is invalid because n occurs in v's annotation.
For `⊢ k:Nat` and `⊢ w:Vec(k)`, two applications of 5.4 yield `⊢ w:Vec(k)`.
The intermediate judgment after the first substitution is
`⊢ {y:Vec(k)} y:Vec(k)`, so the second argument's dependent type is visible.
Erasure and 6.5 recover the same tt derivation under a suitable context for k,w.

For a conversion example, use metavariables declared in order
`n:□:Nat`, `m:□:Nat`, `e:(n ≡ m:Nat by □)`, and `v:□:Vec(n)`.
The equality metavariable e is a judgmental assumption, not an Id proof.
Metavariable application and Vec congruence derive `Vec(n) ≡ Vec(m)`; conversion
then derives `v:Vec(m)` in tt. In cf, the equality carries the assumption e
and hence its annotation dependencies n,m. With annotations suppressed in the
display, a suitable conversion is `κ(v,{e}):Vec(m)`: v already records n in
its type and the result records m, while e must not disappear. Double erasure
returns `v:Vec(m)`. Reading only that final tt judgment cannot reconstruct the
use of e; a derivation provides it. Choosing another equality derivation can
produce another eligible assumption set. This example requires no equality
reflection rule.

For the repository's proposed Id/J test, fix `Γ ⊢ a:A` and the based path
context `P = Γ,y:A,p:Id(A,a,y)`. A finite tail may be
`z:B(y,p), w:D(y,p,z)`. A motive C lives over the entire extended context;
the reflexivity branch d lives over
`Γ,z:B(a,refl(a)),w:D(a,refl(a),z)` with result
`C(a,refl(a),z,w)`. A contextual J rule should yield
`J(C,d,y,p,z,w):C(y,p,z,w)` and compute to d after the full reflexivity
substitution, including its action on B,D and C.

This is a proposed independently stated rule schema, not a theorem that the
paper derives this stronger contextual eliminator from a smaller Id signature.
For each fixed tail length its finitely many binders fit the paper's syntax;
an indexed collection of such finite rules is allowed. Proving finitarity,
standardness and any derivability from ordinary J is still required. Currying
a dependent tail would require suitable function-type structure, absent from
a structural/Id-only specification unless explicitly added.

Under a nonidentity substitution `σ:Δ→Γ`, the comparison must reindex A,a,
the path context, each successive tail type, the motive, and the branch before
comparing J. A second substitution `τ:E→Δ` tests composition. The vector
example explains the dependency order; the conversion example explains why
tracking only the final J term or its endpoint family misses obligations.

## Mapping to the guarded engine and selected clients

[GuardedTheory.lean](../../SquareKit/GuardedTheory.lean) has one raw term carrier,
operation arities and predicates. `Atom.eq` is untyped equality; `reflexive`
admits every raw term and `congruence` has no typing guards. `Derivation.sound`
interprets a derivation in a supplied model under satisfied assumptions. This
is a proved semantic contract, with no independent-calculus adequacy conclusion.

`Term.subst` is `FinitaryTerm.bind`, substituting schematic leaves. In the
dependent presentation, `subTy`, `subTm`, `comp`, weakening and pairing are
*object-language operations* with guarded rules and semantic laws. The paper's
metavariable instantiation is closer to schematic instantiation, but it also
supports arguments with binding and dependent boundaries. Its object-variable
substitution instead acts on contextual syntax. An adapter must relate both
levels; invoking `Term.subst_comp` proves only the schematic composition law.

[TypedMaps.lean](../../SquareKit/Internal/DependentJudgments/TypedMaps.lean)
shows the exact assumption boundary. `TypedAssumptions Ω` requires each equality
assumption's operands to have separate `Defined Ω` witnesses, which can be a
context, family, term, substitution or telescope. It does not require a shared
sort, context or family, and those witnesses themselves use Ω. This is sufficient
for its stated partial-interpretation map theorem with semantic satisfaction.
It is not the well-founded declaration discipline or common typed equality
boundary used in the paper. Preserve this API; define a separate admissibility
judgment for the independent-calculus comparison.

`TypedEquality` in
[Templates.lean](../../SquareKit/Internal/DependentJudgments/Templates.lean)
packages both terms at one context/family alongside raw equality. This supports
useful result comparisons without certifying all intermediate equalities of
an arbitrary engine derivation. `Command.fresh` constructs reindexed tail,
motive and branch; `Command.comparison` proves substituted-versus-fresh equality
with both typings. `Command.substituted_ne_fresh` proves their syntax heads
differ. This is a better first translation test than a closed reflexivity term:
its exact recipe, dependent boundary and substitution derivation are available.

[ContextualRules.lean](../../SquareKit/Internal/DependentJudgments/ContextualRules.lean)
checks guards for Id formation and finite telescope operations. The independent
source should express these mathematical judgments before specifying their
encoding. It must say whether substitutions are dependent tuples, generated
explicit substitution expressions, or primitive assumptions. Finite tails must
be dependent sequences, not merely a natural length attached to an opaque leaf.
The current guarded telescope operations remain useful implementation machinery;
sharing them would require a proved representation of the independently
specified sequence and its substitution.

[GuardedJudgmentBoundaries.lean](../../Examples/GuardedJudgmentBoundaries.lean)
already separates agreement in one interpretation from source equality
(`no_source_equality`) and rejects unconditional raw interpretation naturality
(`no_unconditional_interpretation_map`). Those negative controls should remain.
For the new boundary, test malformed raw reflexivity and equalities whose
operands are separately defined but have incompatible boundaries. Establish
rejection syntactically, not merely by making the semantic assumptions
unsatisfiable.

The second inspected client is
[UniversalTransfer.lean](../../SquareKit/Internal/PathTransport/UniversalTransfer.lean).
Its source `proof` is a selected `trConcat` derivation, consumed through
`TransferConsumer`; `transport_concat` observes
`B.map (p ≫ q) b = B.map q (B.map p b)` for a groupoid family B. Replacing its
proof by an independent proof of functoriality would retain the endpoint theorem
but omit the source recipe. A migration comparison should retain the translated
source proof, its complete family and selected term before deriving this
observation. This remains a concrete candidate, not a selection made by this
report. The #323 record supplies additional nested-J recipe comparisons; its
native examples do not establish the pending higher-provider requirements.

## Architectural consequences and alternatives

The paper offers a better **reference specification** for conventional dependent
typing and typed equality than declaring the guarded engine to be that calculus.
Its separately stated raw syntax, boundary formation and standardness conditions
provide falsifiable obligations. It also offers reusable construction ideas:
dependency-ordered annotations, boundary conversion, rulewise translation and
transport of metatheorems. Implementing the entire cf calculus would introduce
new annotation and assumption bookkeeping; no author-effort improvement has
been measured. An independent conventional calculus connected to the engine is
a smaller first experiment. Defining its derivations as wrappers around engine
derivations would lose the independent adequacy test.

Several architectural results already justify retention:

- [RepresentedFamilies.lean](../../SquareKit/RepresentedFamilies.lean) separates
  strict indexed families and a natural representing equivalence from signature,
  Id/J and a distinguished empty object. It derives projection, generic section,
  pairing, eta and pairing naturality. The
  [existing adapter](../../SquareKit/Internal/PathTransport/Representability.lean)
  recovers the old chosen operations. This gives #324 a concrete consumer
  boundary without first designing a new global hierarchy.
- [InterpretationMaps.lean](../../SquareKit/Internal/PathTransport/InterpretationMaps.lean)
  retains strict family/substitution equations and dependent term comparisons;
  `ModelMap.mapJ` names the transported telescope, motive and branch. A coherent
  comparison in #325 must construct corresponding family and section transport,
  chosen-J compatibility and composition. Equivalence of contexts alone does
  not supply them. The strict maps should remain a specialization.
- [Sigma/Capability.lean](../../SquareKit/Internal/DependentJudgments/Sigma/Capability.lean)
  supplies a pack/unpack isomorphism over the base. `pack_unpack` aligns the
  motive in `split_type`; both inverse laws derive split beta, eta, uniqueness
  and injectivity of restriction. [Sigma/Maps.lean](../../SquareKit/Internal/DependentJudgments/Sigma/Maps.lean)
  derives unpack and split preservation from formation and packing compatibility.
  Weakening the contract loses this inverse-uniqueness argument; it does not
  justify retaining the old implementation of split unchanged.

The equality distinctions must survive any new presentation. Host Lean equality
of semantic substitutions validates the current source judgmental equations;
it is neither Lean definitional reduction nor an inhabitant of the modeled Id
type. For a primitive dependent Sigma eliminator with computation and Id types,
the proposed eta proof is induction with reflexivity at each constructed pair.
The formal comparison and any genuine judgmental-eta separator belong to
[#331](https://github.com/VladimirMarko/conaled/issues/331), coordinated with
[#327](https://github.com/VladimirMarko/conaled/issues/327). Projection beta
alone does not supply arbitrary dependent elimination. If first-projection beta
is only a path, second-projection beta must compare in a common fiber using
transport. The finitary paper permits separately specified equality rules; it
does not prove the needed Sigma separation or select an equality strength.

There is also a source derivability check worth retaining. At the baseline,
[Sigma/Composition.lean](../../SquareKit/Internal/DependentJudgments/Sigma/Composition.lean)
proves semantic validity of a law extension for split eta. Since source split
is substitution along unpack, the candidate derivation is

```text
split A B (subTm t (pack A B))
  = subTm (subTm t (pack A B)) (unpack A B)
  ≡ subTm t (comp (pack A B) (unpack A B))
  ≡ subTm t (identitySub (extend Γ (sigma A B)))
  ≡ t.
```

The steps use the definition, term-substitution composition, Sigma eta with
congruence, and term-substitution identity. The four `splitEtaRule` premises
supply the family and term boundaries; pack/unpack typing must discharge the
composition guards. This is an unchecked source proof plan for #327, not a
new formal deliverable or an independence claim. The existing semantic proof
already requires no additional model-builder law.

Likewise, its explicit empty variable context and cf assumption discipline do
not prove terminality of the repository's ambient semantic context category.
[GeneratedContexts.lean](../../SquareKit/Internal/DependentJudgments/GeneratedContexts.lean)
constructs an empty substitution for extension-generated contexts; it does not
classify every arrow between them. A closed generated-arrow grammar and a
policy permitting arbitrary substitution constants are different statements.
[#330](https://github.com/VladimirMarko/conaled/issues/330) owns their formal
resolution. The paper helps specify declarations and distinguish implicit
assumptions, but supplies no automatic answer for our arrow grammar.

Alternative foundations remain legitimate comparisons. The existing
[dependent coherence comparison](dependent-coherence-comparison.md) and
[architecture reassessment](dependent-architecture-reassessment.md) separate
model construction from judgment interpretation. More specific alternatives
from the architectural assessment remain worth testing:

- Isaev's [*Algebraic Presentations of Dependent Type Theories*, v3,
  §§3–5](https://arxiv.org/html/1602.08504v3) uses partial Horn theories with
  substitution structure. Proposition 3.1 relates its structural models to
  contextual categories; Examples 5.3–5.4 specify projection/eta and
  primitive-eliminator sums separately. This is a candidate for modular
  definedness and extension machinery. It still needs a comparison with our
  context/substitution encoding and selected operations.
- Uemura's [*A general framework for the semantics of type theory*, published
  2023, Definitions 4.1–4.5 and §5](https://doi.org/10.1017/S0960129523000208)
  uses small representable-map categories and models as representable-map
  functors into discrete fibrations over a category with a terminal object.
  Its introduction excludes nontrivial context operations, including the cited
  dual-context/modal systems. It offers semantic organization and a logical
  framework, but is not automatically the full language ambition with crisp
  restrictions, nor an adapter from our weaker empty-context assumptions.
- Lumsdaine–Warren's [*The local universes model*, v2, Definition 3.1.3 and
  Theorem 3.4.1](https://arxiv.org/html/1411.1736v2) takes a full comprehension
  category satisfying LF and weakly stable constructor structure to strictly
  stable structure on a split replacement. LF requires finite products and
  the specified dependent exponentials for a display map followed by a display
  map or product projection. Section 4.1's extension discussion excludes
  type-equality rules from its general recipe. This addresses model construction;
  preserving a client's previously chosen J operation needs a further comparison.

These are different problems from Section 6's syntax translation. Section 7
of the finitary paper itself discusses logical-framework comparisons and leaves
formal adequacy comparisons open. No surveyed method automatically preserves
this repository's previously chosen J recipes. Compare alternatives on the same
dependent client and observation, including their assumptions. A direct source
calculus is the clearest initial adequacy test; an algebraic presentation tests
extension modularity; the semantic alternatives test model construction and
comparison. None is selected for adoption here.

## Bounded next steps and acceptance evidence

| Owner | Concrete investigation | Evidence needed |
|---|---|---|
| [#324](https://github.com/VladimirMarko/conaled/issues/324) | Run a selected structural consumer through the existing represented-family interface. | A provider without dummy signature or Id/J data, the old-model adapter, and recovery of selected projection, variable and pair. State which strict substitution assumptions remain. |
| [#325](https://github.com/VladimirMarko/conaled/issues/325) | Compare two different presentations of one dependent client. | Derived family/section/tail transport, motive and branch alignment, selected-J compatibility and composition of two comparisons; recover strict maps. Do not request the final client comparison as a field. |
| [#326](https://github.com/VladimirMarko/conaled/issues/326) | Specify structural/Id/J judgments, finite tails and declaration policy independently, then translate the chosen fragment into the engine. | Rule/boundary well-formedness and source presupposition proofs; separate schematic and object substitution theorems; Command-like J under nonidentity substitution; typed-equality negative controls. State forward preservation and interpretation agreement first. Attempt reverse reconstruction on an independently recognizable admitted fragment, recording any obstruction to reflection. |
| [#327](https://github.com/VladimirMarko/conaled/issues/327), with #331 | Compare primitive dependent split plus computation with strong Sigma. | Derived propositional eta, a justified separator for any claimed nonderivability, and an account of which uniqueness, stability and map results survive. Recover the strong specialization. Also check source split-eta derivability before claiming a law extension adds deductive strength. |
| [#328](https://github.com/VladimirMarko/conaled/issues/328) | Freeze one client's source recipe and semantic observation before bounded migration. | Complete dependent family and selected-term comparison under two substitutions, an observation detecting a lossy replacement, unchanged public entrypoints, and recorded adapter/author obligations. A directly proved client comparison can proceed without universal adequacy. |

For #326, acceptance of a forward translator must not be reported as reflection.
A reconstruction domain consisting only of translated derivations bundled with
their original proofs is insufficient evidence of adequacy. A judgment-level
admissibility predicate may still permit problematic raw intermediate steps;
the reconstruction theorem must quantify over the actual admitted derivations.
If reconstruction fails, preserve the forward theorem and classify the mismatch
with a concrete derivation or missing hypothesis. Initiality, conservativity,
all-model expansion and semantic soundness are separate claims.

Unresolved choices are the exact independent declaration policy, contextual-J
rule strength, reconstruction domain, coherent comparison data, and selected
migration client. The investigation sequence permits these choices to be
constrained by evidence without retiring successful interfaces. #107 remains
paused, #108 unselected/unprepared and #260 inactive.

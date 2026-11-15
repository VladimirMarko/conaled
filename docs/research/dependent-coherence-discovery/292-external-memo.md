# Dependent arguments across mathematical settings: external architecture memo

Phase A, 2026-11-04. This memo precedes inspection of the project's implementation, architecture documents, tracker, and historical examples. It proposes acceptance criteria and alternative designs; it does not assess the existing implementation. Exposure and access details are recorded in the accompanying source log.

The capability to design around is an author writing one dependent argument, substituting its parameters twice, and interpreting its terms and identity witnesses in different models. My recommendation is to specify that capability through a judgment interpretation contract first. Keep at least two model-construction routes open: local universes for suitable weak models, and directly supplied strict models, possibly constructed from a chosen classifying universe. This recommendation is an architectural inference from the sources below, not a claim that one of these routes already fits the project.

## Author capability, before an encoding

An author supplies mathematical parameters and a derivation. The infrastructure must provide:

1. Contexts with dependent extensions, well-typed simultaneous substitutions, and substitution into both types and terms.
2. An explicit distinction between judgmental equality, object-language identity, and comparison data between semantic presentations.
3. Interpretation of every admitted judgment and constructor into each advertised model.
4. Composition laws for substitution and interpretation, including the dependent types of the resulting witnesses.
5. A boundary at which a model builder proves that a new constructor satisfies the required rules. Routine use of that constructor should not require the author to repeat these proofs.

An interpretation need not be faithful on all paths. A model deliberately truncated to sets cannot distinguish every higher witness. The promise must instead name which observations each model supports and demonstrate that the common interface permits models in which those observations remain nontrivial. Requiring all models to preserve every distinction would rule out many useful interpretations; requiring only preservation of truth would miss the stated witness requirement.

Here is the proposed author test, stated independently of any host representation. Work over signature parameters `A type` and `a:A ⊢ B(a) type`. These are schematic parameters, so the test does not itself demand an object-language universe. Use the context

```text
Γ = (x,y,z:A,
     p,p′:Id_A(x,y), h:Id_{Id_A(x,y)}(p,p′),
     q:Id_A(y,z), u:B(x)).
```

Write `p·q` for traversing `p` and then `q`, and `tr_B(p,u)` for transport. Construct

```text
v(p,q,u) = tr_B(q, tr_B(p,u)) : B(z)
η(p,q,u) : Id_{B(z)}(v(p,q,u), tr_B(p·q,u))
w(p,q,u) = (v(p,q,u), η(p,q,u))
  : Σ(v:B(z)). Id_{B(z)}(v, tr_B(p·q,u)).
```

The construction of `η` is by identity elimination on `p` and `q`, with reflexivity in the reflexive case. Transport composition is Lemma 2.3.9 of the [HoTT Book](https://hott.github.io/book/hott-online-82-g578b85c.pdf). No uniqueness of identity proofs, equality reflection, univalence, function extensionality, or truncation is used in this derivation. The pair `w` explicitly makes the witness depend on the value it certifies.

There are two substitutions with dependent components:

| Substitution | Source context | Assignment to the target context |
|---|---|---|
| `σ : Δ → Γ` | `Δ=(x,z:A, ℓ,ℓ′:Id_A(x,x), h:Id(ℓ,ℓ′), r:Id_A(x,z), u:B(x))` | `y↦x`, `p↦ℓ`, `p′↦ℓ′`, `q↦r`; preserve the other components |
| `τ : Θ → Δ` | `Θ=(x:A, ℓ,ℓ′:Id_A(x,x), h:Id(ℓ,ℓ′), k:Id_A(x,x), u:B(x))` | `z↦x`, `r↦k`; preserve the other components |

The resulting term has the dependent type

```text
w[σ][τ] : Σ(v:B(x)). Id_{B(x)}(v, tr_B(ℓ·k,u)).
```

It must agree with `w[σ∘τ]` by the declared substitution law. This is a statement about substitution into a term and its type. It does not assert that all inhabitants of the resulting identity type coincide.

Retain `h` as data as well. With `K(p)=Id_{B(z)}(v(p,q,u),tr_B(p·q,u))`, dependent action gives

```text
apd_η(h) : Id_{K(p′)}(tr_K(h,η(p,q,u)), η(p′,q,u)).
```

The two substitutions must also apply to this expression, including its transported source. A comparison only between the endpoints of `η` is insufficient.

Two observations prevent a vacuous success:

- **Path-dependent transport.** Interpret `A` as the one-object groupoid of integers under addition. Interpret `B` as the action on the discrete integer groupoid in which a loop `m` sends `n` to `n+m`. Set `ℓ=ℓ′=1`, `h=refl`, `k=2`, and `u=0`. The transported value is `3`; replacing the first loop by reflexivity gives `2`. This proposed instance is derived directly from the group action. The general legitimacy of proof-dependent transport is supported by Hofmann and Streicher's groupoid model, whose identity types are discrete hom-groupoids and which refutes UIP. [Hofmann–Streicher, §§3–5](https://people.csail.mit.edu/jgross/personal-website/papers/academic-papers-local/agroupoidinterpretationoftypetheroy.pdf)
- **Higher identity.** In a model containing a pointed type `(A,x)` with a nontrivial second homotopy group, specialize `B(y)=Id_A(x,y)`, `u=refl_x`, and `ℓ=ℓ′=k=refl_x`. Keep `h:Id(refl_x,refl_x)` nontrivial. The map `T(p)=tr_B(p,refl_x)` is pointwise identified with `p` by identity induction. Writing `β_p:T(p)=p` for this identification and `e=refl_x`, its naturality gives `β_e⁻¹ · ap_T(h) · β_e = h`. Thus the observation retains `h` after explicit endpoint identifications. This is my proposed preservation test; it does not assert that `apd_η(h)` itself must be nontrivial. A sphere supplies a familiar witness setting: the [HoTT Book, Corollary 8.5.2](https://hott.github.io/book/hott-online-82-g578b85c.pdf) establishes `π₂(S²)≃ℤ`. That existence theorem has the book's additional homotopical assumptions; the generic transport argument does not. A semantic sphere may instead be supplied as a model parameter without adding a sphere constructor to the author language.

The groupoid observation alone cannot certify unrestricted higher identity. Conversely, a higher-dimensional model can interpret the same generic derivation while supplying a different instance of `A,B`. There is no claim that these distinct parameter instances are connected by an automatically supplied functor of models.

## What the external results establish

**Local universes.** For a full comprehension category, `(LF)` requires finite products and categorical dependent exponentials `Π_f(g)` when `f` is a display map and `g` is a display map or product projection. These exponentials need not be types of the object language. Theorem 3.4.1 transfers the specified weakly stable constructors to strictly stable constructors in `C!`: binary sums, Π, Id, Σ, zero, unit, and W relative to a stable class of Π-types. A type is represented by `(V,E,a:Γ→V)`; substitution changes `a` by composition. These are model-construction facts. They do not identify object identity with equality of arrows. Section 4.1 gives a heuristic, not a general theorem, for further constructors; type-equality conclusions are excluded, and infinitary rules need stronger limits. The alternative right splitting `C*` carries constructors when their entire structure is pseudo-stable, including eliminators (Lemma 2.4.2). Weak existence of eliminators does not provide that hypothesis. [Lumsdaine–Warren, §§2.4, 3.1, 3.4, 4.1](https://arxiv.org/pdf/1411.1736)

**Direct models through presheaves.** For a small context category `C`, a representable natural transformation `Tm→Ty` of set-valued presheaves packages types, terms, substitution, and context extension. This is equivalent to the CwF presentation. Intensional identity additionally needs the identity and reflexivity maps plus the specified left-lifting structure of Proposition 20. Representability alone does not provide it. Awodey's general construction theorem is related to, and explicitly credits, local universes; it should not be counted as an independent strictification theorem. The direct interface itself nevertheless permits a model to be supplied without using that construction theorem. [Awodey, §1, Proposition 20, Remark 34](https://arxiv.org/pdf/1406.3219)

**Models from one chosen universe.** Given a category, terminal object, a map `p:Ũ→U`, and chosen pullbacks of `p`, Proposition 1.3.3 constructs a contextual category from finite sequences of classifying maps. Theorem 1.4.15 transfers the corresponding constructor structures on that universe to the contextual category; its development uses a locally cartesian closed ambient category. The theorem does not say that an arbitrary classifier automatically supplies these structures. This paper also constructs a simplicial model with a univalent universe, under its stated inaccessible-cardinal assumptions. [Kapulkin–Lumsdaine, §§1.3–1.4 and 3.4](https://arxiv.org/pdf/1211.2851)

**Extensional categorical equivalences have a narrower target.** The corrected LCCC correspondence is a biequivalence involving democratic CwFs with extensional identity, Σ, and Π, with suitable structure-preserving pseudomorphisms. It is not a result that every intensional model is equivalent to an LCCC carrying extensional equality. [Clairambault–Dybjer, §§2–5](https://arxiv.org/pdf/1112.3456)

**New rules need a specification.** Bauer, Haselwarter, and Lumsdaine distinguish raw theories from acceptable theories. Acceptability includes tightness, presuppositivity, substitutivity, and congruity; well-founded presentation is a further condition. Their metatheorems provide evidence that checking the shape and dependencies of new rules is substantive work. [Bauer–Haselwarter–Lumsdaine, Definitions 5.12 and 6.20](https://arxiv.org/pdf/2009.05539)

These sources support a separation of responsibilities. They do not establish that a particular collection of host-language interfaces already interprets all the judgments an author expects.

## A judgment interpretation contract

The following is a proposed theorem obligation, not a theorem proved in this memo.

Fix a specified fragment `T` and a presentation `Syn(T)` with its structural and judgmental equality rules. Assume its initiality for the chosen class of strict structured models has been established. Given a model `M` supporting exactly those rules and an interpretation of the primitive signature satisfying its declared judgments, initiality supplies the corresponding structure-preserving interpretation. The signature assignment is part of the hypothesis. Neither the existence of a runtime evaluator nor merely naming a category a model discharges it.

The required observable equations include

```text
⟦σ∘τ⟧ = ⟦σ⟧∘⟦τ⟧
⟦A[σ]⟧ = ⟦A⟧[⟦σ⟧]
⟦t[σ]⟧ = ⟦t⟧[⟦σ⟧]
⟦w[σ][τ]⟧ = ⟦w⟧[⟦σ⟧∘⟦τ⟧].
```

All these are equations in the metatheory describing the interpretation. The last equation has the interpreted dependent Σ-type as its type. Separate clauses must interpret `Id`, reflexivity, `J`, its computation rule, and the derived terms `η`, `apd_η(h)`, and `ap_T(h)`.

If model morphisms preserve structure only up to isomorphism, replace the displayed equations with specified comparisons and prove their unit, composition, and constructor compatibility. A list of unrelated isomorphisms is not enough. In particular, the term comparison must use the associated type comparison. Whether to expose strict or pseudo morphisms is an architectural choice whose cost should be measured on the example.

Initial syntax is one possible implementation of this contract. A parametrically authored derivation over a semantic interface is another candidate, provided its allowed operations and parametricity are controlled and its interpretation theorem is supplied. It should not be assumed that arbitrary host functions are automatically syntax-independent derivations. A bounded fragment sufficient for the example is enough to begin; no full proof assistant or universal syntax generator is proposed here.

Ordinary metatheoretic equality can be proof irrelevant without collapsing the object-language identity type, because the latter is separate modeled structure. Conversely, representing every object identity witness by a host proof-irrelevant equality would fail the observations above. Having a one-category of contexts is not itself such a representation choice.

## Competing architecture proposals

The following comparison is my assessment of the obligations, not a ranking of an unseen codebase.

| Proposal | Model-builder work | Author-facing work | Decisive limitation |
|---|---|---|---|
| Weak models plus local universes | Establish the comprehension structure, LF, each required weak-stability condition, and the connection to the judgment interface | Use the derived operations and substitutions | The advertised theory may require a rule outside the proved transfer result, especially a strict type equation |
| Direct strict CwF or natural model | Supply context extension and substitution laws, constructors, eliminators, and their strict stability directly | Use the same judgment interface | A semantic construction may provide only weakly stable choices; direct strict data may be expensive or unavailable |
| One chosen classifying universe | Select represented families, chosen pullbacks, and all required constructor/closure structures; build the contextual model | Use codes only if the author language itself needs a universe | A needed family may lack a code, or a needed operation may lack suitable closure and computation data |
| Right splitting of pseudo-stable structure | Supply coherent preservation of the complete constructor data, including chosen eliminators | Use the resulting strict interface | Pointwise existence of `J` does not produce its required coherent choices |

A CwF is a possible common interface for these routes; choosing it does not by itself choose local universes or solve strictification. Likewise, changing the public interface to the natural-model presentation while retaining the same model-construction proof may be useful, but it is not an independent escape from that proof's hypotheses.

There is room for substantial replacement. If the current design, once inspected, identifies the author language with one execution mechanism, replacing that boundary with the judgment interpretation contract could be justified even if it retires substantial code. If it already has a suitable contract, a local-universes adapter could be an incremental addition. If all intended models admit convenient direct strict presentations, implementing a general weak-model strictifier may have little immediate value. If local universe records leak into routine proofs, hide them behind the interface or reconsider the model-construction route. None of these cases can be decided during the isolated stage.

## Admission obligations and failure tests

Every proposed new structure should state its formation context, introduction and elimination judgments, computation and uniqueness rules, and all dependencies on earlier structures. It should then supply its interpretation, substitution compatibility, and any model-morphism compatibility. If a transfer theorem is used, name the theorem and prove its hypotheses for that structure. A provider may state a weaker supported fragment; an author should not discover that weakening through an unexplained failed transport.

The following tests distinguish architectural success from merely compiling a diagram.

| Test | Required evidence | Failure means |
|---|---|---|
| Dependent context extension | The contexts and substitutions above typecheck with the displayed dependencies | The author interface has not demonstrated genuine dependency |
| Two substitutions | The law for `w`, its Σ-type, and `apd_η(h)` is established from infrastructure laws | Repeated substitution still leaves term-specific bookkeeping with the author |
| Monodromy | The integer-action instance distinguishes outputs `3` and `2` | Transport has erased its path input or the model contract is too weak |
| Second identity | The path-family instance admits nontrivial `h` and identifies the observation `ap_T(h)` correctly | Only one-dimensional witness behavior has been established, or higher identity is being truncated |
| Elimination, not just formation | `J` interprets arbitrary admitted motives and its computation equation survives substitution | Stable identity-type objects alone do not support the author proof |
| New-rule dependency | A new rule using an earlier constructor has an explicit stability proof for all allowed input structures | A nominal extension mechanism has hidden mathematical obligations |
| Strict type equations | Any promised equation such as `El(codeΣ(a,b)) ≡ Σ(El(a),El(b))` has its own semantic proof | A constructor transfer theorem has been overextended |
| Changed presentation | Equivalent choices of model presentation have explicit comparisons on the observed terms | Meaning may depend on untracked implementation choices |

The monodromy and higher-identity instances also expose invalid shortcuts. A family of sets with only proof-irrelevant equality can pass ordinary substitution tests but cannot serve as the sole model of the required path behavior. Passing to homotopy classes may retain some first-level information while deleting the second-identity observation. Neither shortcut becomes acceptable merely because it simplifies a coherence proof.

For the local-universes route, failure to establish LF or the required weak stability blocks that application of the theorem; it does not prove that the mathematical setting has no other type-theoretic model. For the direct route, proving only the ordinary category laws is insufficient: dependent context extension and stable eliminators remain obligations. For the fixed-universe route, an unrepresented family is a concrete coverage failure. For right splitting, the missing object is a coherent choice of eliminator, not just an additional equality lemma.

## Decision boundary for phase B

Phase B should first map the actual author requirements to the example and the interpretation contract. Then inventory which model constructions and theorem hypotheses are already present. Compare repair, replacement of the public boundary, and replacement of the model-construction route separately. A small repair is preferable only if it earns the same author capability; a large replacement is justified only if its new obligations can be stated and tested.

This memo has not established machine-checked syntax initiality, constructed a model, or verified the proposed observations in project code. The cited results make the alternatives mathematically credible. The tests above identify the remaining evidence needed to select among them.

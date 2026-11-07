# Denotation boundaries, settings, and compositional satisfaction

This inspection answers the 2026-11-07 discussion under
[#235](https://github.com/VladimirMarko/conaled/issues/235). It separates existing
Lean definitions, pinned upstream implementations, and proposed experiments.
No square interface or Lean declaration changes here. The related
[calculus transport note](calculus-satisfaction-and-transport.md) supplies the
earlier comparison; [source provenance](../SOURCES.md) pins Felix and the
language-derivatives source.

## Type-valued languages are already the specification

Elliott's pinned
[Language.lagda](https://raw.githubusercontent.com/conal/paper-2021-language-derivatives/fc7fd2b31f8fedc0ee7f4b59c28aa2810c82b2e4/Language.lagda)
defines `Lang = A ✶ → Set ℓ`: a word indexes a type of membership witnesses.
Union retains a tagged choice, concatenation retains a word split and both
parses, and star retains component parses. The corresponding
[Symbolic.lagda](https://raw.githubusercontent.com/conal/paper-2021-language-derivatives/fc7fd2b31f8fedc0ee7f4b59c28aa2810c82b2e4/Symbolic.lagda)
indexes executable syntax by its semantic language and returns a decidability
result carrying a witness or refutation. The mathematical specification does
not supply a general executable procedure deciding every such language.

This pattern is present locally, not displaced by Boolean semantics:

| Existing declaration | Preserved information |
|---|---|
| `LanguageWitnesses.Language` in [Witnesses](../../Applications/Languages/Witnesses.lean) | `List α → Type u`, with actual parses as inhabitants. |
| `Concat`, `Star`, `derivativeConcatIso`, `derivativeStarIso` there | Split words, constituent parses, and nullable parses needed by the derivative laws. |
| `Parser P`, `Parser.parse` in [Parser](../../Applications/Languages/Parser.lean) | Syntax indexed by its witness language; a `Decision (P w)` selects a parse or refutes all parses. |
| `WitnessTrie.lookup` in [WitnessTrie](../../Applications/Languages/WitnessTrie.lean) | A selected decision for a word within a finite observation depth. |
| `recovered` in [IndexedCompositional](../../Applications/Languages/IndexedCompositional.lean) | Equality of selected decisions between parser and trie interpretations for arbitrary constructor terms and in-bound words. |
| `contextual_exact` in [ExactRewrites](../../Applications/Languages/ExactRewrites.lean) | Exact observation preservation through finite constructor contexts. |

[ParserBridge](../../Applications/Languages/ParserBridge.lean) explicitly
forgets witnesses with `Nonempty` and `Decision.test` to compare the separate
Boolean recognizer. `recognizers_agree` proves agreement at that layer; it does
not redefine the witness language. A generic warning about Boolean observers
must not be presented as a description of the primary parser specification.
[ADR 0004](../adr/0004-convolution-and-languages.md) already makes this division.

The automatic representation uses finite observations, rather than a direct
copy of the upstream coinductive implementation with termination overrides.
This constrains that implementation technique, not the type-valued denotation.
The parser returns one valid witness, not an enumeration of all ambiguity.
These distinctions should remain visible when assessing parity.

## Felix certifies laws but does not hide every representation

At the pinned Felix revision,
[MakeLawful.agda](https://raw.githubusercontent.com/conal/felix/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/MakeLawful.agda)
derives source category laws using source equivalence induced by a
homomorphism. It does not require raw source arrows to become identical.
[Homomorphism.agda](https://raw.githubusercontent.com/conal/felix/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda)
separates congruence and preservation of identity/composition, and composes
those witnesses.

However,
[Comma/Type.agda](https://raw.githubusercontent.com/conal/felix/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda)
exposes constructor `mkᵐ`, component fields `f₁`, `f₂`, and the commuting proof
`↻`. Its forgetful homomorphisms project either component. Its own equivalence
observes both components through a product homomorphism. These definitions
provide typed certification, not a universal abstraction barrier preventing
all clients from accessing implementation data.

Locally, [Squares](../../Squares.lean) likewise exposes `Rep.R`, `Rep.S`,
`decode`, `Square.impl`, and `Square.spec`.
[CategoryMap](../../SquareKit/CategoryMap.lean) provides the semantic mechanism:
`RawMap.induced` pulls back the target equivalence; `inducedLaws` derives map
laws; `transportLaws` transfers category laws; `comp_laws` composes certified
maps. Equality of meanings does not imply equality of representations.

**Recommendation:** distinguish representation-aware compiler clients from
clients admitted at a semantic interface. For the latter, every admitted
operation must respect the specified equivalence or richer interpretation
contract. A cache or hidden bit may affect the compiler's choices while its
semantic result remains fixed. A semantic client that reports the hidden bit
as an observable Boolean would require an additional specification and proof.
Merely exposing a raw carrier alongside a setoid does not enforce this rule.

The extra-flag pair example is therefore a separation of contracts, not an
objection to redundant pair representations. If the independent denotation
forgets the flag and every semantic-client operation respects that denotation,
repacking may satisfy the specified pair law without preserving the flag.
The checked weak-pair countermodel addresses a different, explicit contract:
its stronger law asks for equality of the interpreted substitutions themselves.
Its failure cannot be used to conclude that a flag-forgetting pair realization
is invalid under a different semantic contract.

Possible enforcement mechanisms include an abstract interface, quotient
elimination with respectfulness obligations, or typed syntax whose interpreters
certify every operation. These are candidates for the experiment, not adopted
changes. Quotients can discard relevant identity witnesses, so they are not a
universal solution for higher settings. Exposing only denotation *respecting
operations* also need not mean evaluating and returning an entire denotation,
which may be non-executable.

## Equality requirements belong to the specification

An implementation relation may differ from specification equality. The
interpretation must establish the direction needed by a client. If an operation
claims to *decide* specification equality, a finer representation equality is
insufficient: it can reject distinct representations of equal meanings. A
sound incomplete prover has a different contract. The specification therefore
constrains the comparator's behavior even though it does not prescribe its
algorithm or representation.

The appropriate record for an issue is its semantic acceptance contract:
required operations, object equality or identity data, interpretation relation,
and preservation guarantees. It is not an exhaustive catalogue of equality
flavors exercised by unrelated tests. Such contracts can be parameterized by
a setting. Lean remains the host: its own equality is fixed, while it can
represent many relations and identity structures as mathematical data. The
current guarded engine's built-in equation atom uses host equality in its
model semantics; modeled identity is separate. Consequently, current support
does not establish a universal encoding of every equality or pair structure.
See [GuardedTheory](../../SquareKit/GuardedTheory.lean) and the
[pair comparison](primitive-dependent-sums.md).

## What the finitary-calculus study produced

The [#332 study](finitary-type-theories.md) informed completed #326 work:

- [ReferenceCalculus](../../SquareKit/Internal/DependentJudgments/ReferenceCalculus.lean)
  defines boundaries and an independent typed derivability relation.
- [ReferenceSignature](../../SquareKit/Internal/DependentJudgments/ReferenceSignature.lean)
  checks ordered family/term declarations and their presuppositions.
- [ReferencePresuppositions](../../SquareKit/Internal/DependentJudgments/ReferencePresuppositions.lean)
  extracts typed equality operands and substitution contexts.
- [ReferenceSubstitution](../../SquareKit/Internal/DependentJudgments/ReferenceSubstitution.lean)
  transports derivations under schematic instantiation.
- [ReferenceTranslation](../../SquareKit/Internal/DependentJudgments/ReferenceTranslation.lean)
  defines `translate`, inductively constructing guarded derivations in the
  named telescope extension.
- [ReferenceDependentCalculus](../../Examples/ReferenceDependentCalculus.lean)
  exercises the bounded source fragment.

These are existing formal artifacts informed by the paper's boundary discipline
and comparison obligations. They are not a Lean port of its general framework.
In particular, the reference calculus shares raw constructor/substitution
machinery with the engine, although its inference relation is separate.
Haselwarter and Bauer compare contextual and annotated context-free
presentations of finitary theories. We have not implemented both general
presentations and their bidirectional correspondence. The completed local
translation targets an explicitly extended engine; it proves neither arbitrary
reverse translation nor conservativity. See the
[paper, §§2–6](https://arxiv.org/html/2112.00539v1) and
[current result boundary](reference-dependent-calculus.md).

## Satisfaction alongside computational squares

For an institution, a signature map carries sentences forward and models
backward. Its satisfaction condition equates satisfaction of a translated
sentence with satisfaction in the reduct model. This is already a two-sided
compatibility condition, but its opposite directions do not provide an inverse
compiler. Cross-logic translations require additional institution-level maps;
they are not merely signature maps. See Goguen and Burstall,
[Definition 1 and the institution-morphism development](https://courses.grainger.illinois.edu/cs522/sp2016/InstitutionsAbstractModelTheory.pdf).

**Proposed specialization:** write satisfaction as `Sat(M, φ)`. Compare the
two routes from `(M', φ)` to propositions:

```text
(M', φ) ↦ (M', translate φ) ↦ Sat_target(M', translate φ)
(M', φ) ↦ (reduct M', φ)    ↦ Sat_source(reduct M', φ)
```

An equivalence of the resulting propositions states the satisfaction condition.
To preserve selected evidence, replace the final proposition by an explicitly
specified evidence type and ask for the needed maps and coherence. Ordinary
satisfaction equivalence does not furnish those evidence maps automatically.
An execution implementation can then be connected to this semantic layer by
a separate correctness square. This gives a candidate composition of
computational correctness and satisfaction transport, not a theorem that
their existing APIs coincide.

The [theory-network comparison](theory-network-comparison.md) already records
a failed extension and distinguishes these directions. The next experiment
should test two successive routes, a shared client, retained witnesses, and
an unsupported extension. It should establish reuse before introducing a
library-wide institution or double-category interface. No current square
interface change follows from this note. The cross-logic comparison is now
tracked in [#340](https://github.com/VladimirMarko/conaled/issues/340), under
#290; the compositional specification experiment is
[#339](https://github.com/VladimirMarko/conaled/issues/339). A same-logic
specialization of the latter would not by itself complete the former.

## Settings do not automatically provide terminating normalization

Separate four activities: representing derivations, checking explicit
certificates, searching for certificates, and evaluating programs. A semantic
setting need not come with a normalization algorithm. Even if it does,
soundness of that algorithm does not establish termination or completeness.
A parameterized argument can retain explicit equality steps and assumptions
without normalizing every possible interpretation.

There is a direct primary comparison: Bauer and Petković Komel's
[extensible equality checker](https://arxiv.org/html/2103.07397v4), introduction,
proves soundness while explicitly allowing nontermination and unpredictable
behavior. It does not claim general completeness. Andromeda's
[object-theory interface](https://www.andromeda-prover.org/type-theory.html)
keeps judgments under nucleus control and delegates substantive equality
construction to user code. This is evidence that generic settings and checked
evidence can coexist; it does not remove the algorithmic tradeoff.

**Recommendation:** keep equational validity separate from an admitted rewrite
strategy. A rewrite package needs its own operational contract, such as a
termination argument or bounded proof-producing search. For example, orienting
commutativity naively in both directions creates a loop even though each step
is valid. A bounded search can report failure to find a proof without treating
that failure as inequality. When extensions are combined, reassess their joint
computational properties; individual proofs do not automatically establish
the combined strategy's termination or confluence.

Checking a finite certificate by recursion is a separate achievable contract
when its primitive checks are effective and bounded. No blanket termination
claim for arbitrary object theories, elaborators, or host conversion follows.
Lean's own [kernel discussion](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)
also cautions against claiming unconditional type-checker termination.
The conversion-extension research in
[#338](https://github.com/VladimirMarko/conaled/issues/338) should include these
distinctions.

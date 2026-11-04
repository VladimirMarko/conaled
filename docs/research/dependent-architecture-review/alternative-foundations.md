# Alternative foundations for reusable dependent arguments

**Keep the four responsibilities as questions to answer, but do not freeze them
as four independent layers.** Model morphisms help determine what counts as a
uniform argument; changes of setting can occur inside judgments; chosen
coherence data can affect the interpretation being compared. These interlocks
could require a different architecture, not additional fields on today's records.

This is the third requested architectural challenge, dated 2026-11-04, against
`d108142`. I previously coordinated that candidate's integration review and read
both completed reports, the discovery memo and repository direction. This is
therefore not an unexposed discovery exercise. I have neither read the other
two challenge drafts nor coordinated conclusions with their authors. The sources
below were inspected afresh; their absence from the original memo's source log
does not establish that the repository never considered them. No new theorem or
implementation is delivered here.

## Author representations need separate comparisons

The [external memo](../dependent-coherence-discovery/292-external-memo.md)
correctly leaves initial syntax and controlled parametric derivations open.
Local universes and chosen universes answer a different question: how to obtain
models with the required structure. Choosing either construction does not choose
how authors express arguments.

| Author representation | Evidence needed before adoption | Main risk |
|---|---|---|
| Explicit judgments with initial/generalized-algebraic syntax | Interpretation and equality-respect for the admitted rules; a usable author interface | An initiality theorem for the wrong rules or morphisms |
| Uniform derivations over semantic interfaces | A construction discipline that establishes uniformity under the intended maps | Host operations or classical choices that depend on representation |
| Controlled shallow embedding | An abstraction boundary and translation accounting for allowed host reasoning | Helpful host conversions importing stronger object equations |
| Mode-indexed dependent judgments | Rules and comparisons for changing modes inside dependent contexts | Assuming all setting changes can happen outside the argument |

Bezem, Coquand, Dybjer and Escardó define valid generalized-algebraic signatures
using uniform families of contexts, types and terms over structured CwFs. A
uniform term family commutes with every strict structure-preserving morphism.
Their Theorem 1 constructs an initial CwF for each valid signature; §3 explains
how uniform families correspond to syntax in that initial object. This gives
positive evidence for relating semantic authoring and initial syntax, rather
than declaring them incompatible. The result concerns their signatures and
strict morphisms; it supplies neither unrestricted higher coherence nor a
parametricity theorem for arbitrary Lean functions.
[GAT paper, §§3–4](https://arxiv.org/pdf/2012.08370)

My proposed rejection test is deliberately small. Classical selection supplies
an element of each nonempty carrier, but cannot commute with the swap of Bool:
that would require a fixed point of negation. Thus “a result in every model” is
weaker than a uniform reusable argument. Restricting the comparison category
until this selection appears natural would conceal the missing capability.
The author representation and the intended changes of setting must be tested
together.

Kaposi, Kovács and Kraus establish an injectivity result for a shallow embedding
and use implementation hiding to prevent illicit constructions. However, §8.2
expressly leaves the general moral-correctness translation unformalized and
discusses postulated initiality. Their result therefore supports investigating
controlled shallow authoring, not assuming that abstraction automatically
provides a checked recursor into every model. Their treatment of mismatched
host/object equalities also makes the equality boundary a concrete experiment.
[Shallow embedding, Theorem 2, §§6, 8.1–8.2](https://arxiv.org/pdf/1907.07562)

## Changes of setting can belong inside the language

Uemura's representable-map framework relates type theories and models through
a biadjunction; the resulting biequivalence singles out democratic models.
It offers a semantic account of judgments and interpretations without selecting
one concrete syntax presentation. But the paper explicitly takes substitution
as model structure and excludes nontrivial context operations, including the
modal systems discussed there. Adopting its framework would not itself prove
substitution admissibility for new raw rules or cover every contextual
discipline. [Uemura, §§1.2, 7.3–7.4](https://doi.org/10.1017/S0960129523000208)

MTT supplies a distinct stress case. Its mode theory includes modalities and
transformations; locks act contravariantly on contexts, with explicit equations
for modal substitutions and their naturality. Modal comprehension connects
these context operations to types and terms. Thus a change of mode participates
in formation and variable use, rather than merely translating a completed
argument between externally chosen models. [Gratzer et al., §§2, 4–5 and
Figure 3](https://www.danielgratzer.com/papers/multimodal-dependent-type-theory.pdf)

This does not identify modes with the project's [internal setting
construction](../../../GLOSSARY.md). Nor does an internal-language theorem
automatically construct a setting from object-language presentation data. My
proposed missing test is a presentation `P` varying over a base context, with
an interpreted setting `S(P)`. Substituting `P` and then constructing its setting
must compare coherently with constructing first and reindexing. Test terms,
dependent witnesses and two successive substitutions. A collection of unrelated
external model instances cannot establish this contract. A successful modal
comparison would still leave this internal-presentation test to discharge.

## Higher semantics changes what comparisons must retain

Awodey's natural-model presentation makes context extension representability
of a presheaf map. Identity elimination requires additional chosen lifting
structure; representability alone does not supply `J`. This is useful compression
of obligations, but placing that lifting structure in an interface does not
construct it. [Natural models, §1 and Proposition 20](https://arxiv.org/pdf/1406.3219)

Nguyen and Uemura's higher framework is another credible foundation to assess.
Theorem 6.2 identifies a localization of theories with the relevant
finite-limit infinity-categorical semantics. This is a result about structured
theories and equivalences after localization, not equality of concrete
presentations. Its coherence construction uses substantial model-category
machinery. The Π-extension has additional universe hypotheses; extensions
including higher inductive types are left open. It therefore challenges the
need to make strict presentations fundamental without delivering a cheap
replacement implementation. [Infinity-type theories, Theorems 6.2, 6.25,
§§6.2–7](https://higher-structures.math.cas.cz/api/files/issues/Vol9Iss1/NguyenUemura)

For this project, meaningful comparison should preserve the specified dependent
observations, without requiring every interpretation to be faithful. A
set-valued interpretation may intentionally identify paths. At least one
advertised higher interpretation must retain the memo's nontrivial second
identity, and the supported comparison must identify its image correctly.
Object identity need not be host equality; ordinary categories of contexts do
not by themselves force object identity to be proof irrelevant.

The proposed four-part separation is incomplete if it specifies term maps
without their type comparisons, independent substitution comparisons without
composition coherence, or `J` preservation only for the displayed example's
motive. A candidate must account for arbitrary admitted motives, computation,
reindexing and the dependent types of selected witnesses. Strict maps,
pseudomorphisms and higher comparisons impose different obligations. We should
derive the needed list from the chosen semantic structure and universal
property, then test omissions, rather than hand-pick a few convenient diagrams.

## Discriminating follow-ups

These are proposed acceptance criteria, not claims that a replacement already
satisfies them. Preserve #107's repair boundary and #108's independent trial.

1. **Compare author representations first.** Express the memo's same dependent
   transport argument in explicit initial syntax and a controlled uniform
   interface. Include `apd_η(h)` and both substitutions. Identify which laws
   follow from interpretation and which the author must prove. Give an actual
   translation or a precise missing theorem; reject unrestricted classical
   selection as uniform authoring. Compare mathematical capability separately
   from elaboration cost.
2. **Test contextual setting construction.** Use a nonconstant internal
   presentation `P`, a construction `S(P)`, and a second construction depending
   on it. Prove the reindexing comparison and its composition law on selected
   dependent data. If this forces changes to judgments, revise the proposed
   separation instead of relegating the capability to an external adapter.
3. **Construct one demanding model and one comparison.** Retain a nontrivial
   second identity with contextual `J`; prove the memo's observation under both
   substitutions. Compare two presentations with explicit dependent transport.
   Reject a proposed comparison that preserves truth while erasing the promised
   witness. Do not replace this deliverable by a record assuming all its laws.
4. **Add a rule that depends on an earlier constructor.** Show how its
   interpretation and comparisons compose, and expose an unmet hypothesis in a
   failing target. Reject the architecture if each client must repeat the same
   semantic alignment or if adding a rule silently strengthens old models.

The current [#292 results](../dependent-coherence-comparison.md) justify pursuing
these tests: dependent Type-family stability is constructed, while the higher
adoption condition and concrete groupoid LF package remain open. They do not
rank the alternatives above. A failed shallow interpretation theorem, a needed
modal judgment outside the chosen framework, or a context-indexed setting that
cannot be expressed would each justify replacement of a proposed foundation.
The next decision should depend on those failures and capabilities, rather than
the number of compatibility fields we can add.

This assessment inspected the linked primary texts and named sections, not all
proofs or implementation artifacts of those projects. It supplies no Lean
formalization, benchmark or author-usability measurement. Its architectural
recommendations and rejection tests are inferences from the sources and the
project's stated capabilities.

# Extension discovery: post-freeze comparison

2026-11-04. The independent initial memo `/tmp/conaled-280/extension.md` remains unchanged. This memo was written only after freezing it and reading the three assigned reports and the cached issue bodies. It makes no repository or tracker changes and implements nothing.

## Result and changed ordering

The first discovery's broad recommendation mostly **confirms existing decisions**. #254 already separates extension guarantees, examines general rule frameworks and specifies effect interaction laws. #267 already proves observation refinement, quotient descent, and a no-factor counterexample with actual selected parser witnesses. #278 already owns constructor/observer cross-interaction and extension-order questions. #262 already owns admissible semantic type extensions and retention of a chosen old client. Repeating these discoveries does not justify new implementation tickets.

The genuinely new next question is narrower: **when does adding a representation sort preserve every model in a stated class, rather than merely extending selected interpretations?** First-order Morita extensions provide a concrete challenger for D2. Dependent Morita equivalence provides a relevant but much more conditional connection to D1; it does not displace the existing coherence comparison or permit erasing higher identity.

My extension-specific ordering is: bounded D2 representation-sort comparison first; existing D1 coherence work when its actual client requires it; effect interaction and richer observations through their existing owners. The parent's proposed overall sequence places a separate proof-requirement extraction comparison before this D2 task. That is compatible with these findings, but this extension track supplies no independent evidence for ranking extraction against D2. Do not infer an endorsement of its sources from this memo.

## Accepted evidence versus additions

| Initial finding | Comparison with inspected prior evidence | Consequence |
| --- | --- | --- |
| Distinguish derivation inclusion, consequence reflection, interpretation extension and normalization | Explicit in #254 and #259 | Confirmation, no new work item. |
| New observations can invalidate use of an old identification | Stronger checked evidence already in #267 than my operational counterexamples | Reuse #267; MMR is a useful literature control, not a new prototype. |
| Separate effect structures need interaction laws | HPP and a same-cell overwrite failure already in #254; #278 owns mixed extensions | 3MT adds a proof-factoring example, not a reason to replace current interfaces. |
| Institutions describe theory/model changes without a universal syntax | Already in D2 and the prior foundations comparison | General architecture vocabulary, not a new priority. |
| Morita extension gives a certified class of representation-sort additions | Not developed in the three inspected reports or assigned issues | Real D2 challenger; test scope, witnesses and naturality rather than merely adding another signature. |
| Equivalence stable across cofibrant dependent extensions | New full-text follow-up below | Add a conditional D1/D2 alternative and limits, without a new ticket now. |

The negative cases are not claims that existing scoped theorems are false. They test proposed stronger interpretations of those theorems.

## The model quantifier matters

For an extension map i:T→T⁺, write U:Mod(T⁺)→Mod(T) for reduct. The following is a proposed comparison vocabulary, not a claim that one source identifies all notions:

- **Selected-model extension:** for the specified M, construct M⁺ and an identified reduct U(M⁺)=M or an explicit comparison. This is enough for that client. It does not establish an expansion for any other model.
- **Expansion over a class C:** for every M in an explicitly stated C⊆Mod(T), establish such an expansion. C may include admissibility conditions; claiming C is all models is stronger.
- **Functorial expansion:** give compatible action on allowed model maps and coherence. Pointwise existence alone does not provide an algorithm or a natural choice.
- **Representation-only extension:** require uniqueness up to the specified isomorphism over the old model and suitable formula/term translation, not just existence.
- **Replacement up to weak equivalence:** construct a new model connected by a named weak equivalence. This may change the old carrier and strict equalities, and is not literally extension on the same carrier.

In a satisfaction-compatible setting with isomorphism-invariant truth, universal expansion gives a short countermodel argument for semantic conservativity: an old countermodel to an old sentence expands to a countermodel of its translation. Over C, the conclusion is only C-relative. Derivability reflection additionally needs an appropriate soundness/completeness or syntactic argument. Retention of a particular proof object is another condition. This is my elementary inference from the definitions, not a newly sourced general conservativity theorem.

A precise relative failure: take T with a nonempty sort A and an unconstrained predicate P. Extend by c:A and P(c). The model A={0}, P={0} expands; the model A={0}, P=∅ does not. The extension entails the old-language sentence ∃x.P(x), which T does not entail. One successful interpretation cannot justify universal model preservation. Restricting the model class to P-inhabited models fixes existence, but does not select c naturally or preserve a previously selected c unless supplied.

## First-order Morita certificates: scope and witness limits

The frozen memo inspected Barrett–Halvorson's [*Morita Equivalence*, §§4.1–4.2, Theorems 4.1–4.3](https://arxiv.org/html/1506.04675). The theorem concerns explicit definitions in classical many-sorted first-order logic. Function/constant definitions require provable existence and uniqueness; their nonempty subsorts require provable inhabitation; quotient definitions require a provable equivalence relation. Products/coproducts have their defining equations. Expansions are unique up to an isomorphism fixing the old structure. New-sort formula translation uses codes, not a function selecting representatives.

Design limits follow directly from what the proposed client requests. A quotient object A/R and its projection are not a section A/R→A. In Set, forming the set of equivalence classes does not require choosing an element in each class. A blanket selector would be a stronger claim, and no such selector is part of this certificate. Even where a section exists noncanonically, it need not be definable, computable, natural, or equal to an existing selected witness. “Up to isomorphism” does not mean literal equality of implementation values. A category lacking the relevant quotients cannot be declared an admissible target merely because Set supports them.

Tsementzis's [Theorem 4.7 and Corollary 4.8](https://arxiv.org/pdf/1507.02302) strengthen the coherent-theory account using equivalence natural across Grothendieck-topos models. The full-text result was checked in the frozen pass. It does not say arbitrary categories have those interpretations. In particular, changing to a completion of a target category is replacement, not retention of every interpretation in that original category.

## Omitted alternative followed: dependent Morita and strictification

This was selected because it could join the new representation-extension lead to D1's existing dependent coherence question, potentially changing priority more than another effect-combination example. Exact follow-up searches:

- `dependent type theories Morita equivalence conservative extensions Isaev Bocquet strictification`
- `conservativity dependent type theories adding type formers generalized algebraic theories model extension`
- `Kapulkin Li Extensional concepts intensional type theory revisited pdf`

Primary source trail: Isaev → Kapulkin–Li and Bocquet; author/publication search → arXiv full versions. HTML locator requests repeatedly failed; full PDF retrieval resolved access for the decision-bearing follow-up. Conference abstracts and secondary summaries were discovery leads, not theorem evidence.

**Isaev, arXiv:1804.05045v2 (2020).** [Definition 2.4 and Proposition 2.5](https://arxiv.org/pdf/1804.05045v2) distinguish three unit conditions for the adjunction induced by a theory morphism: weak equivalence at the initial model (syntactic equivalence), every cofibrant model (Morita equivalence), or every model (strict Morita equivalence). The Quillen characterization assumes semi-model theories. These are not Barrett–Halvorson's same-carrier first-order expansion conditions. This distinction prevents treating the word “Morita” as a single witness-preservation theorem.

**Kapulkin–Li, arXiv:2310.05706v2 (19 December 2025).** Inspected [§1.1–1.4, Definitions 1.10–1.11, Theorem 7.3, §8](https://arxiv.org/pdf/2310.05706v2), PDF pp.3–6,34. Their ITT models are contextual categories with Id, Σ, and Π with function extensionality; the comparison adds stable UIP structure on the intensional side and equality reflection on the extensional side. Structure-preserving maps and strict substitution are part of the model definition. Theorem 7.3 establishes the free/forgetful Morita equivalence: its unit is a weak equivalence at cofibrant models. Weak type/term lifting gives equivalence/homotopy, not literal representative equality. The conclusion covers cofibrant extensions, not arbitrary additional judgmental equations. Section 8 explicitly reports use of choice in §§5–6 and leaves constructive improvement open. This is a theorem with a concrete scope, not evidence for computational extraction or unrestricted higher-identity preservation.

**Bocquet, arXiv:2304.10343v1 (2023).** Inspected [Theorems 6.6, 8.1 and Conjecture 6.3](https://arxiv.org/pdf/2304.10343), PDF pp.29,35; introduction pp.4–6. For a second-order generalized algebraic theory with homotopy relations and a selected set of homotopies, the equational-extension result needs the generated higher congruence to be relatively merely 0-truncated and its first comparison to be a weak equivalence. Theorem 8.1 proves the second factor's trivial-fibration property; the broad first-factor criterion remains a conjecture. The paper explicitly supplies no concrete applications, identifying missing hypotheses. This keeps a non-UIP route alive, but does not establish that the present client's hypotheses hold.

Decision: **do not open a separate D1 research ticket for this lead now.** Record it as a challenger and boundary in D2, and cross-reference the existing D1/#107 work. The #107 body was not included in the inspected issue selection; coordination with it is parent-supplied, not independently audited here. A separate task becomes justified if a concrete client repeatedly needs additional judgmental equalities, accepts the precise identity contract, and supplies the relevant model/cofibrancy hypotheses; or if a non-UIP result has all required hypotheses discharged for that client. Neither condition has been demonstrated in this pass.

## Bounded matched experiment E1: representation sorts without invented choice

Proposed D2 experiment; no checked result is claimed. Compare **direct existing type/model interfaces** with **explicit Morita-style representation definitions** on the same small theory, in two stages of one task.

1. Start with a sort A carrying an equivalence relation R and a named invariant observation o:A→O, with R(a,b) implying o(a)=o(b). Add a genuinely new quotient sort Q, q:A→Q, surjectivity and q(a)=q(b) iff R(a,b). State the intended class of models and maps before construction. Require the observation to descend, old-client recovery under exactly its previous premises, and composition through two interpretation maps. One small product-sort case can serve as a witness-preserving positive control: the pair and both projections must remain available.
2. Run two fixed failures. First add c with P(c), using the pair of old models above to distinguish selected-model from all-model expansion. Second require a representative selector natural under old-model automorphisms; reject it on the two-point indiscrete relation. Its quotient has one element and swapping the two points fixes the quotient. Naturality would force the chosen representative to be fixed by the swap, which neither point is. This is a finite no-natural-selector proof, not a proof that no set-theoretic section exists.

The exact-recovery test is separate: if an existing observer distinguishes the two points, it cannot descend to the indiscrete quotient. Reuse #267's public no-factor result to expose that failure rather than re-proving observation theory. Retain the original witness-carrying interface alongside the quotient; do not replace a required selected witness by a mere existence assertion. A selector with explicitly provided asymmetry would be an additional input, not automatic quotient elimination.

**What can falsify each route:** the direct route fails its advertised contract if it cannot express the new type without a mandatory replacement grammar, or silently changes old-client premises. The Morita route fails the exact-witness task if it returns only a class, existential witness, or arbitrary representative. Either route fails the all-model claim if it verifies just the selected successful model. The generic route may legitimately support fewer target categories; it must report that rather than weaken the model class after seeing the failure.

**Acceptance and stopping:** one representation sort, one old client, two composable interpretations, the two finite failures, and a table of manual obligations suffice. Separate mathematical preservation, encoding effort and author effort. No initiality formalization, automatic weakest-assumption inference, universal conservativity checker or empirical author claim is required. Stop with a scoped positive/negative result even if the generic certificate gives no practical improvement.

## Optional E2, not a new ticket: two substitutions after equality strictification

If D1's chosen client fits the admitted intensional fragment, add a fresh type and a term witnessing an identity, then compare retaining explicit transports against an equality-reflecting presentation. Require the same dependent term through two substitutions, an explicit return comparison and the selected observation. Freeze whether the output judgment is strict equality, an identity term or only homotopy. A homotopy-only result must not be passed off as exact recovery.

The failure control is an intended model with nontrivial higher identity, for which UIP is not available. The strictification theorem cannot be invoked there by adding UIP to make the proof fit. Conversely, the direct route should not be credited with equivalent bookkeeping relief if every extension requires unrelated transport proofs. This test becomes a real comparison only after its source fragment and model hypotheses are fixed. Until then it is a scope boundary, not an active experiment or a reason to postpone E1.

## Ownership and finite handoff

- **#262:** retain its selected semantic-type/admissibility experiment. E1 can coordinate its new type interpretation and old-client evidence, but it should not silently expand #262 into a universal-model theorem or repeat the DRFCaml artifact inventory.
- **#278:** owns mixed constructor/observer and extension-order laws. Keep those independent; E1's quotient certificate does not prove arbitrary extensions commute.
- **#285:** owns higher-order behavior versus independent denotation, including binding and changed observation. The MMR lead informs its negative cases, but does not open another evaluator experiment.
- **#254 and #259:** completed comparison/primitive-extension baseline. E1 is new only if it adds a type and a model-class certificate beyond those fixed-grammar results.
- **#267:** reuse existing exact-observation descent and no-factor proofs. No duplicate quotient-choice claim follows from that implementation.
- **#271:** completed evidence for changing observation indices and exact dependent fibers. Neither first-order Morita nor equality strictification discharges its indexed obligations automatically.
- **#235/#280:** parent should create or assign one separate bounded D2 comparison scope if selected. This memo requests no automatic activation of every lead. Continue D1 under its existing ownership with the conditional source comparison recorded.

Reversal triggers: promote D1 ahead of E1 if the next real client cannot state its result without repeated dependent coherence and the exact weak/strict comparison hypotheses fit. Demote the generic Morita route if its model class excludes intended consumers or its certificate erases required witnesses; retain direct extension interfaces. Promote effect work only if an actual new effect changes the witness/observation contract beyond #278's scope. Quantitative sum/tensor remains an unresolved source lead from the frozen pass, not evidence used for this ordering. Broad completeness of discovery and usability superiority remain unclaimed.

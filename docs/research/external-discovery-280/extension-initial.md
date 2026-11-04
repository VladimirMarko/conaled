# Independent initial discovery: extension obligations

Status: FROZEN initial memo, 2026-11-04. No repository, issue, prior report, shortlist, or other researcher memo was consulted. This note is the only artifact written.

## Exact common brief
We are designing a language in which authors can express a mathematical construction or argument in familiar terms, identify the structure and principles it actually requires, and reuse it in settings satisfying them. Changes of meaning and admissible reasoning are part of the ambition: equalities, witnesses, context restrictions and quantitative observations must not be silently erased. Routine representation bookkeeping should be absorbed by tools. Requirements may compose but automatic inference of all weakest requirements is not assumed. We prefer compositional denotational meaning independent of a chosen execution mechanism; operationally presented work may still supply useful mathematics or implementation/adequacy/resource contracts. Architectural replacement is allowed. Publication counts and implementation familiarity are not merit.

Your assignment is independent initial discovery from author needs, not validation of a provided architecture. Do not read repository code, reports, issue bodies, the previous shortlist or other researchers' notes until your initial discovery memo is saved. Do not inspect this conversation's history. The parent intentionally supplied no such context. Broad conceptual vocabulary from training is unavoidable; record it and do not claim statistical independence. Work read-only apart from your assigned /tmp note. No subagents needed; parent orchestrates.

Use web search and primary sources. Begin with capability/problem queries rather than only named schools or authors; retain the actual initial queries, follow-on citation trails, candidate selection reasons, and excluded/unknown leads. Follow source claims to their owners, inspect full text of decision-bearing claims, and state precise scope/locators and access limits. A secondary source may be a discovery lead but cannot establish a theorem. Separate sourced results from your design inferences. Do not force every candidate to supply the whole language or be easy to encode. A paper-level discriminating comparison is sufficient; do not implement.

Deliver one Markdown memo to the assigned path: exact brief/task, prior-exposure statement, search trace with links, source-backed candidate accounts, two or three consequential comparisons with matched author tasks and falsifying cases for both candidates, provisional priority reasoning, and omissions that might reverse it. Aim for depth on the strongest challengers rather than many shallow entries. Notify parent when the initial memo is frozen before receiving comparison material.

## Exact distinctive task

Independent literature discovery. Read ONLY /tmp/conaled-280/common-brief.md as common instructions; do not read repo or issue/history/other memos during initial discovery. Your distinctive task: an author adds a type former, operation, axiom, effect or observation to a language and wants precise predictable obligations for retaining existing proofs, composition and interpretations. What mathematics separates valid reuse from silently invalid old guarantees, without fixing one universal grammar or evaluation machine? Begin from problem/capability searches, consider overlooked approaches and genuine alternatives, inspect primary source text. Write single initial memo /tmp/conaled-280/extension.md including common brief and this exact task, sources/search traces/exposure/uncertainties, candidate comparisons and priority. Parent will persist after freeze. No implementation or subagents. Notify when frozen before receiving existing shortlist.

## Prior exposure and selection

My training supplies familiarity with institutions, conservative extension, algebraic effects, monads, distributive laws, Morita equivalence, logical relations and modular metatheory. I cannot claim statistical independence or identify particular training documents. No supplied architecture directed selection. Initial capability searches led to operational counterexamples and modular monadic metatheory; follow-up searches added institutions and Morita extensions because the task explicitly allows changing logical structure and adding types. I prioritized papers with concrete obligations and counterexamples over framework breadth. This is a limited discovery pass, not an exhaustive review.

## Search trace

Initial web queries, exactly:

1. `language extension preserve proofs models conservative extension modular semantics`
2. `combine effects preserve equations modular denotational semantics distributive law`
3. `logical systems translation preserve reflect satisfaction institution conservative extension`

These surfaced [3MT author's page](https://skeuchel.org/publication/2013-icfp-modular-monadic-metatheory), [Madlener thesis](https://www.cs.ru.nl/~marko/research/phds/thesis.KenMadlener2014.pdf), [Hyland–Plotkin–Power repository](https://era.ed.ac.uk/items/0e848b79-0acf-4d7a-b411-deb402609f6a), [Pyrosome thesis](https://dspace.mit.edu/entities/publication/48ed26b8-5092-48ab-bd63-7045a671aa2e), ontology conservativity, guarded interaction trees, and attribute-grammar extension systems. Search-result abstracts served as discovery leads only.

Follow-up queries, exactly:

- `Goguen Burstall institutions abstract model theory specification programming pdf 1992`
- `Plotkin Power combining effects sum tensor conservative theories pdf`
- `new observations language extension equations bisimulation conservative extension Mosses Mousavi Reniers 2010`
- `Morita equivalence theories new sorts conservative extension Barrett Halvorson pdf`
- `"Logical Support for Modularisation" pdf`
- `"Institution Morphisms" Goguen Rosu pdf`
- `"Institutions" "147524" pdf`

Citation/access trails: 3MT author page → author-hosted full PDF; effects repository → expanded 2006 full paper; Madlener result referring to MMR10 → Mosses–Mousavi–Reniers full arXiv HTML; Goguen project page → original institutions and modularisation references, then author-hosted *What is a Logic?*; Barrett–Halvorson full HTML → Tsementzis full PDF. Search also exposed quantitative sum/tensor, whose abstract and introduction were read; subsequent full-text locator requests timed out. No theorem below relies on those timed-out sections. Guessed original-paper PDF paths failed and are not evidence.

## Finding: extension is several different contracts

This is my synthesis, not a theorem attributed to one paper. A useful extension interface must distinguish:

1. **Derivation transport:** translate assumptions, conclusions and proof steps into the new theory.
2. **No new old-language consequences:** reflect provability/consequence along that translation.
3. **Interpretation retention:** every intended old model admits an expansion, possibly uniquely up to a specified equivalence.
4. **Combination compatibility:** independently interpreted additions agree on their overlap and satisfy interaction laws.
5. **Observation stability:** the new observation or context class does not invalidate the equivalence used by old proofs.
6. **Witness preservation:** transport proof objects or construction witnesses, not merely truth values.

Adding an axiom in a monotone proof system ordinarily keeps existing derivations. That does not retain every old model. Conversely, preserving behavior of closed old programs does not promise old open equations remain true for newly available substitutions. A rule allowing contractions can invalidate a resource interpretation even when ordinary extensional equations remain sound. These are separate obligations; calling all of them “conservative” obscures the work.

## Candidate A: institutions as a logic-independent contract boundary

Primary inspected source: Mossakowski, Goguen, Diaconescu and Tarlecki, [*What is a Logic?*](https://cseweb.ucsd.edu/~goguen/pps/nel05.pdf), Definitions 2.1, 2.6, 3.1–3.2, 4.12; PDF pp. 3, 5–7, 12. Signatures index sentences and model categories; sentence translation and model reduct satisfy a satisfaction equivalence. Comorphisms connect different institutions. Semi-exactness is an additional hypothesis: compatible models over a signature pushout amalgamate uniquely, also on morphisms. It is not implied by the basic satisfaction axiom.

Design inference: this is the best general vocabulary for declaring what an extension means without prescribing all syntax or execution. An expansion property can separately certify retention of interpretations; a proof-enriched variant must carry witnesses. The basic satisfaction condition alone cannot establish conservativity or preserve arbitrary observational quotients. Concrete instantiations still owe the model/reduct construction and coherence evidence. The original 1992 paper was discovered but not obtained; *Logical Support for Modularisation* was discovered but its decision-bearing results were not inspected. I therefore do not claim a specific pushout-conservativity theorem from it.

## Candidate B: Morita extensions for genuinely new types with old meaning

Primary inspected source: Barrett–Halvorson, [*Morita Equivalence*](https://arxiv.org/html/1506.04675), §§3.1, 4.1–4.2, Theorems 4.1–4.3. New product, coproduct, subsort and quotient sorts have explicit defining axioms. Required admissibility conditions include existence for subsorts under their nonempty-sort convention and equivalence-relation laws for quotients. Every old model expands uniquely up to isomorphism; conservativity follows. Formula translation involving new-sort variables requires codes relating them to old-sort variables.

Design inference: authors can add representation types with a specific “nothing semantically new” certificate instead of treating every type addition as a new primitive assumption. This does not certify arbitrary function types, inductive types, or effects. It also does not identify proof objects merely because first-order truth is retained.

Further primary source: Tsementzis, [*A Syntactic Characterization of Morita Equivalence*](https://arxiv.org/pdf/1507.02302), Theorem 4.7 and Corollaries 4.8–4.9 (PDF p.22), §5. For coherent theories, syntactic Morita equivalence matches classifying-topos equivalence and model-category equivalence natural in every Grothendieck topos. Fragment-specific versions change allowable sort constructors. This is materially stronger evidence than an accidental equivalence of Set-model categories.

## Candidate C: effect theories and chosen combination laws

Primary inspected source: Hyland–Plotkin–Power, [*Combining Effects: Sum and Tensor*](https://www.pure.ed.ac.uk/ws/portalfiles/portal/17919624/Hyland_Plotkin_ET_AL_2006_Combining_Effects_Sum_and_Tensor.pdf), introduction; Theorems 9 and 11 (PDF pp.23,25); discussion PDF p.27. Sum retains each theory's laws without cross-equations; tensor adds commutation. Theorem 9 identifies tensor models with iterated models under its enrichment/cotensor hypotheses. State-transformer identification has additional presentability assumptions. The paper explicitly warns that tensoring deadlock and nontermination identifies their constants. Exception handling is outside the algebraic operations covered by the basic account.

Design inference: do not accept “two effects compose” as a complete author contract. Name their interaction theory, its interpretation, and the distinctions it preserves. This supplies denotational obligations with no chosen evaluator, but is not itself a language of arbitrary mathematical arguments.

Quantitative challenger: Bacci–Mardare–Panangaden–Plotkin, [*Sum and Tensor of Quantitative Effects*](https://arxiv.org/html/2212.11784), abstract and introduction inspected. It replaces plain equations with approximate equality in metric-space effects. It is a high-priority continuation for quantitative observations, but I have not checked the exact hypotheses of its main theorems and do not use them to rank it above the fully inspected candidates.

## Candidate D: feature/effect proof factoring, a practical alternative

Primary inspected source: Delaware, Keuchel, Schrijvers and Oliveira, [*Modular Monadic Meta-Theory*](https://skeuchel.org/files/papers/2013-icfp-modular-monadic-metatheory.pdf), §5 pp.6–8 and §6 pp.8–9, especially §6.1 and Figure 11. Feature soundness abstracts over used effects; an effect theorem specializes the computation typing judgment to a selected effect combination; the language theorem combines them. For state plus exceptions, alternative catch/state interaction laws give separate reusable proof cases. The paper also records weakening, binder and inversion obligations in its case study.

Design inference: this offers the clearest pattern for predictable author work when adding executable features: reuse feature proofs, prove genuinely new interaction cases, and state the resulting theorem correctly. It provides a useful implementation architecture without proving that an arbitrary mathematical extension retains all interpretations. The fixed denotational metatheory and selected soundness properties should not be promoted into a universal proof-reuse guarantee.

## Candidate E: robustness under new observations, an adversarial control

Primary inspected source: Mosses–Mousavi–Reniers, [*Robustness of Equations Under Operational Extensions*](https://arxiv.org/html/1011.6435), Example 4, §3 Theorems 19–20, §4.1 Example 21. In positive GSOS, proper fh/hp bisimilarity survives disjoint extensions. Plain variants need restrictions, including label restrictions in the relevant preservation result. Example 21 has only deadlocked closed terms initially, validating an open equation by all old closed instances; adding a live constant refutes it despite disjoint extension. Example 4 shows new labels can break old equations without matching rules for old operators.

Design inference: operational work supplies indispensable falsifying tests even if the chosen architecture is denotational. It proves preservation only for specified proof notions and extension formats. We should borrow the distinction between an equation's old instances and a proof stable under future instances, without adopting GSOS as a universal grammar.

## Three consequential comparisons

These tests are proposed design experiments, not additional literature claims.

### 1. Add quotient objects, then reuse an argument in another interpretation

Compare institutional model expansion with Morita extension certificates. Take a theory with a relation R and ask for a quotient sort Q. Under a Morita contract, prove R is an equivalence relation and give the defining quotient axioms. Under an institutional contract, define reduct, satisfaction compatibility, and the desired expansion property. The latter admits more forms of extension; the former offers a smaller and more predictable certificate for this author task.

Falsifying test for a too-permissive institutional design: add a supposedly harmless new constant c with old-language axiom P(c), when an old model has no P-elements. Satisfaction under reduct may hold, yet that model has no expansion. Falsifying test for a too-universal Morita design: ask to freely add a linear order to an arbitrary structure, preserving possible choices rather than uniquely recovering one. This is new structure, not a definitional/Morita representation extension. Rejecting it altogether would fail the broader goal; it should instead receive a weaker, explicit contract.

Priority: use Morita as a strong extension class inside a more general boundary, not as the only permitted extension.

### 2. Add state and exceptions, then reuse type-soundness and equation proofs

Compare algebraic effect composition with 3MT. The effect-theory route asks which cross-laws define the intended model; 3MT asks how those laws discharge precisely the new cases of a selected theorem. These approaches overlap but do not replace each other.

Falsifying test for an unqualified algebraic-combination claim: add an observable trace and require the ordering of a write and raise to remain distinguishable. A selected commutation equation can erase that information. Existence of a tensor is not preservation of all distinctions. Falsifying test for an unqualified 3MT claim: run a typed program under two handlers with distinct state-restoration policies. Both can satisfy an appropriate type-soundness statement; that proves neither identical behavior nor transport of the same contextual-equivalence proof. A reusable proof may need a hypothesis parameter, or two theorem statements.

Priority: make interaction laws part of the authored theory; use feature/effect factoring to generate a finite, intelligible proof obligation surface. Do not infer laws from transformer order without exposing their meaning.

### 3. Extend the observation vocabulary, then reuse an open equation

Compare institutional truth transport with robust behavioral proof formats. A logic-independent boundary can state the intended preservation map, but its interface must encode the changing observation/context class. A robust operational proof gives an actual sufficient criterion within a restricted language family.

Falsifying test for truth transport alone: an old semantics sends two programs to the same result, while the extended semantics distinguishes their execution costs. A forgetful map back to old results preserves old truth but cannot reflect the stronger equality. Falsifying test for insisting on a GSOS robustness certificate everywhere: a geometric quotient construction has no intended transition system. Translating it into one merely to meet a proof format creates irrelevant obligations and may lose intended witnesses.

Priority: explicitly index equality by observations and admissible contexts. Admit format-specific robustness certificates as one way of discharging a general preservation claim. This proposal still needs a proof-relevant formulation; none of the inspected sources automatically supplies it.

## Provisional priority and omissions

For this author need, the leading architectural direction is **a family of explicit extension contracts**, with institutions providing the broad model/sentence interface, Morita extensions providing unusually strong reusable certificates for representation types, and effect theories specifying interaction. 3MT is the strongest inspected guide to how to expose manageable proof obligations. Behavioral robustness is a necessary negative control: it catches guarantees that otherwise sound plausible but are false.

I would not choose a universal grammar or evaluator from this pass. Nor would I promise automatic weakest-requirement inference. Proposed obligation templates are: definitional/admissibility certificate; model-expansion certificate; cross-law/model certificate; observation reflection certificate; and proof-object transport certificate. Their composition laws and possible dependence on chosen models remain design work.

Potential reversals and limits:

- Proof-relevant institutions, doctrines, fibrations and comprehension categories could be better than ordinary institutions once witness/context retention is primary. They were known vocabulary but not investigated here. The current ranking is strongest for extension contracts, weaker for the core language of arguments.
- Generalized algebraic theories, logical frameworks with binding, higher-order algebraic theories and dependent type-theory conservativity may give more direct obligations for arbitrary type formers. Not examined deeply enough to rule them out.
- Pyrosome was a strong discovery lead for extensible equivalence-preserving compilation, but only its abstract was inspected; it deserves full-text comparison with 3MT if compilation becomes central.
- Guarded interaction trees and logical relations deserve inspection for higher-order effects and adequacy. Their concrete semantic domains may be useful locally without being required globally.
- Quantitative effects may replace ordinary equations in the main contract when observations carry distances. Full theorem hypotheses remain unchecked due fetch failures.
- Modular attribute grammars and projection-based metatheory are genuine alternatives for predictable syntactic extension; their grammar commitment made them lower priority for this problem, not mathematically inferior.
- Institutions' conservativity under pushouts, interpolation, and amalgamation are an important unfinished source trail. Do not substitute the author's project-page summary for a checked theorem.
- No claim of complete theorem-proof auditing: I inspected definitions, statements, adjacent arguments and counterexamples at the locators given; some long proofs and references remain unread. Web PDF text sometimes has OCR corruption; the NASA institution-morphisms PDF was especially poor and supports no decisive claim here.

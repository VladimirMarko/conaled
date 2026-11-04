We are designing a language in which authors can express a mathematical construction or argument in familiar terms, identify the structure and principles it actually requires, and reuse it in settings satisfying them. Changes of meaning and admissible reasoning are part of the ambition: equalities, witnesses, context restrictions and quantitative observations must not be silently erased. Routine representation bookkeeping should be absorbed by tools. Requirements may compose but automatic inference of all weakest requirements is not assumed. We prefer compositional denotational meaning independent of a chosen execution mechanism; operationally presented work may still supply useful mathematics or implementation/adequacy/resource contracts. Architectural replacement is allowed. Publication counts and implementation familiarity are not merit.

Your assignment is independent initial discovery from author needs, not validation of a provided architecture. Do not read repository code, reports, issue bodies, the previous shortlist or other researchers' notes until your initial discovery memo is saved. Do not inspect this conversation's history. The parent intentionally supplied no such context. Broad conceptual vocabulary from training is unavoidable; record it and do not claim statistical independence. Work read-only apart from your assigned /tmp note. No subagents needed; parent orchestrates.

Use web search and primary sources. Begin with capability/problem queries rather than only named schools or authors; retain the actual initial queries, follow-on citation trails, candidate selection reasons, and excluded/unknown leads. Follow source claims to their owners, inspect full text of decision-bearing claims, and state precise scope/locators and access limits. A secondary source may be a discovery lead but cannot establish a theorem. Separate sourced results from your design inferences. Do not force every candidate to supply the whole language or be easy to encode. A paper-level discriminating comparison is sufficient; do not implement.

Deliver one Markdown memo to the assigned path: exact brief/task, prior-exposure statement, search trace with links, source-backed candidate accounts, two or three consequential comparisons with matched author tasks and falsifying cases for both candidates, provisional priority reasoning, and omissions that might reverse it. Aim for depth on the strongest challengers rather than many shallow entries. Notify parent when the initial memo is frozen before receiving comparison material.

## Exact assigned task

Independent literature discovery. Read ONLY /tmp/conaled-280/common-brief.md as common instructions; do not read repo or issue/history/other memos during initial discovery. Your distinctive task: an author notices the same proof or construction in different mathematical settings and wants to discover, state and reuse its actual requirements, including when the admissible logic or notion of equality changes. What research enables this act without requiring the author to manipulate encodings constantly? Start from author/problem searches, consider replacements and overlooked approaches, inspect primary source text. Write single initial memo /tmp/conaled-280/assumptions.md including the common brief and this exact task, sources/search traces/exposure/uncertainties, candidate comparisons and priority. Parent will persist it in repo after initial freeze. No implementation or subagents. Notify when frozen before receiving existing shortlist.

## Exposure and independence

Initial discovery frozen 2026-11-04. I read the common brief and assignment as task-specific input, and no repository documents, issue bodies, history, shortlist, or other researchers' notes. General prior training exposure includes logical frameworks, institutions, parametricity, univalence, theory morphisms, abstract algebra, reverse mathematics, and type classes. This is procedural separation, not statistical independence. Named-school follow-ups were influenced by that vocabulary. No repository changes or implementation were performed.

## Search trace and selection

Actual initial queries, in order:

1. `mathematical proofs reuse discover assumptions change logic equality abstract mathematics specification`
2. `reuse mathematical proof different logics theorem transport institutions little theories`
3. `infer algebraic requirements mathematical algorithms generic programming concepts proofs`

The first batch returned [Johnsen–Lüth](https://ebjohnsen.org/publication/04-tphols/), [Adams–Luo](https://pure.royalholloway.ac.uk/en/publications/a-pluralist-approach-to-the-formalisation-of-mathematics/), [the IMPS manual](https://imps.mcmaster.ca/manual/node10.html), and [Cerioli–Meseguer](https://www.sciencedirect.com/science/article/pii/S0304397596001600). These directly address discovery from completed proofs, logic changes, reusable assumptions, and logic transport. Generic-programming results were less directly concerned with changed proof logic and were not promoted merely for being implementable.

Actual follow-ups:

- `proof generalization abstraction weakest assumptions proof terms Johnsen Luth 2004 pdf`
- `univalent parametricity transport proofs equivalences Trocq equality relations proof transfer`
- `institutions Goguen Burstall logical systems satisfaction condition 1992 pdf`
- `Adams Luo Plural pdf logic enriched 2011`
- `Goguen Rosu May I borrow your logic pdf`
- `Farmer Guttman Thayer little theories 1992 pdf`
- `"May I borrow your logic" pdf Tarlecki Cerioli Meseguer`
- `"institutions" "Goguen" "Burstall" filetype:pdf 1992`

The Goguen/Rosu query was an incorrect authorship guess, corrected by discovery: *May I borrow your logic?* belongs to Maura Cerioli and José Meseguer. Search-result timestamps were unreliable; bibliographic dates below come from the papers.

Trails: Johnsen's author page → author PDF; Royal Holloway record → manuscript link (403) → Luo's published author PDF; IMPS manual → authors' 1992 paper; Trocq → explicit comparison with Tabareau–Tanter–Sozeau and representation-independence references; institutions search → Goguen's publication page and PDF. Secondary snippets only supplied leads.

## Source-backed candidates

### A. Extract requirements from a proof already written

Johnsen and Lüth, *Theorem Reuse by Proof Term Transformation*, TPHOLs 2004. [Primary PDF](https://ebjohnsen.org/publication/04-tphols/04-tphols.pdf), §§2–3, pp. 2–6; §§4.3–4.4, pp. 10–12. Inspected full text of these passages.

The method makes selected proof dependencies into premises, abstracts operation symbols, then abstracts types. The result is another checked theorem with applicability conditions. Type-specific inference rules must also become explicit. Isabelle proof-term replay checks the transformation; ordinary proof tactics remain usable. Signature morphisms support reuse, with dependency order reducing repeated discharge. The authors caution that abstracting everything produces difficult-to-use results.

Scope: sufficient requirements for this proof, not globally weakest assumptions for the proposition. The natural-number example exposes induction as well as addition equations. This is the strongest direct match for retrospective discovery. Design inference: present extracted obligations as a reviewable draft theory instead of requiring authors to anticipate an abstraction. Whether generated premises align with mathematicians' preferred concepts at scale remains unknown.

### B. Give requirements a reusable mathematical home

Farmer, Guttman and Thayer, *Little Theories*, CADE 1992. [Primary PDF](https://imps.mcmaster.ca/doc/little-theories.pdf), §§1.3, 2.1–2.3, 4; manuscript pp. 5–9, 11–12. Inspected these sections and their examples.

IMPS organizes mathematics into axiomatic theories linked by checked interpretations. Obligations include translated axioms and conditions for sorts/partiality. Translation matching retrieves or constructs interpretations while applying lemmas; context interpretations allow locally assumed instances. Thus users need not manually assemble translations at every invocation. The underlying logic is LUTINS, a simple type theory with partial functions and subtypes.

Scope: demonstrated organization and automation, not discovery of the weakest theory. The interpretation theorem is cited to Farmer's foundational treatment rather than proved here; I have not inspected that owner paper. Design inference: little theories are a serious alternative to making an ambient implementation-language class hierarchy the sole mathematical interface. Prioritize them for presentation and reuse; their particular fixed logic does not answer every logic-change requirement.

### C. Change logic without rewriting every script

Adams and Luo, *A Pluralist Approach to the Formalisation of Mathematics*, MSCS 21 (2011), 913–942. [Published primary PDF](https://www.cs.rhul.ac.uk/~zhaohui/pluralismJ.pdf), §§3.3–4, especially Definition 4.1 and import-module conditions, pp. 926–927; §5.3, pp. 930–933. Inspected full text, including failed and successful negative translations.

Logic-enriched type theories separate logical propositions/proofs from types/terms. A translation module supplies target definitions for source constants and must respect source computation rules. Importing it permits reuse of unchanged scripts for translated statements. For negative translation, naïve connective replacement fails at disjunction elimination; restricting the translated proposition universe to stable propositions repairs that failure.

Scope: demonstrated translations, not arbitrary automatic foundation changes. Logical declarations are hand-built. Design inference: specialists may manipulate encodings once while mathematical authors receive explicit translated statements and a checked logic contract. Unchanged scripts must not conceal changed meaning. This separation is especially worth investigating if ordinary proofs should retain familiar notation while the admissible logic varies.

### D. Infer how much relational structure transfer needs

Cohen, Crance and Mahboubi, *Trocq: Proof Transfer for Free, With or Without Univalence*, ESOP 2024, 239–268. [Primary full text](https://link.springer.com/chapter/10.1007/978-3-031-57262-3_10), §§2.1, 3.2–3.3, 4.3–4.5 and introduction examples. Inspected prose and formulas. Some displayed theorem/figure formulas are raster images and were not recovered; I do not independently certify the exact displayed Theorem 6 judgment.

Trocq decomposes equivalence into a hierarchy of relational structures and uses annotated types to guide transfer synthesis. It can avoid univalence when unnecessary and permits relations beyond equivalences. Source syntax alone does not determine translation: expected-outcome information is required. Constants need registered relational information. The calculus concerns dependent type theory, not unrestricted migration among object logics.

Design inference: this approach can absorb representation bureaucracy while reporting required directional maps and compatibility witnesses. It should not be confused with discovering algebraic axioms. Its strongest relevance is precision about transfer evidence when the available relation is weaker than an equivalence.

### E. Challengers not sufficiently inspected

Tabareau, Tanter and Sozeau, *The Marriage of Univalence and Parametricity*, JACM 2021. [Author PDF](https://pleiad.cl/papers/2021/tabareauAl-jacm2021.pdf), [authors' arXiv record](https://arxiv.org/abs/1909.05027). Abstract inspected, not decision-bearing full text: a lead rather than independently established evidence here. It promises transfer across equivalences with optional function correspondences, including dependent terms and type-level computation. Trocq's direct comparison motivated prioritizing the latter, but that is the newer authors' comparison. Independent examination of the predecessor could revise this judgment.

Goguen and Burstall, *Institutions: Abstract Model Theory for Specification and Programming*, JACM 39 (1992), 95–146. [Author publication page](https://www-cse.ucsd.edu/~goguen/projs/inst.html), [primary PDF](https://cseweb.ucsd.edu/~goguen/pps/ins.pdf). PDF accessible but extracted text corrupt. Screenshot requests returned references without readable images in this session. I inspected the abstract and author account, not decisive proofs. It promises logic-independent theory structure and conditions for borrowing theorem provers; no theorem-level endorsement here. Its semantic orientation could materially outrank the proof-transformational approaches if proof-relevant and quantitative obligations are supplied.

## Consequential comparisons and falsifying tasks

These are proposed experiments and design judgments, not claims that cited implementations were run.

1. **Retrospective discovery: A versus B.** Author proves an identity for a concrete algebra, then sees the argument elsewhere. Extract requirements from the completed proof and publish one compact interface supporting both instances. A loses if it yields only unmanageable expanded premises and cannot help recover reusable concepts. B loses if users must manually restate and reprove the argument before reuse. Prefer A for candidate requirements, B for naming and composing them. Neither wins by listing ambient axioms. Test a proof with an irrelevant detour through classical choice: extracting that dependency is honest, advertising it as mathematically necessary is wrong.

2. **Changed equality/representation: D versus equivalence-only E.** Author has only a one-directional relation and wants to transfer a dependent theorem. Require a generated target proposition/proof and inspectable compatibility data. D loses if it silently strengthens the relation or loses witness dependence. E loses if it demands an unavailable, unnecessary equivalence. Conversely, with equivalent structures and rich higher equalities, do not presume D's finite annotations suffice; evidence could reverse priority. Include a function distinguishing representatives: rejection should be expected unless the target theorem is explicitly weakened.

3. **Changed admissible logic: C versus B.** Author reuses a classical argument constructively. Demand a visible target statement; test whether an existential conclusion still yields a witness. C loses if script replay hides a changed conclusion or assumes the missing principle. B loses if interpretations only rename nonlogical structure inside the old logic. Fidelity of meaning matters more than unchanged syntax. For ordinary same-logic algebraic reuse, C's foundational machinery may be needless and B should win. For linear reasoning, both need new evidence that contraction and weakening are controlled rather than inherited unnoticed from the framework.

## Provisional priority and architectural consequence

For this author need, prioritize **A + B** as discovery and publication, then **C** for an explicit logic-translation boundary, with **D** for representation transfer. This ranks research questions and obligations; it does not mandate assembling four implementations. The architecture could instead be a logic-independent theory network with these as authoring services. A replacement should demonstrate four acts: expose sufficient requirements, name them, instantiate them, and show how meaning changes under translation.

No inspected candidate establishes the entire language, automatic weakest requirements, unrestricted equality changes, or quantitative/resource preservation. Checked proof transformations do not themselves provide compositional denotational semantics for the whole author language. That requirement remains open.

Omissions that could reverse priority: institution comorphisms and proof-relevant general logics; frameworks controlling structural rules; contextual/modal type theories; categorical internal languages and hyperdoctrines; reverse-mathematical proof analysis; program slicing and theory exploration; partial Galois transport; cubical structure identity and representation independence. Initial results included [Transport via Partial Galois Connections and Equivalences](https://arxiv.org/abs/2303.05244), but I did not inspect its full text. I did not inspect current tool maintenance, measure user effort, or run examples. Cerioli–Meseguer remains abstract-only. These are bounded omissions, not negative findings.

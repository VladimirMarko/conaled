# Comparison after independent discovery: recover requirements before choosing transport machinery

2026-11-04. The initial `/tmp/conaled-280/assumptions.md` remains frozen. This memo was written after reading the existing shortlist and direction. It is a research recommendation, not an implementation or an author trial.

## What changes relative to the first pass

Promote a narrowly revised **D2: retrospective requirement discovery and publication** to the first investigation group. Keep D1 as the paired semantic check. D3 remains valuable, but should not be the default second investigation for an author whose immediate problem is recognizing and extracting a common argument.

This is a change in task selection, not a claim that the literature underlying D1/D3 is weaker. The existing foundations note already includes theory morphisms, LF/MMT, parametricity and logic changes. Its proposed D2 begins with a theory presentation or signature already available. The new discriminating input is a **completed concrete proof whose reusable requirements have not yet been designed**. It asks whether the author can turn that proof into a good interface without redoing it. D1 treats coherence of a selected dependent semantics; D3 treats computational witnesses under effects. Neither directly tests that earlier act of discovery.

The initial recommendation for “Johnsen–Lüth + Little Theories” should therefore be refined: investigate proof-derived requirements against **author-designed theories with MMT-style views**, rather than recommend an IMPS-shaped replacement. Little Theories supplies an important author-facing precedent; MMT is a stronger credible competitor for foundation-independent organization. A proof transformation may be an authoring service inside either organization.

## Local exposure and issue evidence

Read: `docs/research/recursive-fusion-implementation.md`, `abstract-fifo-client.md`, `toolkit-author-effectiveness.md`, the recommendation in `language-extension-metatheory.md`, and `docs/language-direction.md`, architectural-quality/domain guidance, relevant glossary entries and ADRs 0001/0002; `external-language-comparison.md`, `external-language-foundations.md`, the computational companion's effects/domain sections; relevant passages in `internal-proof-authoring.md`, `higher-theory-reuse-and-outsourcing.md`, and `composable-internal-languages-and-relativization.md`. `rg` searched those documents for theorem/reuse/logic/transport candidates. The local reports are evidence about prior investigations, not independent verification of their Lean results. I did not inspect or change Lean code or run builds.

Read `/tmp/conaled-280/issues.json` by title filtering, then bodies of #280, #254, #249, #248, #210, #140 and #117. An initial unfiltered display was truncated; the body inspections above were explicit bounded reads. The original JSON omitted issue state. Parent checked live state and corrected #248/#252, #210, #249 and #254 to closed; #107, #117 and #235 remain open. The following supersedes any implication that these completed investigations remain active owners. Issue overlap is substantial:

- **#248 and #252 are closed, completed evidence.** Reuse `docs/research/recursive-argument-transport.md`, `recursive-fusion-implementation.md`, `SquareKit/ListInitial/Fusion.lean`, `Types.lean`, `Presheaves.lean`, and `Examples/RecursiveFusion.lean`. The accepted categorical proof already serves types and a nonconstant presheaf; do not repeat that implementation.
- **#254 is closed.** Reuse `docs/research/language-extension-metatheory.md` and its explicit extension contracts. Send newly exposed gaps to #235, not the completed survey.
- **#210 is closed.** `docs/research/abstract-fifo-client.md`, `Applications/Sequences/AbstractFIFO.lean`, and `Examples/AbstractFIFO.lean` provide accepted operation-preservation and hidden-observation fixtures. Any new Trocq comparison needs a new #235 child, not renewed ownership assigned to #210.
- **#140** supplies retained-witness/dependent-data fixture specifications; reuse its distinctions rather than another theorem merely showing propositional existence loses data. Its live status is not inferred from the state-less snapshot.
- **#249 is closed.** Reuse `docs/research/toolkit-author-effectiveness.md` and `experiments/toolkit-authoring/protocol.md`; #117 remains open for surface comparisons. A new trial needs a new scope under #235 or explicit coordination with #117.
- **#280** selects research; **#235** retains architecture/integration ownership, coordinated with **#36/#200**. The proposed change does not activate #260 or replace the kernel.

No ADR revision is needed for a research comparison. Adopting a theory-network architecture would require a separately scoped proposal preserving the concrete interfaces and distinct contracts required by ADRs 0001/0002.

## Decision-bearing source checks

### Proof extraction: exact promise retained

[Johnsen–Lüth, *Theorem Reuse by Proof Term Transformation*](https://ebjohnsen.org/publication/04-tphols/04-tphols.pdf), §§2–3 and 4.3–4.4, was inspected in the initial pass. Its three transformations expose dependencies, abstract operation symbols, then abstract types, with replay checking the resulting proof. The proposed output consists of sufficient applicability conditions for that proof, not a unique weakest theory. This distinction is decisive: the benchmark must score usefulness and semantic fidelity separately from minimization. I recommend a bounded investigation of this act, not a general theorem that arbitrary Lean elaborated proofs can be generalized by the same implementation.

### Little Theories: owner theorem now inspected, with its actual limits

Followed the IMPS authors' bibliography to Farmer, [*Theory Interpretation in Simple Type Theory*](https://imps.mcmaster.ca/doc/interpretations.pdf), LNCS 816 (1994), 96–123. Inspected §6 (manuscript pp. 16–19) and §8 (pp. 21–25), including Theorem 8.8 and its proof. A LUTINS translation must satisfy the sort/type conditions, map variables injectively to suitably sorted variables, and map constants to closed appropriately typed expressions. Four obligation classes are translated axioms, sort nonemptiness, constant sorts, and sort inclusion. When all are target theorems, Theorem 8.8 yields theorem preservation. It reduces via normal translations to PF*; the proof explicitly uses Farmer 1993, Theorem 12.4, which I have not independently audited.

This resolves the immediate owner-source gap without claiming arbitrary-logic or witness preservation. Equality/logical constructors are translated by the specified LUTINS clauses. The result does not authorize changing equality to an arbitrary observational relation. Recommend its obligation discipline and author-facing reuse precedent, not its theorem as the universal setting-change contract.

### Strongest organization alternative: MMT

Inspected [Rabe–Kohlhase, *A Scalable Module System*](https://www.kwarc.info/people/frabe/Research/mmt.pdf), author preprint, §7.2, Definition 30, Definition 32 and Theorem 34, printed pp. 60–64. Regularity requires compatible normalization/equality, congruence, and typing/equality preservation along flat declaration assignments. Under a fixed regular foundation, Theorem 34 supplies morphism composition and transport; its typing/equality preservation clause requires **total** morphisms. Partial views can omit axiom assignments, so cannot be treated as certified theorem transport. The following counterexamples explain why even unfiltered terms may lose a derived equality when its supporting axiom is filtered.

This is a real challenger: a compact theory plus total views may produce more legible obligations than mechanically extracted proof dependencies. Conversely it does not by itself discover that compact theory. Prefer a matched extraction-versus-presentation experiment, not separate success demonstrations. Foundation-independent packaging also does not remove the need for an adequate object-logic encoding or a model interpretation.

### Trocq: formula access gap resolved, priority remains conditional

The [authors' arXiv HTML v1](https://arxiv.org/html/2310.14022v1), §4.4, renders the theorem missing from the Springer extraction. Its Theorem 4.7 (numbering differs from published Theorem 6) assumes a well-formed `γ(Δ)`, typing `γ(Δ) ⊢+ M : A`, and Trocq derivations both for `M @ A` and for `A @ Box_i^α`, producing `M'`, `A'`, and witnesses. It concludes typing of `M' : A'` and of `M_R : rel(A_R) M M'`. The proof is induction on the translation derivation. §4.3 defines the annotated calculus; the input type carries information about the intended output. These premises do not establish existence of a successful transfer for every requested relation.

Thus the missing display is no longer an access blocker for a bounded transfer comparison. This remains a syntactic relational theorem with supplied annotations/constants, not recovery of algebraic requirements or arbitrary logic migration. I do not promote it ahead of D1/D2; reuse the completed #210 fixture in a newly scoped #235 child if its relation contract fits. I did not compare all version differences or audit the plugin.

### Strongest reason to keep D1 early

Inspected [Lumsdaine–Warren, *The local universes model*, v2](https://arxiv.org/html/1411.1736v2), Theorem 3.4.1, Definition 3.1.3, and §4.1. Theorem 3.4.1 takes a full comprehension category satisfying (LF) and weakly stable specified constructors; its split replacement has strictly stable corresponding constructors. The listed W-type case is relative to a stable class of products. Section 4.1 labels broader extension claims a heuristic and excludes type-equality rules from the simple generalization.

This directly attacks recurring semantic coherence work. If the same intended argument cannot be interpreted without repeatedly repairing substitution, an elegant extracted requirement list does not solve the problem. Hence retain D1 as a paired test and promote it above extraction when coherence is the actual blocking obligation. The theorem does not claim every model/map can be strictified with arbitrary extra equations.

## Bounded matched tasks and possible failures

### R1: Recover a theory from a completed argument

Create a new bounded #235 child, coordinated with #36/#200 and #107/#117. Begin with two calibrated cases: an equational algebraic argument and a constructive witness-producing argument. Compare three routes on identical frozen inputs: manual operation/law interface, explicitly presented theory with total MMT-style views, and proof-derived requirements subsequently edited into a public theory. The latter two can share an implementation boundary; the experiment must still distinguish discovering requirements from packaging them.

Use the accepted #248/#252 reachable left-fold fusion as a subsequent reuse fixture, not a new recursive-transport implementation. Its source `SquareKit/ListFusion.lean` theorem and accepted categorical `SquareKit/ListInitial/Fusion.lean` proof give an unusually useful contrast: concrete induction versus initiality and selected exponentials. Types and presheaf instances are already available. Freeze those artifacts and their existing assumptions before adapting routes. Include the actual induction/initiality principle rather than a primitive named `fold` or a premise equal to the whole fusion result.

Deliverables: a dependency ledger distinguishing rules, mathematical axioms, definitions and imported theorems; the resulting public requirements; target obligations; the retained equality/witness contract; and a traced correspondence to the original proof. Neither count of generated premises nor shorter syntax is sufficient success evidence.

Negative cases: remove the target induction/stability premise; add an unused ambient classical principle; then deliberately use that principle in a detour. The tool must distinguish ambient availability from actual proof dependence and actual dependence from mathematical necessity. A new proof avoiding the detour may justify fewer requirements, but the report must identify that proof change.

**Extraction loses** if its premises are semantically opaque, force irrelevant structure, or require reconstruction as hard as writing the generalized proof. **Manual presentation or MMT-view organization loses** if authors must discover and duplicate the argument unaided or rebuild translations at each use. Either route loses if it transports only the final proposition while claiming reuse of the recursive argument. The result may be that extraction is useful as a diagnostic but a human-designed theory is the best published artifact.

### R2: The same proof under a changed logic

A short paper-level task, coordinated with D2/#36/#200, should precede another importer project. Fix a source proof that uses classical disjunction elimination and compare an explicit translated derivation with an Adams–Luo-style translation module. Require a displayed target proposition, rules justifying the translation, and a clear separation between an existential proposition and a selected witness. Include the failed naïve negative-translation case and the stable-proposition repair from the initial source inspection.

**Module reuse loses** if an unchanged script obscures changed meaning or smuggles in a forbidden rule. **Explicit translation loses** if every downstream author must repeat the encoding and stability boilerplate. Both must reject a promise to extract an ordinary constructive witness solely from a negatively translated existence claim. This isolates changed logic from effectful execution; it neither establishes higher identity transport nor supersedes D3's effect equations.

R2 can be a bounded research subsection in a revised D2 ticket. Do not require a universal translator or a Lean kernel change. If its model/encoding work becomes substantial, split that implementation scope after the paper comparison.

### D1 paired check; D3 retained as a different question

For R1's selected dependent invariant, write two successive substitutions in the baseline and a qualifying local-universes presentation. Count model-builder versus proof-author obligations separately. If (LF) or the needed equality rule fails, record the obstruction rather than simplify the semantics until it fits. Conversely, if direct interfaces repeatedly reconstruct coherence, that failure justifies prioritizing D1 machinery.

D3's retained-realizer/effect-law comparison should proceed when the selected author case actually changes effects. Its merit is not reduced by R2, but effectful witness interpretation is not a prerequisite for discovering a reusable algebraic or intuitionistic proof. Existing witness fixtures should constrain every task without forcing every task into EffHOL.

## Sequence, uncertainty and revision triggers

1. Queue R1 as a new #235 child: freeze the two calibration cases and compare proof-derived requirements, a manual interface, and total theory views. Then reuse the accepted #248/#252 recursive fixture if needed to discriminate remaining claims. Obtain explicit interfaces and failure traces before broad implementation.
2. Pair its first dependent obstruction with D1 and open #107/#235; reuse completed #254 evidence for metatheory gaps without treating that issue as live. Run R2 as a small independent logic-change comparison if it does not require building a general frontend.
3. Reuse completed #210 fixtures for any newly scoped representation comparison under #235, with Trocq's theorem premises explicit. Schedule D3 when a selected effectful witness task earns it; retain D4–D6 as distinct unresolved semantic tests, not rejected traditions.
4. Only then scope new author trials through #235/open #117, reusing the completed #249 protocol, with frozen reference solutions and distinct author exposure. Architecture adoption and migration remain separate #235 work.

Reverse this ordering if the selected proof has no useful retrospective abstraction, if a direct theory already eliminates the discovery burden, or if coherence prevents either candidate interpretation. Move D3 ahead when effects and realizer observations are the actual user need. Promote a richer LF/MMT or categorical internal-language replacement if it gives both compositional semantics and a demonstrably better requirement-discovery workflow. Decline extraction tooling if it provides only a noisy trace with no improved reusable artifact.

This investigation supports changing the next **question**, not choosing a universal foundation. The strongest uncertainty is author benefit: neither readable notation in a paper nor successful kernel replay measures whether extracting and editing a theory is easier than designing it directly. No current implementation cost, author-effectiveness result, full transitive source proof audit, or comprehensive survey is claimed.

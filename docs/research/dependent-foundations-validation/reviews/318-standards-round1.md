# #318 Standards review, round 1

Outcome: **Passed**. Findings: **0**. Worst severity: **none**.

Reviewer: `/root/review316/standards318`. This is an independent Standards assessment within the existing review loop. The Spec outcome was present in the supplied coordination record but was not used as evidence for this conclusion. No prior Standards findings existed, and no finding IDs were issued. IDs `318-STD-001` onward remain available for later rounds.

## Fixed scope

- Base and merge-base: `d7d2beeea699bccc2f7eb0fee7f8fa52e6718186`.
- Candidate: `de2b1987e2f2caaad83ecddedb05c3ccded5bfff`.
- Candidate tree: `d38d7d450009a49f30c825dd3d1da07c1b5c0fb3`.
- Stable checkout: `/tmp/conaled-314-320/318`.
- Diff: `git diff d7d2beeea699bccc2f7eb0fee7f8fa52e6718186...de2b1987e2f2caaad83ecddedb05c3ccded5bfff`.
- Entire scope: all 307 added lines of `docs/research/concrete-dependent-coherence.md`, with no exclusions.
- Commits: `dba3d29 research: assess concrete dependent coherence benefit (#318)`; `195b5e1 chore(dependent): incorporate reviewed higher investigation (#318)`; `de2b198 docs(dependent): ground coherence decision in reviewed higher evidence (#318)`.

The full saved requirements are `specs/318.json`, `specs/orchestration.md`, and `specs/318-routing-notes.md` under `/tmp/conaled-314-320`. Their hashes match the exact-candidate validation record. The routing note is preliminary input, not the result being approved.

## Applicable standards and evidence

I read candidate `AGENTS.md`, README development/build/audit and isolated-experiment rules, `docs/agents/architectural-quality.md`, `docs/agents/domain.md`, `GLOSSARY.md`, the ADR index and ADRs 0001/0010, and `docs/language-direction.md`. Review procedure came from the code-review skill, its heuristics, and `docs/agents/review-loop.md`. I used example-driven-development's statement-review guidance for descriptions of existing formal results and the no-ai-slop skill plus its reference for authored prose. No additional scoped AGENTS, CONTRIBUTING, or CODING_STANDARDS file was found in the reviewed document paths.

I inspected the handoff, candidate-specific artifact receipt and validator, coordination record, #314/#316 review records, architecture reassessment, #292 comparison and frozen memo, and the relevant incorporated #314/#316 reports. Source inspection included `DisplayCategory.lean`, `Comprehension.sectionsOver`, `FamilySquares`, `LocalUniverses.displayCurry`, the groupoid universe wrapper, the actual groupoid shear, and the Agda declarations for both substituted terms and both observations. Primary-source verification used the cited Lumsdaine–Warren, Kapulkin–Lumsdaine and Warren papers.

## Standards assessment

**Conditional construction methodology: satisfied.** Candidate lines 5–12, 31–57 and 261–280 compare a named dependent consumer across direct strict, local-universe, coherent-right-splitting and chosen-universe routes. Existing ordinary groupoid stability is not counted as a new benefit. The candidate preserves the alternatives and supplies a concrete promotion condition under #289. The direct higher investigation remains owned by #322, with the cubical programme separately owned by #321. This conforms to the architectural standard's requirement to identify actual reuse and remaining gaps and the language direction's distinction between research and adoption. The issue expressly permits this conditional deferral; a new categorical implementation is not a methodological prerequisite to reporting it.

**Derived structure and family arrows: satisfied.** Lines 91–133 use the existing all-square display category and accurately identify its fullness, pullback and cartesian-factorization results. The Type-family equivalence supplies both inverses and identity/composition preservation. `sectionsOver` quantifies over actual substitutions, so its groupoid specialization retains functor coherence. The C₂ shear is an actual functor on the Grothendieck construction and fails chosen horizontal-lift preservation. The report limits its consequence to the corresponding inclusion, retaining the separate concrete transformation-category correspondence. It does not reintroduce a derived fullness theorem as a generic assumed field or transfer it to incompatible arrows. This meets the architectural requirement to reuse existing constructions while preserving semantic distinctions.

**Transfer hypotheses and source attribution: satisfied.** Lines 137–156 and 190–240 state construction obligations rather than claimed local theorems. The LF representation quantifies over slice arrows, with evaluation, inverse laws and precomposition naturality. Whole-eliminator weak stability includes newly supplied motives and branches; pseudo-stability requires coherent chosen elimination. The cited transfer results support those distinctions and the separate treatment of additional type equations. [Lumsdaine–Warren, Definitions 3.1.2–3.1.3, Lemma 2.4.2, §3.4.3 and Theorem 3.4.1](https://arxiv.org/html/1411.1736v2).

The chosen-universe account retains constructor structure, internal lifting and size assumptions; it does not derive a lower bound for this universe-free fragment. [Kapulkin–Lumsdaine, Proposition 1.3.3, Definition 1.4.8, Theorems 1.4.15 and 2.3.4](https://arxiv.org/html/1211.2851v5). The strict ω-groupoid existence result remains external evidence, with finite-dimensional closure and the Lean interpretation still unproved. [Warren, Theorem 7.1](https://mawarren.net/papers/crmp1295.pdf).

**Ambient/generated and universe boundaries: satisfied.** Lines 163–188 distinguish the carrier universes from the collection of groupoids, identify the existing lifted instance, and retain closure obligations for new higher families. Ambient terminality, a reachable component, and generated contexts/arrows remain distinct. The report asks for actual terminal/product universal properties and closure of the selected bases under representing objects. It neither infers LF failure from the generic countermodel nor treats generated empty-map existence as uniqueness.

**Reviewed evidence and selected observations: satisfied.** Lines 17–27 and 59–80 use the incorporated approved #314/#316 revisions. The Agda references match the actual generic two-substitution comparisons, conjugate higher observation and erasure rejection, and circle-cover values. The failed strict-natural contraction is kept separate from a substitution-strictification failure. Lines 242–257 retain the named native clients, type-dependent term comparisons, composition and branch compatibility, and the selected higher witness. These descriptions comply with statement-review guidance concerning domains, assumptions and equality notions. No new formal declaration is introduced, so new checked specializations and a new formal build are not required by this diff.

**Evidence limits, prose and repository conventions: satisfied.** Lines 282–307 distinguish builder work, author work and host encoding, make no productivity claim, and retain the compiler/proof boundary. The report does not claim categorical-package completion, Lean higher interpretation, or passage of the higher adoption gate. Quantities and attributions are traceable to sources. The repeated qualifications concern distinct mathematical failure modes and are useful cross-references rather than unsupported emphasis. Commit subjects follow Conventional Commits and carry #318.

**Heuristic judgment:** no concrete heuristic defect found. In particular, deferring unselected machinery does not abandon the repository's reusable-abstraction requirement: the report preserves exact construction obligations, selected consumers and an owned condition for promotion. Imposing a speculative framework now would not follow from the heuristics or the documented acceptance. No heuristic finding or remedy is proposed.

## Validation, separately from findings

Validation is **established for the documentation artifact scope**. I inspected and reused [the exact-candidate receipt](318-validation-de2b1987e2f2caaad83ecddedb05c3ccded5bfff.json) and its validator. It records 13 local targets, 18 named declarations, unchanged incorporated evidence, unchanged frozen discovery files, saved specification hashes, diff whitespace, a clean checkout and report identity. Declaration presence is not semantic validation; the source and theorem checks above address the report's interpretation separately.

A final read-only check in `direnv exec . python3` independently confirmed HEAD, tree, merge-base, clean checkout, the report SHA-256, specification hashes, the one-file 307-line diff and the commit list. The report SHA-256 is `6733f33320168ece9f27d08821ef4d6cd30a3d768048d94422ce7037471dc652`; its Git blob is `6b6c10e6cc6b0425cdb50335933d46b6e9ff3a56`.

No Lean or Agda compilation was run or claimed for this documentation-only candidate. #314's build/audit and #316's isolated Agda validation retain their own reviewed scopes. No source, branch, tracker, merge, or frozen-evidence change was made by this review. The sole write is this report outside the candidate checkout.

Standards outcome: **Passed**, **0 findings**, worst severity **none**. Base: `d7d2beeea699bccc2f7eb0fee7f8fa52e6718186`. Candidate: `de2b1987e2f2caaad83ecddedb05c3ccded5bfff`. This approval covers the stated conditional assessment, not a completed categorical package or higher-model adoption.

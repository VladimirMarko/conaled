# #318 Spec review, round 1

**Outcome: Passed. Findings: 0. Worst severity: none.**

The candidate meets #318's explicitly permitted conditional-deferral outcome. It identifies the frozen dependent consumer, compares four construction routes on that consumer, uses the reviewed reconstruction and higher-investigation evidence, and records the missing categorical obligations and promotion conditions under #289. This approval does not certify construction of a higher Lean interpretation, LF for a concrete groupoid or Kan package, or the higher adoption gate.

## Fixed scope and requirements

- Base and merge-base: `d7d2beeea699bccc2f7eb0fee7f8fa52e6718186`.
- Candidate: `de2b1987e2f2caaad83ecddedb05c3ccded5bfff`.
- Candidate tree: `d38d7d450009a49f30c825dd3d1da07c1b5c0fb3`.
- Checkout: `/tmp/conaled-314-320/318`, clean and at the fixed candidate.
- Diff: `git diff d7d2beeea699bccc2f7eb0fee7f8fa52e6718186...de2b1987e2f2caaad83ecddedb05c3ccded5bfff`.
- Scope: all 307 added lines of `docs/research/concrete-dependent-coherence.md`. No exclusions.
- Commits: `dba3d29`, `195b5e1`, `de2b198` as recorded in the coordinating review record.
- Requirements: the complete saved `specs/318.json`, `specs/orchestration.md`, and `specs/318-routing-notes.md`. Routing was assessed as preliminary input, not as a supplied conclusion.
- Evidence: `318-handoff.md`, `318-review.md`, and the exact-candidate artifact validation record. No prior findings existed.

The review applied the existing code-review workflow's Spec axis and statement-review checks to the mathematical descriptions. It inspected the relevant unchanged definitions and applications. No nested implementation/review loop or child agent was started.

## Acceptance assessment

### Consumer, gain, and conditional decision

Lines 30–57 fix the same terminal/dependent/Σ/Id/contextual-J fragment for all four routes. They retain both substituted terms, the transported source of `apd_η(h)`, integer transport values 3 and 2, and the conjugated higher observation. They correctly avoid requiring `apd_η(h)` itself to be nontrivial. Schematic parameters are distinguished from an object-language universe.

The comparison does not promote ordinary groupoid substitution recovery into a new benefit. The existing `GroupoidSoundness.fullModel` supplies `contextualJ`, its computation law, and `contextualJ_sub` for arbitrary admitted motives and tails. The direct higher route remains a proposed construction. Local universes have a concrete possible use for a weak higher provider; right splitting and chosen universes have distinct input obligations. The report does not claim equal capability or infer rejection from a missing adapter to current source annotations.

The deferral is justified at this stage because the reviewed direct higher investigation has not exhibited a weak higher provider whose remaining gap is strict substitution, nor a matched construction with recurring coherence work eliminated by a strictifier. This is the issue's allowed initial assessment, not completion of its conditional construction branch. Lines 263–280 give a testable trigger: select a weak model providing the required higher dependent capability and identify strict stability as the missing step, or demonstrate recurring construction work removed by transfer. #289 owns the resulting categorical and comparison proofs. #322 owns the direct higher prerequisite; #321 owns the separate cubical alternative.

### Reviewed evidence and the higher boundary

Lines 16–26 identify the incorporated approved #314 and #316 revisions and explicitly preserve #316's precise-prerequisite outcome. Lines 59–86 match the underlying source statements:

- `FrozenMemo.agda` constructs the genuine dependent pair and transported dependent action; `w-twice` and `apd-twice` compare repeated with direct substitution.
- `HigherWitness.agda` applies these declarations to the selected second inductive identity. `observation-detects-one` observes the conjugate of `ap_T(h)`, and `erasure-rejected` rejects its replacement by reflexivity.
- `Monodromy.agda` proves the two different transport values through the same generic consumer.

The report accurately treats those declarations as external source evidence. It does not convert their compilation receipt into a Lean interpretation theorem. Its description of the missing higher-family action and coherent contraction agrees with the reviewed #316 prerequisite. That semantic data gap does not establish a substitution-strictification failure.

### Actual family arrows and comprehension

Lines 89–133 select all commuting display-map squares explicitly. `DisplayCategory.lean` defines exactly those homs, an explicit fully faithful comprehension functor, a pullback theorem, and unique cartesian factorization. The report does not transfer this fullness result to an unproved category of concrete transformations.

`FamilySquares.equivalence` has both inverse laws; `equivalence_comp` and `equivalence_id` supply the claimed functorial compatibility. `Comprehension.sectionsOver` represents sections by actual substitutions into an extension over a fixed base substitution. In the groupoid instance these are functors, including arrow data. `GroupoidComprehensionBoundary.shear_over_base` and `shear_not_horizontal` support the stated C₂ obstruction. The report limits that obstruction to preservation of the chosen cleavage and leaves the pseudonatural comparison open.

### Exact remaining categorical obligations

Lines 163–188 read the concrete `Context`, `Family`, lifted `Section`/`Substitution`, and `universeModel` interfaces correctly. They separate the universes of carriers from collections of groupoids and require closure for the new higher families. Terminality and products are specified by their universal properties. The distinction between ambient contexts, reachable objects with ambient arrows, and generated contexts with generated arrows agrees with #314's countermodels. Generated empty-map existence is not used as uniqueness.

Lines 190–209 state LF using actual slice hom sets for every `W → Γ`, with evaluation, both inverse equations, and naturality under every map over Γ. Both required classes of `g` are present. Fiberwise objects alone are explicitly insufficient, and the representing object need not be an object-language type. This is an exact outstanding representation obligation, not a new field assuming the desired theorem.

### Constructor stability, equations, and comparisons

Lines 211–240 retain complete dependent Σ and Id elimination, finite tails, arbitrary newly supplied motives and branches, computation, and any choice principle used to select operations. Weak stability is not described as preservation of an already chosen eliminator. Right splitting requires coherent comparisons for that chosen eliminator, including identity and composition behavior. The classifier route requires coverage and closure plus decoding compatibility. Additional strict code-decoding type equations remain separate obligations.

Lines 242–257 name the old generated transfer proof and groupoid interpretation, the dependent conversion client, and the native Type-family pair. Required comparisons act on contexts, families, terms, substitutions, and branches, with terms carried through their type comparison. The higher detector must remain attached to the interpreted selected observation. The report neither rejects intentionally lossy interpretations at their declared observation level nor allows them to certify the higher gate. No replacement is adopted, so this conditional outcome does not require new client-recovery proofs now.

## Primary-source verification

The cited primary sources were opened independently and checked against the claims used by the report:

- Lumsdaine–Warren: Definitions 3.1.2–3.1.3 specify the slice representation and LF; Theorem 3.4.1 has full comprehension, LF, and constructor stability hypotheses. Section 3.4.3 includes dependent tails. Lemma 2.4.2 and its following discussion distinguish whole-constructor pseudo-stability from weak elimination. Section 4.1 excludes additional type-equality rules from its extension recipe. These support the report's obligations without constructing their local instances. [Primary source](https://arxiv.org/html/1411.1736v2).
- Kapulkin–Lumsdaine: Proposition 1.3.3, Definition 1.4.8, and Theorem 1.4.15 support the chosen-universe construction and its elimination requirements. Theorem 2.3.4 has the stated inaccessible size assumption and an additional inaccessible for the internal universe. The report does not present these as lower bounds for the frozen fragment. [Primary source](https://arxiv.org/pdf/1211.2851v5).
- Warren: Theorem 7.1 supplies the stated intensional Π/Σ/Id interpretation and η-rules. It does not prove the project's proposed finite-dimensional restriction or Lean interpretation. [Primary source](https://mawarren.net/papers/crmp1295.pdf).

The earlier reassessment, its linked assessments, #292, the frozen memo, and the client fixture were used as contextual evidence. Their proposed diagnoses were checked against the newer #314/#316 results rather than treated as proved conclusions.

## Validation status

**Applicable validation: passed.** The supplied record `318-validation-de2b1987e2f2caaad83ecddedb05c3ccded5bfff.json` covers local targets, declaration references, unchanged incorporated evidence, frozen discovery files, specification identities, whitespace, candidate identity, and a clean checkout. I inspected its generating script and confirmed that declaration presence is only an artifact check; the semantic checks above were separate.

A read-only reviewer check through `direnv exec . python3` reconfirmed the candidate, tree, clean status, report SHA-256 and Git blob, specification hashes, and validation-script hash against that record. The report SHA-256 is `6733f33320168ece9f27d08821ef4d6cd30a3d768048d94422ce7037471dc652`. The diff statistic and merge-base were independently confirmed.

No Lean or Agda source changed. No new Lean/Agda build or proof audit was run or required for this documentation-only candidate. The incorporated formal evidence retains its previous validation scope; this review does not expand it. No source, branch, tracker, merge, or frozen artifact was changed by this review.

## Findings and disposition

No findings. No `318-SPEC-*` identifiers were allocated. No missing required evidence blocks this axis.

Base: `d7d2beeea699bccc2f7eb0fee7f8fa52e6718186`.
Candidate: `de2b1987e2f2caaad83ecddedb05c3ccded5bfff`.
Spec outcome: **Passed**, zero findings, no worst severity.

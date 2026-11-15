# #319 Standards review, round 1

Outcome: **Passed**. Findings: **0**. Worst severity: none. No unresolved prior findings were supplied, and this review introduces no finding IDs.

Reviewed candidate: `f0773fee8fa40214c67606c46ba8c41eed8e674b`.
Base and confirmed merge base: `3484ce523bf23524f715a3a2029c290a2d43c4c0`.
Scope: committed changes only, no exclusions, using `git diff 3484ce523bf23524f715a3a2029c290a2d43c4c0...f0773fee8fa40214c67606c46ba8c41eed8e674b` in `/tmp/conaled-314-320/319`. The checkout's HEAD matched the candidate and its worktree was clean. The four commits are `8ad581f`, `285383d`, `93d69f3`, and `f0773fe`; their subjects follow the required Conventional Commits format and reference #319.

The complete change is five files and 809 added lines: `SquareKit/Internal/NestedSetting.lean`, `Examples/NestedSetting.lean`, the public import in `SquareApplications.lean`, and the two `docs/research/internal-setting-*` documents. I read both Lean files and both documents completely, inspected the entrypoint diff, and followed relevant unchanged definitions and Mathlib implementations. This is an independent Standards review within the existing loop; it does not replace the separate Spec review.

## Applicable standards and evidence

I applied candidate `AGENTS.md`, `docs/agents/architectural-quality.md`, `docs/language-direction.md`, `docs/agents/domain.md`, the glossary, ADRs 0001 and 0010, README's development/build/audit instructions, the preservation-contract inventory, and the example-driven-development statement-review instructions and worked example. The code-review heuristics were subordinate to those requirements. Prose was assessed using the no-ai-slop guidance. No nested directory guidance applies to the five changed files.

The supplied requirements were `specs/319.json` and `specs/orchestration.md`; I also read the supplied handoff and persistent review record. I used the architectural reassessment and relevant passages of its three assessments, #292's report, and the frozen external memo as context. Their proposals were not treated as checked mathematical dependencies. No standalone orbifold formalization was used.

## Architecture and statement review

All new definitions, theorem statements, equivalence inverse laws, examples, and failure claims were inspected. The following groups account for the complete new formal development.

| Candidate location | Review result |
| --- | --- |
| `SquareKit/Internal/NestedSetting.lean:18–49` | `Setting` is an actual Type slice. `settingEquivalence` invokes the objects-and-morphisms iterated-slice equivalence. `Q` ranges over predicates on the constructed first total, rather than over an unrelated externally supplied model. `reindex` substitutes along the first `totalMap`; `map` applies the second total construction. Identity and composition have the correct contravariant substitution order. |
| `SquareKit/Internal/NestedSetting.lean:51–137` | `Pullback` retains the new base point, original dependent pair, and base equation. `comparison` constructs both directions and proves both inverse laws. Its two projection laws preserve the full data. The composition/rebase statements preserve both nested components and the equality certificate. `formed_isPullback` supplies commutativity, joint injectivity, and existence via `Types.isPullback_iff`, establishing the categorical universal property rather than assuming it in a record. The second slice equivalence and `comparisonSettings` use actual categorical equivalences. |
| `SquareKit/Internal/NestedSetting.lean:139–165` | `settingSub` is Mathlib's inverse-image functor on slice objects and morphisms. Identity and composition are natural isomorphisms, with the expected order. `setting_term_twice` specializes the existing `Family.termSub_composition` to arbitrary slice sections. I inspected `Family` and `FamilyCoherence`: the inherited canonical pullback comparisons have the stated unit, associativity, and term laws. No definitional equality between arbitrary chosen pullbacks is claimed. |
| `SquareKit/Internal/NestedSetting.lean:167–212` | `Ty` admits any Type-valued family at the declared universe. Type and term substitution are precomposition by the same nested map. The term cast in `term_comparison` uses exactly `type_comparison`, which is induced by preservation of the original nested value. `dependent_comparison_comp` compares the entire Sigma pair, including its index and selected dependent term, after two substitutions. Its conclusion is stronger than an equality of tags or an inhabitation statement. |
| `SquareKit/Internal/NestedSetting.lean:214–297` | `Argument` retains the second section over the first chosen section. `normalize` transports the whole dependent pair along the base equation; its eta result supports recovery. `recover_classify` and `classify_recover` establish both inverses. `argumentEquiv` classifies pairs over identity, while `argumentOverEquiv` quantifies over arbitrary base substitutions and retains the equation over that substitution. The inverse is constructed through the proved comparison and recovers both selections. |
| `SquareKit/Internal/NestedSetting.lean:299–345` | Model recovery uses the existing finite model/section correspondence. Generic recovery pulls back the actual first and second generic models along the classifying maps. These are section-classification claims, not a new arbitrary-source geometric-morphism theorem. Argument substitution, its unit/composition equations, classification compatibility, and the selected comparison retain the second component's dependency. |
| `Examples/NestedSetting.lean:11–81` | The selected sections satisfy the finite scheme through the existing public interpretation. Zero forbids the first left branch; the two choices at the same positive index give different second predicates. Thus the premises are usable and the dependence is not merely variation in the original Nat index. Generic recovery, actual slices, the second classifier coproduct isomorphism, and the section equivalence are exercised through public results. |
| `Examples/NestedSetting.lean:83–155` | The retained cases use public argument, pullback, type, term, and whole-dependent-value results. The composite is `shift ∘ double`, yielding `2*n+1`. The finite payload depends on the second tag as well as the original index. The two orders yield different values, and `payload_whole_twice` preserves the exact nested value and `Fin 7` witness through `dependent_comparison_comp`. |
| `Examples/NestedSetting.lean:157–178` | `erase` is a well-typed map over the base. `erase_fails` refutes its promised tag preservation. `no_second_left` and `cannot_repair_second` quantify over every candidate in the erased first branch and show why retaining the second-left observation is impossible. This does not impose faithfulness on an intentionally lossy interpretation with a weaker contract. |

The generic declarations use same-universe bases and payloads, as disclosed in the handoff. There is no hidden decidability premise on either predicate, no assumption of the desired comparison, and no circular coherence field. Classical model-to-section extraction is inherited and documented; the selected concrete branches and explicit comparison do not decide arbitrary predicates. Native equality and proof irrelevance remain separate from retained sum tags and finite payload data.

The fixture commits precede implementation and record independent expected tags, dependency, composition order, universal section interpretation, and failure behavior. The later payload specialization supplies additional concrete data and connects to the general theorems. The report explains the unsuccessful componentwise transport as an encoding failure; it does not claim an unproved mathematical obstruction. This meets the EDD requirement without manufacturing a runtime test or a failed proof where existing results already suffice.

The shared library exposes the construction and reusable comparisons; the client contains chosen predicates, sections, numerical observations, and the erasure counterexample. Existing interfaces are reused, and existing clients are unchanged. The report identifies the impact on #314/#315 and assigns broader constructor and higher-model questions to #317/#36/#235 and #316/#321. It does not convert this bounded specialization into a universal architecture or an author-usability measurement. No heuristic produced a concrete maintenance, semantic, or caller-cost defect requiring a finding.

## Research claims and boundaries

The report explicitly distinguishes the finite geometric syntax from Lean-hosted arithmetic/tag predicates and metatheoretic slice formation. Inspection of `FiniteSetting`, `FiniteClassifierComparison`, and the pinned Mathlib slice code supports that description. The second presentation is built in the first constructed context, and the old coproduct and model-section results are consumed. This is sufficient for the stated shallow Set-family specialization; it is not an object-language universe of categories or arbitrary internal sites.

I checked the cited primary-source passages. Awodey's Proposition 2 assumes a small context category with terminal object and a natural transformation of presheaves; the report uses it as context for the display-map account and does not infer that every project model satisfies it. [Natural models, §1 and Proposition 2](https://arxiv.org/html/1406.3219v4)

The Stacks theorem concerns a sheaf topos sliced over a sheaf and identifies the localization inverse image. Its role is categorical context; the Lean proof instead uses the actual Type slices and pullback construction. [Stacks Project, Lemma 7.30.1](https://stacks.math.columbia.edu/tag/04GY)

MTT's locks act contravariantly, and its models require a supplied mode theory together with mode-local CwFs and modal structure. The report correctly treats those access rules as distinct from constructing this context-dependent presentation. It makes no claim that MTT alone supplies the new internal setting. [Gratzer et al., §§2, 4–5 and Figure 3](https://www.danielgratzer.com/papers/multimodal-dependent-type-theory.pdf)

The report's extensional boundary is consistent with the code: there is no higher identity interpretation or contextual J construction. The higher adoption gate remains separate. References to future work are scoped owners rather than assumptions smuggled into the present theorem.

## Validation

Validation status: **Passed for the exact reviewed candidate**, using the supplied logs rather than repeating successful full checks.

- `319-integrated-candidate.log` identifies candidate `f0773fee8fa40214c67606c46ba8c41eed8e674b`, successful source/coverage/version checks, all 1016 checked modules, and the exhaustive audit. The transitive axiom union is exactly `propext`, `Classical.choice`, and `Quot.sound`.
- The audit includes the new library module (99 logical declarations, 60 theorem declarations) and client (34 logical declarations, 20 theorem declarations), each with zero unsafe runtime declarations. Generated declarations explain why these counts exceed the visible named statements.
- The guard's initial invalidations are missing traces for the newly incorporated #314 modules. The final guard hashed 3045 artifacts and reported zero inconsistent modules. There is no evidence here of an unexpected integrity failure.
- `319-integrated-audit-regressions.log` passes the unused-external-axiom, private-transitive-axiom, private-admission, and source-unsafe cases.
- `319-integrated-verification.json` records the exact candidate, Lean 4.35.0, the pinned dependency revisions, incremental mode, and a passed result. `319-integrated-verify.log` confirms the matching receipt after regressions.
- My `git diff --check` found no whitespace errors. No build tooling, toolchain, or dependencies changed in this scope, so a fresh rebuild and build-tool regression rerun are not required by the applicable policy.

The coordinator retains the immediate final `--verify-candidate` step before approval. This review made no source, tracker, or merge changes.

Limitations: the review establishes the documented standards for this exact bounded candidate. It does not claim higher-model coverage, a general setting-constructor theorem, an ergonomic trial result, or a separate Spec-axis outcome. The full successful validation was inspected, not rerun. No required evidence was unavailable.

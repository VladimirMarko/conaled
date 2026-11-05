# #319 implementation handoff

## Integrated candidate (2026-11-05)

Candidate: `f0773fee8fa40214c67606c46ba8c41eed8e674b`.
Exact incorporated integration tip and new review base:
`3484ce523bf23524f715a3a2029c290a2d43c4c0`.
Merge commit: `chore(dependent): incorporate reviewed structure audit (#319)`.
The first parent is the previously validated #319 candidate
`93d69f361ebb9b368c0dfa610559a5b8c0871f12`; the second parent is the approved
#314 tip. The merge was clean. Both prospective fixture commits remain in
history, and the fixture, report, library module and examples are byte-identical
to the previous #319 candidate. Only the public-entrypoint imports needed
combining. Relative to the new review base, the task remains five files with
809 added lines. The statement review below therefore remains applicable;
this integration changed no formal statements or proofs.

Exact-candidate validation passed under the shared build lock:
`direnv exec . flock /tmp/conaled-314-320/build.lock ./check.sh --candidate HEAD`.
Log: `reviews/319-integrated-candidate.log`. All 1016 modules and the exhaustive
axiom audit passed in 25.21 seconds. Axiom union:
`[propext, Classical.choice, Quot.sound]`. Post-build integrity guard hashed
3045 artifacts and found zero inconsistent modules. Missing pre-build traces
belonged to the newly incorporated #314 modules and were expected.

All four proof-audit regression cases passed under the shared lock via
`direnv exec . flock /tmp/conaled-314-320/build.lock lake env python3 scripts/test-proof-audit.py`:
unused-external-axiom, private-transitive-axiom, private-admission, source-unsafe.
Log: `reviews/319-integrated-audit-regressions.log`.
Final `direnv exec . flock /tmp/conaled-314-320/build.lock ./check.sh --verify-candidate HEAD`
passed after those regressions. Log: `reviews/319-integrated-verify.log`;
preserved receipt: `reviews/319-integrated-verification.json`. The receipt
matches the exact candidate, pinned dependencies and Lean 4.35.0 in incremental
mode. The checkout is clean.

Independent Standards/Spec review must use this candidate and new base; prior
#319 validation is retained below as provenance, not reused as this candidate's
acceptance evidence. No tracker, master, shared documentation or frozen-fixture
edits were made during this integration.


## Resumed candidate (2026-11-05)

Candidate: `93d69f361ebb9b368c0dfa610559a5b8c0871f12`.
Review base: `9b0a0fe143c6f97f399632d4bb34a179db012181`, confirmed as the
current integration tip before committing and an ancestor of the candidate.
The complete task diff includes the two prospective fixture commits and the
implementation commit. The existing implementation was preserved without
source changes during resume; the final focused log completed successfully
after the last source edit (1239 jobs, including `payload_whole_twice`).
The checkout was clean when candidate acceptance started.

Resumed inspection confirmed the statement-review claims below against all
new statements, the concrete cases, and existing Family coherence. Primary
source passages rechecked: Awodey Proposition 2, Stacks Lemma 7.30.1, and MTT
the contravariant lock rules and Definition 5.1. No additional mathematical
hypothesis or review limitation was found. Independent Standards/Spec review
remains the coordinator's next step after acceptance validation.

Validation log: `/tmp/conaled-314-320/reviews/319-candidate-check.log`.
Command: `direnv exec . flock /tmp/conaled-314-320/build.lock ./check.sh --candidate HEAD`.
Candidate validation passed: all 1005 modules, source/coverage/version checks,
incremental compilation, and exhaustive proof audit (42.04 seconds total).
The transitive axiom union is exactly `propext`, `Classical.choice`, `Quot.sound`.
The new example module contributed 34 logical declarations/20 theorem
declarations; the new library module contributed 99 logical declarations/60
theorem declarations. Neither has unsafe runtime declarations. The integrity
guard rebuilt absent traces from the partially populated private project cache;
post-build verification hashed 3012 artifacts with zero inconsistent modules.
There were no unexpected mismatches or integrity failures.

`direnv exec . ./check.sh --verify-candidate HEAD` passed for this exact commit.
Its log is `reviews/319-candidate-verify.log`; the preserved receipt is
`reviews/319-verification.json`, both under `/tmp/conaled-314-320`.
README's proof-audit regression suite passed all four cases under the shared
build lock: unused external axiom, private transitive axiom, private admission,
and source unsafe declaration. Log: `reviews/319-audit-regressions.log`.
Candidate verification passed again after those regressions, and the checkout
remains clean. No build tooling or dependency changed, so no fresh rebuild or
build-tool regression suites were added.

The original interrupted handoff follows for provenance.

Status: implementation complete, final focused and exact-candidate validation pending; full acceptance held at root's request until the Agda closure exits.

- Worktree: /tmp/conaled-314-320/319, branch research/internal-setting-319.
- Current review base: 9b0a0fe143c6f97f399632d4bb34a179db012181, still reviewed integration tip at last check. Recheck before candidate handoff.
- Prospective freeze:8ad581f, clarification285383d, both before implementation. Root checkpoint approved internality proposal with exact source/host boundary requirement; clarification records it.
- Scope: SquareKit/Internal/NestedSetting.lean; Examples/NestedSetting.lean; public import in SquareApplications.lean; docs/research/internal-setting-fixture.md; docs/research/internal-setting-construction.md. Root shared docs untouched. No tracker edits, Lean tooling/dependency changes or #107/#108 work.

## Intended claims and statement review

1. Construct the internal finite geometric setting from arbitrary predicate P, then Q over the first generic model's total. Setting is the actual Type slice; settingEquivalence and secondSettingEquivalence use Mathlib's objects/morphisms iterated-slice equivalence. Existing formedClassifierIso is consumed in a checked second-stage example. Arithmetic/tag predicates are Lean-hosted base expressions; geometric formula/sequent scheme is existing syntax, slice formation its metatheoretic interpretation. This does not claim object-language categories or arbitrary internal sites.
2. Construct reindex/map and equality-bearing Pullback comparison, with inverse laws, retained base/original projections, identity/composition and rebase associativity. formed_isPullback discharges actual categorical pullback via Types.isPullback_iff using existence/uniqueness, not an assumed comparison field. All base functions and all Q predicates admitted. Native equality only.
3. Types are arbitrary Type-valued families over the nested total. type_comparison provides the actual equality used by term_comparison; dependent_comparison_comp compares entire Sigma values after two substitutions. No witness erasure. settingSub gives slice inverse-image functors with natural identity/composition isos; setting_term_twice uses Family.termSub_composition for arbitrary slice sections. Existing FamilyCoherence unit/associativity is inherited, no claim that arbitrary chosen pullbacks are definitionally equal.
4. Argument is first section plus second section over that first choice. normalize/recover transport the entire pair; argumentEquiv and argumentOverEquiv establish inverse universal classification over identity/all base substitutions. argumentOfModels and model-recovery statements consume existing finite modelSectionEquiv; generic recovery establishes the two interpreted models along classifying maps. No new arbitrary-source geometric-morphism classifier theorem claimed.
5. Concrete P(n)=0<n, Q(a)=a.isLeft. Zero rejects first-left; a positive base permits choices with different second fibers. Selected argument chooses both left at successors/right atzero. Extra payload Fin(n+2) or Fin1 depends on second choice. Composition-order calculation gives original2n+1; payload6 atn2, values2 vs3 atn0 when order reversed. Checked examples invoke public general comparison/substitution/universal properties.
6. erase is a well-typed map over base. It fails only the promised tag contract; no_second_left/cannot_repair_second prove the erased first choice excludes preservation of second-left. No global faithfulness requirement imposed on deliberately lossy interpretations.

All generic assumptions inspected: universe u fixed across base types and payloads; no DecidablePred P/Q required, no circular coherence record, no extra axioms. Models->sections inherits existing classical choice; selected concrete sections and comparison constructions do not decide arbitrary predicates. Props proof irrelevant, sums/Fin payload exact data. No higher identity or contextual J claim.

EDD expectations fixed in fixture. Existing lemmas were reused rather than artificial red tests. Attempted separate transport of first component failed to type the second; normalized whole dependent pair fixes encoding, not a mathematical counterexample. Runtime tests inappropriate for proved behavior. Final source retains no scratch obligation.

## Research and architectural outcome

Report compares split families and display/slice presentations, supported by Awodey Proposition2, Stacks Lemma7.30.1 and pinned Mathlib Over implementation. MTT §§2,4–5/Figure3 inspected as separate modal-context option, not alleged solution of internal construction. Exact theorem scope and host/model boundaries recorded. Positive result: second finite construction inherits reindexing from existing structure without new law fields. #314/#315 should allow subsequent presentation depending on generic data in constructed context; comparison and interpretation cannot be independent boundary layers. Adopt bounded specialization, investigate other constructors under317/36/235, higher remains316/321, modal297 distinct, external discovery301 unaffected.

## Validation evidence

Focused build through universal-over-substitution addition passed (1239 Lake jobs). Latest run adds explicit no-first-left-zero and whole dependent payload composition specialization, pending completion. Five local documentation links checked. Whitespace passed. Full exact-candidate build/exhaustive audit/receipt to be appended after resource release and clean candidate commit. No source changes during running focused build.

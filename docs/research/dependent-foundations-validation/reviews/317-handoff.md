# #317 implementation handoff

Candidate: `7b8c00ae171c8a0b6de696e42aaf8470ff1e7c96`. Clean committed tree; full incremental candidate acceptance, all four audit
fixtures and immediate verification passed. Fixed approved base:
`bb77d67171e6cb610e43149394c8a9b9a0deab3f`. Worktree
`/tmp/conaled-314-320/317`, branch `experiment/dependent-constructor-317`.
Full requirements: saved `specs/317.json`, `specs/orchestration.md`, and
`records/317-dispatch.md`. Root confirmed bb77 remains latest approved integration;
unreviewed shared-doc draft 250a251 is deliberately excluded.

Checkpoints: c7ddcfc admits the semantic operations and guarded rules; d144e1a
adds derived introduction/elimination, semantic stability/maps/native comparison,
source author interface, exact reduct, rejection and valid law composition.
Candidate commit 7b8c00a adds source reindexing, typed source-map preservation,
concrete successive/composite clients and the primary-source report.

## Mathematical result and statement review

The base is the reviewed no-object-Sigma Contextual theory. New object formation
and actual pair sections are distinct from its preexisting context pairing.
The chosen capability is a full over-base comprehension isomorphism between
Gamma.A.B and Gamma.Sigma(A,B), with both inverse laws. This selects judgmental
eta. Split is branch substitution along unpack; its output type alignment uses
pack_unpack. Beta uses unpack_pack. No beta-only semantic realization is claimed.

The initial expected case was a pair (n,i) with i : Fin(n+1), eliminated into the
value-dependent motive Fin(first(pair)+1) to return i. Native reduction alone
already computes this; the missing connection was a reusable admitted source
argument and generic capability theorem. `Authoring.splitDerivation` is source
model-independent. `Examples.GuardedSigma.dependent_elimination_admitted` uses
`Sigma.interpret` with four constructed typing assumptions. `source_beta_selected`
uses `splitBetaDerivation` and that same interpretation theorem to recover the
exact supplied bounded index. Zero's singleton fiber and ordinary object-pair
beta are retained. These are connected claims, not independent arithmetic proofs.

Semantic helper statement review and exact cases are in
`317-semantics-handoff.md`; public type/axiom spot-check evidence in
`317-semantics-statements.log` and `317-source-maps-statements.log`. It constructs
Stable from sigma_sub/pack_sub only, derives unpack/branch/split/pair stability,
identity/composition with the actual family comparisons, and derives model-map
split preservation from sigma/pack preservation. Native Fin/Option comparisons
change dependent families, context and motive, preserve the selected `some zero`
value and recover the selected source section. These native Type cases do not
pass the open higher-model gate.

`Recovery.retain_certificate` and `retain_dependentAction` retain named source
arguments. `recover_certificate`, `recover_dependentAction`,
`recover_transportedSource` and `recover_value` prove exact evaluation equality
under reduct, for arbitrary underlying contextual models with the capability.
The transported source in the higher dependent action is not erased. This is
conditional recovery, not a construction of Sigma on every old model.

`Reindexing.model` extends the same signature with stability equations derived
from Stable. Its `interpret` matches the base argument order (derivation, model,
capability, assignment, assumptions). `ReindexAuthoring` constructs intermediate
sum domains and motive/branch typing from the initial data. The source
`splitSubComp` and `pairSubComp` rebuild twice for arbitrary base substitutions;
`splitSubComposite` invokes inherited term-substitution composition to relate the
same rebuilt term to the composite of the lifted arrows. Concrete
`Examples.GuardedSigmaReindexing.Nonidentity.twice_fresh` / `composite_fresh`
interpret these source proofs at A(n)=Fin(n+1), B(n,a)=Fin(a.val+1), a dependent
motive, shift n↦n+1 and double n↦2*n. Samples establish the order difference 3
versus 4 at n=1. `fresh_composite` separately instantiates source naturality at
the base composite. The semantic `sumMap_comp` compares composite sum lifts
with the canonical base-composite lift and its explicit family comparison;
these distinct source and semantic conclusions are not conflated.

`SourceMap` extends the existing full ModelMap, preserving old Id/J and Sigma
with a single structural map. `interpret_map` applies only to defined source
expressions; `interpret_term_map` consumes a semantic term guard, including one
obtained from the final Reindexing interpreter. It does not transport arbitrary
junk equality. The base typed facade requires typed assumptions, and
`splitDerivation_target`, `Tm.pair_map`, `Tm.split_map` are generic source clients.
The final source equation/data preservation is proved from primitive maps and
capability laws rather than supplied by a caller. Helper record:
`317-reindex-handoff.md`, plus the SourceMaps addendum to semantic handoff.

`Composition.closureModel` constructs a second extension by a split-eta law over
an empty new signature. Its validity follows from the original inverse laws;
clients do not supply another coherence proof. `closure_reduct`, `retain_twice`
and `recover_twice` cover the two-stage composition. This is valid sequential
admission, not a claim about arbitrary new equations or universal conservativity.

`Rejection.collapse_boundary` establishes the type boundaries for Sigma(Unit,Bool)
and Unit. `no_collapse_equivalence` proves even an equivalence impossible, and
`collapse_rejected` refutes semantic admission of the type equation. A separate
`missing_dependency_rejected` omits the B-family guard and uses invalid data to
refute that malformed admission attempt. Its raw parameter remains in scope;
this is a missing dependent-domain check, not a universal syntax scope checker.

Main statement review inspected quantifiers and directions of pack/unpack,
dependent branch and pair-second types, the selected eta dependency, actual term
versus family equality, and witness content of Value.term rather than only its
inhabitation. All rule premises are satisfiable in the native cases. Source
soundness is derived from primitive capability laws, never a final preservation
field. Congruence/conversion use the existing guarded source boundary; no BHL
adequacy or metatheorem import is asserted. Primary-source preparation is checked
in `317-framework-source-check.md` and the report records the exact decision.

## Validation status

Focused builds passed for base source operations/rules, Pairing/Theory,
Authoring, Composition, Recovery/Rejection, semantic modules and SourceMaps.
`317-source-beta-build.log` records the admitted source selected-value case.
The final focused build passed both concrete example modules (861 jobs), including
source reindexing. Log: `317-final-focused-build.log`. Main explicit type/axiom
spot checks passed in `317-main-statements.log`; only the permitted axioms occur.
Final full candidate acceptance passed; details follow.

A concurrent focused build of Examples.GuardedSigmaReindexing regenerated
Reindexing.olean at 03:13:21 +0100 while the helper ran a direct Lean check. That
helper reported a missing dependency artifact. No full check, clean, deletion or
integrity guard ran. The main build log records successful Reindexing generation
followed by ordinary source errors in the helper's changing ReindexAuthoring.
Current olean/ilean/hash/trace files exist. Preserved evidence is in
`records/317-reindex-overlap/` and `317-reindex-missing-output.log`; the latter
is the saved direct-Lean diagnostic, without an embedded observation timestamp.
The helper resumed with exclusive focused-build ownership and passed. This is
a transient missing-output observation during a concurrent Lake rebuild, with no
observed incorrect declaration or output corruption. It is not classified as
an integrity defect. The final candidate guard checked 3,252 artifacts with zero
invalidated or inconsistent modules. No manual cleanup, hash repair or guard
bypass occurred; no #272 integrity-incident claim is warranted by this evidence.
The full candidate check is serialized after all helper writers stopped.

No push, merge, issue closure, #107 resumption, #108 selection, #260 activation,
#322 implementation or held-out #320 task selection occurred.

## Final candidate acceptance

All commands ran in the private checkout under
`flock /tmp/conaled-314-320/build.lock`, via
`records/317-acceptance.sh`, after helper source ownership was released.

- `direnv exec . ./check.sh --candidate HEAD`: PASS on exact candidate
  `7b8c00ae171c8a0b6de696e42aaf8470ff1e7c96`, all 1,085 modules and exhaustive
  proof audit. Only propext, Classical.choice and Quot.sound occur. Total 25.19s;
  proof audit 17.76s. Guard hashed 3,252 artifacts before and after, with zero
  invalidated or inconsistent modules. Log `317-candidate-check.log`.
- `direnv exec . lake env python3 scripts/test-proof-audit.py`: all four fixtures
  PASS: unused-external-axiom, private-transitive-axiom, private-admission,
  source-unsafe. Log `317-audit-regressions.log`. Temporary fixtures removed.
- Immediate `direnv exec . ./check.sh --verify-candidate HEAD`: PASS, record
  matches this exact incremental candidate. Log `317-verify-candidate.log`.
- Receipt copied exactly from `.lake/verification.json` to
  `317-verification.json`; completion timestamp
  `2026-11-05T02:21:39.293372+00:00`, pinned Lean4.35.0 and dependency revisions
  recorded inside the receipt.
- Final `git status --short` is empty; retained zero-byte
  `317-final-status.log`. Fixed base bb77d671 is an ancestor of candidate.
- Report links resolve and `git diff --check` passes. No tooling/dependency
  changes; incremental acceptance is claimed, not fresh-mode acceptance.
- All helper builds/writers and the acceptance script are finished. No shared
  writable artifacts or hardlinked caches were introduced.

The candidate is ready for independent Standards and Spec review. The active
coordinator is `/root/review317`, record `reviews/317-review.md`; neither axis
has been reported passed at this handoff. No merge, push or tracker closure by
the implementer. Remain available for corrections in this same review loop.

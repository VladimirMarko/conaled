# Integration process and acceptance intake

Read-only assessment on 2026-11-13. Governing source revision:
`9175737c2b14ef738cfb6c2cdc68d885c0805ddd` (`conaled` master pinned by the coordinator
before implementation). The user's exception replaces remote issue/spec tracking
with local records persisted in each checkpoint. It does not waive architecture,
statement review, independent review, build, audit, or durability requirements.

**Conclusion:** the incoming records show substantial use of the repository's
implementation, statement-review and independent-review process, with materially
different validation outcomes across projects. They do not establish acceptance
of a new integrated candidate. Preserve their analysis and findings, then assess
the complete integration against the new pin. A mechanically clean merge is only
an intermediate source state.

## Current user clarification: Nix is optional

After the initial intake, the user explicitly made Nix optional while requiring
the pinned inputs to be preserved, and attached the native kit. The coordinator's
`intake/native-kit-compatibility.json` verifies that all299 kit files match the
embedded kit byte-for-byte, and that master9175737c's `lean-toolchain` and
`lake-manifest.json` match the kit's exact pin hashes. The earlier absence-of-Nix
blocker is superseded by this authorization. Compatible native execution may
establish the required baseline and validation gates; those gates still require
actual successful evidence. The active operational procedure is
`checkpoint/conaled-textbooks/docs/RESUME.md`. Setup success is not inferred from
compatibility or this instruction correction.

## Current user clarification: integration priorities

The user's subsequent priorities are **library coherence first, preservation of
useful mathematics second**. Unfinished developments may be improved before or
after merging. Select coherent existing owners and sound contracts, preserve
useful mathematical evidence and alternatives, and record justified correction
or replacement rather than mechanically retaining every historical formulation.
Old private chapter sequencing does not constrain the present integration.
These directions do not make an unvalidated candidate accepted or waive the
pinned workflow's exact-candidate proof, review and verification gates.

This assessment read the pinned instructions, the three current STATE records,
selected original process/acceptance evidence, and the complete current bodies
and all comments of issues149/458/459. It does not independently re-prove the Lean
development or authenticate every historical execution record. No source,
compiler, configuration, acceptance state or GitHub item was changed.

## Governing procedure at the pinned master

Primary sources:

- [AGENTS](https://github.com/VladimirMarko/conaled/blob/9175737c2b14ef738cfb6c2cdc68d885c0805ddd/AGENTS.md)
  routes implementation to the implementation skill, formal claims to
  example-driven development, and abstractions to architectural-quality/domain
  guidance. Its repository-default route is Nix/direnv; the current explicit
  user exception permits the compatible pinned native route.
- [Implementation skill](https://github.com/VladimirMarko/conaled/blob/9175737c2b14ef738cfb6c2cdc68d885c0805ddd/.agents/skills/implement/SKILL.md)
  requires saved complete requirements, a stable starting-state capture before
  edits, exact candidate validation, and a reviewer coordinator using code-review.
- [Review loop](https://github.com/VladimirMarko/conaled/blob/9175737c2b14ef738cfb6c2cdc68d885c0805ddd/docs/agents/review-loop.md)
  requires `review_snapshot.py baseline` or committed `validate` before editing;
  candidate/validate receipts for each reviewed candidate; and `compare` before
  acceptance. The full-spec integration base remains the original pinned master
  through ordinary corrections. Ticket incorporation may change a ticket base,
  with recorded ancestry, without changing that full integration base or erasing
  outstanding findings.
- [Code-review](https://github.com/VladimirMarko/conaled/blob/9175737c2b14ef738cfb6c2cdc68d885c0805ddd/.agents/skills/code-review/SKILL.md)
  retains two independent Standards and Spec subagents. Both assess the same
  full immutable candidate and requirements. The coordinator reconciles rather
  than performing a third review. Missing validation is **Blocked**, never Passed.
- [Example-driven development](https://github.com/VladimirMarko/conaled/blob/9175737c2b14ef738cfb6c2cdc68d885c0805ddd/.agents/skills/example-driven-development/SKILL.md)
  requires independently justified expected mathematics, connection through
  public theorems, meaningful hypotheses, and statement/counterexample checks.
  A computational example alone does not establish a general equivalence.
- [README](https://github.com/VladimirMarko/conaled/blob/9175737c2b14ef738cfb6c2cdc68d885c0805ddd/README.md)
  owns the build/audit modes: `./check.sh --candidate HEAD` in the isolated clean
  candidate, followed immediately before acceptance by
  `./check.sh --verify-candidate HEAD`. Add `--fresh` for its actual triggers,
  including changed tooling/dependencies or suspected stale outputs. A restored
  workspace is not itself a mandate to replay every old environment experiment.

If a compatible pinned environment cannot be established within the checkpoint's
bounded setup budget, record the exact blocker. Missing Nix alone is no longer
a blocker. Do not manufacture a snapshot/check receipt or infer a gate pass from
setup. Read-only planning and explicitly uncompiled mathematical work remain
distinguishable from accepted implementation. Obtain the actual baseline receipt
through the authorized route before claiming the pre-edit gate was met.

## Incoming evidence and its reuse boundary

All paths below are relative to the extracted `conaled-textbooks` checkpoint.
Historical absolute workspace paths and process IDs in those records are inert.

| Project | Evidence inspected | What it establishes historically | What remains for this integration |
|---|---|---|---|
| VFA | `books/vfa/STATE.json`; `records/evidence/reviews/1002-monitor-correction-source-review.md`; `records/evidence/validation/1040-eae9-fresh-output-failure.json` | Both independent axes retained full-scope source analysis at `eae9e110adc7ba1cc28386448a6deef23e406c13`, original base `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`. The import correction preserved previous statements/proofs; a 116-module diagnostic succeeded. | Both axes remained Blocked. The subsequent full fresh attempt exited1 after754 successful modules, while writing module755 failed and ordinary available space was zero. No completed exhaustive audit or success receipt. No accepted chapter. |
| FDSA | `books/fdsa/STATE.json`; `records/evidence/validation/fdsa-control/provenance/chapter03-acceptance-20261105/acceptance.json`; corresponding `tree-shape-acceptance-20261105/acceptance.json` | Chapter3's receipt identifies original whole-task base `2da5708478a1d943a9214b5b386ec2db16cd9eca`, accepted candidate `298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2`, both passed reviews, full incremental check/audit and immediate matching verification. XT02's corresponding receipt identifies accepted `e61bb6f6eaf6fd93b1b072eb3e5563b40f16defe` with both passed axes, a full check/audit and immediate verification. | These are prior-session local acceptances. The new merged dependencies, modules, interfaces and conflict resolutions require current-candidate validation and review. Chapter4 and XT03 remain unaccepted. This assessment did not independently re-audit every earlier Chapter1/2 receipt. |
| PFDS | `books/pfds/STATE.json`; three `records/evidence/reviews/common-integration-*-r1-045.md` reports; `chapter01-integration-r3.json`; `records/evidence/validation/integration-3cf-ordinary-r3-045-checkpoint057-observation.json` | Chapter1 acceptance was introductory accounting only. The common candidate `3cf3de4fbc24c1a144353ae64b13b72f5ead54a5` received two complete source assessments over170 paths, retaining nine original review scopes. Those reports identify0 new static defects,39 canonical historical findings and14 open validation IDs. Eleven-target signed-potential focused checking succeeded. | All nine formal scope outcomes remained Blocked. The latest r3 observation at2026-11-04T02:46:44.680540+00:00 was nonterminal, with497 new completion messages. It is neither a successful full gate nor a proved failed terminal. Chapter2 remains unaccepted and16 forward complexity contracts remain open. |

The PFDS reports document careful matching of unchanged source analyses and
guidance, but explicitly separate that reuse from approval. Their former native
runtime exception applied to their original session; current native authorization
comes from the user's new clarification and matching inputs. Historical chapter dispatch
orders, controller permissions, old process holds and old compulsory command
sequences do not override the user's present integration request and master rules.
Keep useful mathematical dependencies and review provenance; retire obsolete
operational authority explicitly.

Old review outcomes may be reused as outcomes only if base, candidate,
requirements, applicable standards and validation inputs all match. That condition
does not hold for a new merge onto9175737c. Unchanged semantic analysis can inform
the new full-scope review when its identity and surrounding context are checked.
Historical successful builds cannot validate a new combined tree merely because
the imported file bytes match.

## Findings and mathematical boundaries to carry forward

Keep these original IDs in the local review record, with links to the immutable
records. A new integration finding may link to several inherited IDs; it must not
silently replace or close them.

- **VFA:** `ST-002` and `SP-VAL-001` remain open. Preserve the old artifact-incident
  evidence and failed-run classification. Address actual current validation and
  incident obligations under the pinned README/runbook; do not recreate an old
  runtime or combine successful prefixes of different failed runs. `ST-006` was
  fixed on the old candidate and should not be reopened without new evidence.
- **PFDS shared:** `IMPORT-VAL-004`, `CH02-PRE-005`.
- **PFDS paired Standards/Spec validation IDs:**
  `SUSP-STD-VAL-001` / `SUSP-SPEC-VAL-001`;
  `PURE-STD-VAL-001` / `PURE-SPEC-VAL-001`;
  `COUNT-STD-VAL-001` / `COUNT-SPEC-VAL-001`;
  `PERSIST-ACC-STD-VAL-001` / `PERSIST-ACC-SPEC-VAL-001`;
  `BODY-COUNT-STD-VAL-001` / `BODY-COUNT-SPEC-VAL-001`;
  `SIGNED-POT-STD-VAL-001` / `SIGNED-POT-SPEC-VAL-001`.
  The shared2 plus paired12 are fourteen distinct IDs, not sixteen.
- **PFDS retained boundaries:** `SUSP-STAT-001` is the established scoped
  cached-reference type/result counterexample; do not silently assert blanket
  value-type preservation. `PREP-10019-02` separates the pure interpretation
  theorem from the general successful cache-write bound owned by10020. Keep
  distinctions between body attempts, successful writes, address identity,
  persistent history, signed potential and ordinary operational work.
- **FDSA XT03:** `XT03-CP01` and `XT03-DOC01` have source corrections/independent
  source rechecks, with compiler and final receiving confirmation pending. The
  ticket and `tree-fold-resource-requirements.md` identify original base
  `64c6b777d828ecfe83234fc2aed94600a1f24297`, donor
  `b0fce71fa00b2ff6250b09002176bdc75baf1f46`, seven paths and88 public names. Do not
  treat historical XT02 ordering as a mathematical prerequisite for XT03.
- **FDSA Chapter4:** preserve original whole-chapter base
  `298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2`, all three draft streams and their
 76 obligations/11 exercises. Latest accepted-main alone does not contain all
  useful prepared work.

The complete PFDS39-ID register and aliases already live in
`books/pfds/records/evidence/reviews/common-integration-coordinator-r1-045.md`,
section5. Link it instead of copying another whole inventory.

## Current ADWH follow-up: useful lessons, superseded work

The deciding criteria in [#458](https://github.com/VladimirMarko/conaled/issues/458)
are useful built mathematics, corrected textbook coverage, and usefulness to
conaled. Checkpoints are evidence, not the mathematical specification. The audit
requires dispositions for named declarations, anonymous examples, contexts and
corrections: retained, generalized with checked specialization, replaced with
proved correspondence, corrected, or explicitly owned remaining work. Preserve
domains, hypotheses, quantifier order, computational witnesses, partiality,
ordered occurrences/ties, arbitrary initial states, pricing, demand and uniformity.
Inspect actual elaborated types where coercions can hide a change. Erasure of
observations does not preserve a richer contract.

#458 is **closed**, accepted at924542a1. Its
[completion comment](https://github.com/VladimirMarko/conaled/issues/458#issuecomment-6802827095)
explicitly limits the audit to selected recovered source and official-code
correspondence: absent printed chapters prevented new whole-book certification.
Do not repeat this completed audit wholesale or revive Timing/Amortized as an
unmet prerequisite.

Current [#459](https://github.com/VladimirMarko/conaled/issues/459) remains open,
but its current body supersedes many older comments:

| Selected family | Current issue disposition |
|---|---|
| R1 list/concatenation costs | Accounted for by468/469 and stronger existing exact head/reverse contracts. |
| R3 trim/prune | Accounted for by470–472, preserving independent specifications and arbitrary-price/native-potential boundaries. |
| R4 dynamic arrays | Accounted for by508's two actual policies, ordered observations, repricing and raw-state bounds. |
| R5 digit search/averages | Accounted for by478's actual first-hit execution and corrected finite mean including failures. |
| R6 counter geometry/output | Accounted for by479/505, including23 tokens and7 writes in the five-state fixture;24 units is a different tariff. |
| R2 demand/deferred append | Open:535 resumable head-of-concatenation;536 deferred append histories, depending on535. |
| R7 permutation costs | Partly delivered by506/507/510;527 owns remaining recursive insertion generation/costs. |

These are observed issue dispositions, not a substitute for verifying source
presence/ancestry at our pinned9175737c. Later issue edits must not silently move
our integration pin. The architectural investigations473–477 produced assessed
proposals, not automatic adoption of a new common framework. Prefer demonstrated
existing owners and real consumers; do not add a general heap evaluator merely
because the books discuss laziness or persistence.

[Issue149](https://github.com/VladimirMarko/conaled/issues/149) remains open for
the broader reconstruction, source-page/provenance and separate queens/kernel
scope. The old weekly-budget rules, publication instructions and process-stop
comments were for earlier orchestration sessions. They grant no current remote
write permission and are not new stop conditions for this local integration.

## Proposed local acceptance record

Use one full-scope local integration issue, with small child records only where
useful. It should retain the complete current user request, pin9175737c, incoming
checkpoint hash, source ref registry, original full-spec base, candidate history,
subscope relationships, preserved inherited findings, and two review axes.
Requirements for completion:

1. **Preservation:** all incoming useful Lean/paper work is either integrated,
   replaced through an explained checked relationship, corrected with retained
   evidence, or explicitly preserved as owned pending work. No arbitrary source
   exclusions or acceptance relabeling to make the merge look complete.
2. **Architecture:** inspect actual existing operations, semantic contracts,
   representations, observations and law-transport facilities before selecting
   seams. State precisely which equivalent specifications/implementations can be
   interchanged and under which hypotheses. Preserve ordinary Lean clients.
3. **Connected mathematics:** new bridges have statement review and meaningful
   consumers using their public results. Include discriminating empty/failure,
   duplicate/order, initial-state, price, sharing and demand cases where the
   proposed relationship depends on them. Value equality alone grants no cost,
   allocation, physical identity or termination equivalence.
4. **Repository integration:** public imports, module coverage, pinned dependency
   configuration and exhaustive axiom auditing remain coherent. Preserve current
   master guidance rather than overwriting it with old branch versions.
5. **Exact acceptance:** candidate snapshot receipts, applicable actual build and
   audit, separate complete Standards/Spec outcomes with0 unresolved findings,
   immediate verify-candidate and final content comparison all identify the same
   approved result. A validation blocker leaves completion pending.
6. **Durability:** pause writers, capture all useful changes and local records,
   verify self-contained restoration, then observe successful owner-root
   `create_library_file`. Save milestones before another extended phase. Missing
   inputs after a wipe require the latest archive; an upload failure requires
   prompt report and a stop. Local captures and Git refs alone are not durability.

This can establish integration of the supplied progress without claiming that
the three entire books are complete. Full absent manuscripts remain necessary
for new source-page audits, with provenance limitations carried explicitly.

## Retrieval identity

Live issue body/comments fetched through the GitHub connector on2026-11-13,
read completely; no remote mutations. Compact identity avoids another raw dump.
Body hashes are SHA256 of UTF-8 body text. Comment hashes are SHA256 of Python
`json.dumps([{id, body}, ...], sort_keys=True, separators=(',', ':'))` in returned
order (default ASCII escaping).

| Issue | Body updated | Comments read | Body SHA256 | Comment-set SHA256 |
|---|---|---:|---|---|
|149|2026-11-11T20:29:07Z|26|`0fb11e61890e128e754977e8670eff2df2926a6a5ce511970918bd54c0348783`|`da2bedd063868d4f3a43bb3de75d8b9752d30e42358dca1a9308982bc8ff1366`|
|458|2026-11-11T17:34:48Z|1|`aea7187c1040cd548aad89861acb5206c4fc26683baf94e000983c228d5fe79d`|`d351a30528844d894078888a7554867eb3f3049163fef1b63504a13c2e55ded6`|
|459|2026-11-13T13:38:04Z|12|`a9d5bcc825d60d110ca05b427fbe51982fd71ca44c0a21c806f88cd87a5f65cc`|`70d386cde2b5d70ff296c6d9c29066dbd1bb9a1da413d911d8c01eba2d9fef1d`|

No formal acceptance, new mathematical conclusion, or durable upload is asserted
by this report. The coordinator owns inclusion in the next verified saved checkpoint.

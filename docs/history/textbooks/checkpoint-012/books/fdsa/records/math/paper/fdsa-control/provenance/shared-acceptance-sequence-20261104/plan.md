# Chapter 2 shared acceptance sequence — read-only plan

Prepared 4 November 2026 by `/root/shared_acceptance_sequence` for the existing
implementation/review loop. This plan performs no integration, validation,
source review approval, ticket closure or acceptance. Only this plan and its
receipt are new files. Source worktrees, refs, outputs and earlier records are
untouched. HOLD is active after this write for checkpoint 0094.

## Fixed starting point

Accepted Chapter 1 is R=`07e480f6ec9958d4975bb90151005b84f2907614`.
The first outstanding acceptance remains exact foundation
F=`f17cc6b1a2bf44215b16202ed0fcee2b5c130761`, containing only its recorded original
foundation prefix plus accepted R and recorded corrections. Do not substitute
XP01 or a later shared prefix. The parent reported its full check live; this
agent did not poll any inherited execution session or inspect its outputs.

Current development C=`5398db774ed5ca9938d0562e379d757323e7a355` is the parent's
immutable focused-check candidate. It is a source/evidence comparison point,
not an accepted tip. Do not change either live tree. Existing focused/type
results may be retained only through matching source, dependency, configuration
and execution-profile evidence; this plan grants no validation credit.

## Exact minimal source scopes

All corrected tips below are actual ancestors of C. Every unit-owned Lean or
source-note file—24 paths in total—is byte-identical between its corrected tip
and C. The shared `SquareApplications.lean` and reconstruction map differ as
expected from cumulative integration. `receipt.json` contains every path, Git
blob, byte count and SHA-256, all requirement hashes, and exact commit histories.

| Unit | Original review base | Original candidate | Corrected minimal source tip | Full unit paths |
| --- | --- | --- | --- | ---: |
| XM01 | `07e480f6ec9958d4975bb90151005b84f2907614` | `5f409e71bb068e3b8cc133226046ce8bbe29d982` | `72a0951aee406f7db67998d2a3bf8810f4e1bccc` | 6 |
| XD01 | `a14977b9e316cc484ffad8a470d26b15615956c0` | `ffeaf8aed84184f49a13acb5c84e1fd608c9b7e8` | `52722e3ee481167e99b8f6c0b2417df7fb7615d8` | 5 |
| XQ01 | `07e480f6ec9958d4975bb90151005b84f2907614` | `de5410286bbefd841dff50bef55c2e52d2ebbd2a` | `0612e80a0c297a38fa1add6e837dc7781e1bbd9c` | 7 |
| XU01 | `a14977b9e316cc484ffad8a470d26b15615956c0` | `ff3dd88082c6283df40bcd86a4363841a0360b12` | `f00078bb2dbf1b8dc8d186d9728c9678f46a96b0` | 6 |
| XU02 | `ff3dd88082c6283df40bcd86a4363841a0360b12` | `4bb13e44a6c7e3277b69cbac9fd9dd37cd7780f8` | `bdac9703aab4b383fa775568d36bf685af329389` | 6 |
| XU03 | `4bb13e44a6c7e3277b69cbac9fd9dd37cd7780f8` | `a0597381f02eddd074ee96cabaa974f2062285f8` | `ee2ea2406a014e43c355f93317455f27b90dd680` | 6 |

The required sources and cases remain:

- **XM01:** additive `Applications/Sorting/Merge.lean` value laws,
  `Applications/Resources/ListMerge.lean`, `Examples/MergeCosts.lean`, its source
  note, public import and map. Keep the actual selected-branch dual observation,
  raw empty/unsorted domains, arbitrary-relation converse, independent-universe
  input-local map transport, actual two-merge bind, and merge-only raw queue body.
- **XD01:** DifferenceListCosts core and examples, source note, import and map.
  Keep separate Rep/AppCost predicates, actual value-dependent invocation,
  creation/applying tariffs, arbitrary suffix/seed, ordinary DList bridge,
  repeated materialization and linear/exponential empty-prefix histories.
- **XQ01:** Sequences/Partition, Resources/Partition, Selection/ThreeWay,
  ThreeWayPartition examples, source note, import and map. Keep all eight old
  Selection names/signatures, the unchanged Selection-specific remainder and
  existing consumers; distinguish the old two-pass value operation from the
  actual one-tail-recursion measured program and nil-inclusive `length+1` law.
- **XU01:** PermutationMinimum core, main and boundary examples, source note,
  import and map. Keep the original global permutation, member-qualified event,
  injective priority domain, overlapping common-sample cases and empty/tie/
  outsider boundaries. It supplies no conditional or algorithm law by itself.
- **XU02:** PermutationOrder core, main and boundary examples, source note,
  import and map. Keep inverse orientation, completeness/Nodup support,
  deterministic nested filtering, whole-output law, separate measurable
  hypotheses and orientation/invalid-enumeration boundaries.
- **XU03:** PermutationTail core, main and boundary examples, source note,
  import and map. Keep the generic current-measure HasLaw route, actual optional
  head/tail, a.e. versus pointwise distinctions, fixed-subset containment,
  changed-environment reuse, null conditioning and the 1/3-versus-2/3 boundary.

## Proposed sequence after F actually passes

A concrete small sequence is **F acceptance → XM01 acceptance → XD01 acceptance
→ XQ01 acceptance → XU01 acceptance → XU02 acceptance → XU03 acceptance → full
Chapter 2 acceptance**. The order of XM01/XD01/XQ01 relative to one another is
an implementation choice, not a newly invented prerequisite. Their scopes are
independent after the accepted Chapter 1/foundation sequence. The XU01→XU02→XU03
acceptance order is explicit in the frozen tickets and requirements and must
not be collapsed into a single unchecked chain merge.

At each arrow:

1. Root first secures the actual closed previous command, full outer/native
   logs, actual exit, audit and matching verification record. Preserve that
   record outside the next active `.lake/verification.json`. Establish that
   the checkout is idle using root's owned process evidence.
2. After the preceding candidate's complete acceptance, record its exact tip
   as the new incorporated integration base for this shared unit. Retain the
   original base, entire unit scope, requirements, prior findings and source
   assessments. The complete Chapter 2 review still keeps R as its full base.
3. In the same now-idle qualified acceptance worktree, construct a new clean
   candidate by a history-preserving merge of the exact corrected minimal tip.
   Preserve all refs/history. No rebase, reset or cherry-pick is needed. Compare
   the resulting tree against both the accepted base and the entire intended
   original unit scope; record every reconciliation. Do not merge a cumulative
   later C2 branch as a shortcut to a smaller shared candidate.
4. Preserve the complete import and documentation union; apply the bounded
   public-status reconciliation below before freezing the new candidate. Keep
   all inherited Lean corrections and all required boundary modules. Record
   exact source/dependency/configuration identities for any retained evidence.
5. Supply the applicable focused evidence, all missing actual statement
   inspection evidence, and the normal full `./check.sh --candidate HEAD`
   through the qualified native kit, `--threads 1`. The full command retains
   clean candidate/dependency checks, coverage and source policy, both integrity
   phases, complete build, exhaustive audit and its new exact verification
   record. Source-only changes do not themselves trigger fresh mode; apply any
   real README/runbook trigger if one arises. Keep normal outputs in place;
   never transplant artifacts/traces from another tree.
6. Continue both independent Standards and Spec axes on this complete scope
   and exact candidate, retaining matching previous source analysis explicitly.
   Assess all new resolutions, status edits, types, compatibility and actual
   terminal evidence. Source findings zero is not an overall Pass.
7. Only after both axes and every gate pass, run qualified
   `./check.sh --verify-candidate HEAD` immediately before exact accepted local
   fast-forward; update local tickets/coverage and save/upload/expose the
   standalone acceptance checkpoint. No GitHub mutation or push.

No compiler/check/cache process was started by this plan. Parent-owned live
commands remain the only builders. Later stages keep the qualified execution
profile and private writable dependency/project outputs; this sequence proposes
no new installation, concurrency or performance change.

### Why ordinary merges preserve the required corrections

XM01 and XQ01 fork R. XD01 and XU01 fork a149, an ancestor of accepted R/F.
They change only their listed unit paths, with common root/map overlap. A
whole old root/map must never replace the accepted versions.

XU02's minimal branch still inherits the original ff3dd minimum files; XU03's
minimal branch still inherits the original 4bb order files. They do **not**
contain the later minimum/order proof corrections themselves. Merge them into
the already accepted corrected predecessors and retain those predecessor bytes.
Their own per-unit deltas from the original bases touch only their six paths.
A direct checkout/copy of their complete trees would regress accepted source.
No merge or merge simulation was executed, so this is inspected ancestry and
scope evidence, not a claim that Git has reported a conflict-free merge.

After accepting these new integration commits, the accepted tip will not be
an ancestor of current C merely because all minimal source tips already are.
Therefore C cannot simply become the accepted tip by a later fast-forward.
Prefer merging the completed C2 development history into the idle qualified
acceptance worktree after XU03 acceptance, yielding a **new exact C2 candidate**.
Alternatively incorporate the accepted tip into an idle C2 successor explicitly.
Preserve the shared accepted changes and all 112 C2 obligations, reconcile the
root/map, continue the original R-based full review, and run its full gates.
No already-approved record is copied onto that new candidate.

## Public imports and documentation

Each shared unit already adds exactly one necessary public import:
`Examples.MergeCosts`, `Examples.DifferenceListCosts`,
`Examples.ThreeWayPartition`, `Examples.PermutationMinimum`,
`Examples.PermutationOrder`, or `Examples.PermutationTail`.
All three probability main example modules already import their own boundary
module; Order's boundary imports Minimum's main, and Tail imports Order.
Preserving these imports keeps the complete cases in public closure.

`ProofAudit.lean` line 1 already imports `SquareApplications`; its documented
exhaustive module ownership includes private/generated declarations. No direct
new imports into ProofAudit or checker/pin changes are required. Retain all
prior public imports. Do not copy the complete C2 public root into an earlier
shared candidate, where its remaining C2 modules are intentionally absent.

The six original map diffs were read completely. They preserve mathematical
boundaries but contain historical draft/uncompiled labels. The unit notes are
byte-identical to their minimal tips and retain related present-tense labels.
This is a concrete **public-status reconciliation**, separate from mathematical
correctness and from pending acceptance. Exact checked excerpts are in the
receipt. Locations include:

| Source note | Current status wording requiring dated framing |
| --- | --- |
| `fdsa-list-merge.md` | Lines 6–8: compilation, full gate and final reviews stated pending. |
| `fdsa-difference-list-costs.md` | Lines 208–213: old compiler exclusivity history followed by present-tense elaboration/gate needs. |
| `fdsa-three-way-partition.md` | Lines 6–8: uncompiled/unaccepted; lines 201–207: originally unaccepted C1 base and gate requirements. |
| `fdsa-permutation-minimum.md` | Lines 3–7: not yet compiled or accepted. |
| `fdsa-permutation-order.md` | Lines 3–5 and 138–139: not compiled/accepted; examples remain uncompiled. |
| `fdsa-permutation-tail.md` | Lines 3–7 and 165–167: not compiled/accepted; all proofs remain uncompiled. |

Before each immutable acceptance check, frame original development status
explicitly by date/source candidate and record the actual already-secured
focused/type evidence and lineage as historical facts. Preserve original bytes
in provenance. Keep all mathematics, scope boundaries and notices unchanged.
Do not preclaim future acceptance, and avoid replacing the old claim with a new
undated 'pending' sentence that would itself demand a post-acceptance source
commit. Final acceptance evidence belongs in the actual immutable candidate's
local records. Both axes must assess the exact documentary delta.

## Retained review and type evidence

XM01's existing full six-path loop is `reviews/ordinary-merge-round1.md`, with
separate `ordinary-merge-standards.md` and `ordinary-merge-spec.md`. The original
source assessments have zero unresolved findings and overall Blocked outcomes.
Keep DOC01/02/03 and ELAB-001/002 dispositions. Its earlier 17-name type output
covers only the selected set; the independently inventoried 78 additional
public names still need actual evidence. Do not repeat the old full-file claim.

XD01 retains `difference-list-cost-candidate.md`, both independent
`difference-list-costs-{standards,spec}.md` reports and its provenance erratum.
XQ01 retains `three-way-partition-candidate.md`, frozen requirements and the
complete `partition-shared-integration-addendum.md`. Minimum/Order/Tail retain
their original candidate/requirements/start records. Their incorporated bases
may advance as allowed by the review procedure; their full task scopes and
all findings remain. C2's existing independent source analysis can be retained
only with exact identities and an explicit continuation for the new candidate.

Parent's current complete accounting distinguishes actual old evidence from
prepared-only programs: XD01 72, XQ01 48 and XU01 37 named types have retained
secured evidence; XU02 53 and XU03 61 are among the missing actual inspections.
These figures are evidence-navigation facts from the parent's completed
inventory, not an independent re-reading of those type logs by this planning
agent. The 793-name program and separate F145 program are prepared, not passes.
No C02-TYPE-001 disposition closes through this plan or inventory alone.

Focused scope, where renewed evidence is actually needed, is XM01's three
Merge/ListMerge/MergeCosts modules; XD01's core/examples; XQ01's shared core,
resource and examples plus Selection.ThreeWay, Selection.Consumers and
Examples.RankSelection; and each included probability core/main/boundary triple.
Reuse matching successful prior focused evidence without unnecessary repeats;
never omit the new exact candidate's applicable complete check/audit.

## Inspection boundary

This is a completed integration-planning investigation, **not another final
mathematical source review**. Complete reads cover the governing request,
checkpoint0093 CURRENT/STATUS/ticket index as observed, all six unit tickets,
AGENTS, applicable implementation/statement/review instructions, README124–307,
architectural/domain guidance and relevant ADRs, all six frozen requirements,
all205 lines of shared-integration-preflight, the whole XM01 round record and
XQ01 integration addendum. Complete unit root/map diffs, exact read-only Git
ancestry/scope identities and import lines were checked. The unit notes were
inspected only in the stated status contexts; previous complete source/review
assessments are referenced rather than represented as re-read here. No original
book/theory/full Lean proof assessment or actual type/audit re-reading is claimed.

All proposed actions remain conditional on the real preceding acceptance and
matching evidence. Source and status edits, merge conflict resolution, new
candidate validation and final independent outcomes are future work for root's
existing loop. This plan changes no permission, requirement or gate.

## Post-checkpoint 0094 clarification: a combined independent-unit candidate

Appended after root reported checkpoint 0094 verified, uploaded and exposed,
and explicitly released this plan's write HOLD. This is a read-only planning
interpretation for root's decision; it creates no permission, source change,
acceptance, mathematical review or validation result. The entire original
238-line plan is preserved byte-for-byte above. Its serial sequence remains a
valid option, not a requirement that the first four independent units receive
different candidate SHAs or four separate full-check invocations.

### Controlling passages and the distinction they establish

The complete relevant instruction and requirement files were read during the
original investigation. The following exact passages were re-read for this
clarification. The receipt saves their full text, line boundaries and SHA-256.

- `reviews/shared-integration-preflight.md`, lines 198–200, requires the accepted
  incorporated base and original component bases/requirements to be retained,
  carries every unresolved finding forward, and states:

  > Both independent final axes must assess the complete included scope on the
  > same combined candidate, including resolution edits and consequential
  > compatibility.

  It also permits retaining unchanged prior analysis with explicit identity
  evidence and rejects focused success, ancestry or preflight as substitutes
  for full-candidate evidence. The passage supplies the general combined-scope
  integration framework; it does not expressly name this particular four-unit
  combination.
- `docs/agents/review-loop.md`, lines 69–92, requires isolated matching candidate
  validation, preservation of the real success record, both review axes and
  immediate `./check.sh --verify-candidate HEAD`. It requires matching relevant
  inputs for evidence reuse. It does not prescribe a separate invocation for
  each local ticket.
- `reviews/ordinary-merge-requirements.md`, lines 328–346, explicitly leaves
  XM01 out of the first foundation candidate, requires that prefix's own gates
  first, and then requires XM01's complete matching focused/full/review/immediate
  gates while preserving the original scope and accepted predecessor changes.
- `reviews/difference-list-cost-requirements.md`, lines 121–129, requires the
  exact model's statement review and pinned focused/public/full/review/immediate
  gates. `reviews/three-way-partition-requirements.md`, lines 198–209, requires
  the complete compatibility scope, candidate check/audit, both full-scope axes
  and immediate verification. Neither adds acceptance of another of these four
  independent units as a prerequisite.
- `reviews/permutation-minimum-requirements.md`, lines 145–154, requires its
  own complete gates and repaired Chapter 1 acceptance. Its final sentence is:

  > Integrate only after repaired Chapter 1 and this unit have both passed
  > their gates.

- The sequential probability requirements are explicit and different.
  `reviews/permutation-order-requirements.md`, lines 208–209, says:

  > Integration depends on acceptance of the repaired Chapter 1 and prior
  > minimum-law base as well as this unit's own gates.

  `reviews/permutation-tail-requirements.md`, lines 228–229, requires the repaired
  Chapter 1 and preceding shared-base acceptance. The retained preflight,
  lines 129–133, lists XU01, then XU02 after XU01 acceptance, then XU03 after its
  preceding base acceptance, and states:

  > Each ticket's explicit acceptance prerequisite remains in force. An eventual
  > merge of an entire saved chain is not a shortcut around those gates.

### Planning inference and its limits

I found no requirement that XM01, XD01, XQ01 and XU01 have four different
immutable candidates or four separate full-check invocations. In view of the
explicit combined-scope framework and the absence of acceptance edges among
these four units, **one declared combined candidate after exact F acceptance
is consistent with the controlling provisions**, provided it supplies every
unit's complete matching gates. This is an interpretation of those provisions,
not an explicit instruction naming this batch and not a waiver. Root will read
the cited requirements directly and decide the assembly before acting.

A combined route would be:

**Exact F acceptance → combined XM01/XD01/XQ01/XU01 acceptance → XU02 acceptance
→ XU03 acceptance → complete Chapter 2 acceptance.**

The four-unit combination does not include XU02, XU03 or the whole current C2
development tree. F itself must still pass at the exact already recorded
candidate first. No XP01 or later unrelated shared draft enters this sequence.

If root selects the combined route, record its complete declared scope before
assembly. Preserve each original unit's requirement, starting base, commit
history and finding record. Record accepted F as the incorporated base and the
actual new immutable candidate in each continuation. Both independent axes
must explicitly cover all four original scopes, all integration/status edits,
all relevant dependencies and every unresolved finding on that same candidate.
Existing complete source analysis can be retained with exact identities; old
source assessments do not become final approvals automatically.

One successful actual full candidate check/audit and matching verification
record can then supply the common build/audit evidence for all four units.
This does not dispense with any unit's applicable focused compatibility,
actual public-type/statement inspection, source-policy or example requirements.
Preserve each required evidence connection explicitly, with no artifact or
trace transplantation. The usual actual closed logs, exit, audit details and
matching immutable identities remain mandatory. A failed or unresolved unit
blocks the **entire combined promotion**; no partial acceptance follows from
that one candidate. After both axes and every gate pass, perform immediate
qualified verification before exact local fast-forward and the acceptance
checkpoint. No fresh-mode or concurrency policy changes are proposed.

XU02 must still begin its acceptance integration after this accepted minimum-law
base exists. XU03 follows accepted XU02. The explicit predecessor acceptance
edges cannot be discharged by validating all three unaccepted probability
stages together. Future final C2 integration still requires a new candidate
containing the accepted integration history and keeps the original R-based
complete 112-obligation review.

### Preserved public-status contexts

The ten exact source-note contexts already inventoried remain unchanged in
`receipt.json` under `public_status_excerpts`, with candidate, full file hash,
path, line boundaries and literal text. They were re-read in full as excerpts
and checked again against immutable C=`5398db774ed5ca9938d0562e379d757323e7a355`.
This adds no complete-note or mathematical source-review claim. The original
note assessment boundary remains explicit.

Retain the proposed dated historical framing: preserve original development
status and actual secured evidence/lineage as dated facts, with mathematical
prose and notices unchanged. Do not conflate focused passes with acceptance,
preclaim a future gate, or introduce a new undated status that would require
another source commit immediately after acceptance. Root's source changes,
if any, remain future work in the existing full-scope review loop.

HOLD resumes after this append and its receipt update. No source, ref, output,
other control file, original requirement or review record was edited.

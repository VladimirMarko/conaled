# FDSA-XB01 — Shared list call counts from Appendix B.1

State: Appendix B.1 accepted and integrated at f17cc6b; acceptance checkpoint saved/uploaded.
Triage: ready-for-agent. Parents: FDSA-000, FDSA-APP-B.

Source: pinned July 27, 2026 PDF, printed pp.347–348, Appendix B.1;
coverage items B-002 through B-015 in `research/appendix-b-obligations.md`.
These list primitives are shared by sorting, selection, tree construction,
dynamic programming and later data structures. This is the user's cross-cutting
exception, not activation or acceptance of a later sequential chapter.

Development starts from the clean shared foundation candidate
`333f900d04be3153518e68cc8c10920f40a08e05`, branch
`work/fdsa-list-foundations`, worktree `conaled-insertion-costs`.
Combined foundation review base remains fixed at
`1aabd512284fe86254278ac631eda061d311050b`, including the exact FDSA-X002 and
FDSA-APP-A requirements. Root coordinates public imports, documentation,
candidate commits, complete validation, independent review and checkpoints.

## Required outcomes

- Reuse measured append and length with their exact source counts `n+1`.
  Do not add duplicate algorithms or transfer runtime costs from standard values.
- Implement measured callback map and Boolean filter through the existing
  `Measured`, `bind`, `pure`, and `CallCount` vocabulary. Empty costs 1;
  each cons pays its callback observation, its recursive-tail count, and 1.
  Preserve the actual callback value in the resulting map/filter branch.
- Prove erasure to standard `List.map`/`List.filter`, the exact recurrences,
  and exact cost `(xs.map callbackCost).sum + xs.length + 1`.
  Occurrences, including duplicates, each pay their own callback count. Both
  filter keep/discard branches traverse the remainder and pay equally.
  Keep Knapsack's existing +2 tariff unchanged; it is a different model.
- Supply measured take and drop adapters over the existing `splitRun`, proving
  each displayed recurrence, erasure and exact `min k length+1` count. A caller
  executing separate take and drop must add both counts, even though fused
  split can return both values for one traversal.
- Supply sequential measured list lookup with explicit optional failure.
  Preserve its zero/successor source recurrences on nonempty inputs and prove
  value erasure to zero-based `getElem?`. On `k<length`, prove exact count `k+1`.
  Any chosen invalid-input count must be identified as an extension, not a
  source theorem. No `Inhabited` payload or random-access execution shortcut.
- Retain minimal operation hypotheses, arbitrary payload universes and
  meaningful checked examples/statement review. Integrate public coverage.
  No admission, extra axiom or native-evaluation shortcut is acceptable.

## Independently calculated cases

- Callback `(x+10,x)` on `[2,2,3]` maps to `[12,12,13]`, with count
  `2+2+3+3+1=11`.
- Predicate callback `(x≤2,x)` on the same input filters to `[2,2]` with the
  same count 11. A discarded occurrence still pays its predicate work.
- Zero-cost callbacks on length three cost 4; unit-cost callbacks cost 7.
- Sequential lookup of position 2 in `[4,4,9]` returns 9 and costs 3.
  Optional failure on `[] : List Empty` needs no default payload.
- Taking/dropping 2 from `[1,2,3]` returns `[1,2]`/`[3]`, with separate counts
  3 and 3. Their sequential composition costs 6, while fused split costs 3.
  Zero counts, empty lists and overlarge counts remain covered.

## Completion gates

- [x] Required recurrences, values and exact properties implemented.
- [x] Connected examples and per-claim statement review retained.
- [x] Focused builds pass.
- [x] Complete immutable-candidate verification and proof audit pass.
- [x] Both independent review axes have no unresolved findings.
- [x] Prerequisite Chapter1 accepted; final candidate identity verified;
      integration and acceptance recorded, checkpoint saved/uploaded.

This ticket does not complete Appendix B as a whole; the remaining subsections
are tied to their corresponding chapter algorithms and invariants.

## Development record

- Root implemented the shared measured list primitives and connected cases in
  `Applications/Resources/ListCalls.lean` and `Examples/ListCalls.lean`, with
  public import and source/statement-review mapping.
- Exact requirements were frozen before editing in
  `reviews/list-calls-requirements.md`. The independent bounded preflight is
  `research/list-calls-preflight.md`; it is not acceptance review.
- Its discarded-head filter and first-invalid lookup suggestions are retained.
- Focused core build is running in the pinned shell with `LEAN_NUM_THREADS=1`;
  log `reviews/list-calls-core.log`. No success or acceptance is inferred yet.

Draft durability candidate: `df116c2f6d834eeb952157505b5c93a9ab5497e8`.
Focused core build and example build are not yet passed; checkpoint capture
is preservation, not acceptance.

The secondary compiler was paused after direct observation of severe file
paging so the primary Chapter1 check can proceed alone. See
`provenance/active-build-observation.json` and `secondary-build-pause.json`.
Resume only after checking the saved process identity; this is not a build
failure, timeout or acceptance result.

The paused duplicate build was subsequently terminated after exact process
identity checks. Root session66704 returned143; the new ListCalls module had
not compiled, so this is neither a proof failure nor a successful check. See
`provenance/secondary-build-stop.json`, including completed child cleanup. Do
not resume the old PID. After Chapter1 acceptance, reuse its idle validation
checkout/cache for the shared candidate and continue focused validation there.


## Accepted foundation continuation — 4 November 2026

Accepted and integrated locally at `f17cc6b1a2bf44215b16202ed0fcee2b5c130761`, from accepted Chapter1 base `07e480f6ec9958d4975bb90151005b84f2907614`. The original four-unit/nine-path scope and prefix c80eec92 are unchanged. The recovered full normal candidate check and exhaustive audit passed (967 checked project modules;45,294 kernel-safe declarations,25,117 theorems; only propext,Classical.choice,Quot.sound). These are whole-project counts. All145 actual public types were fully assessed by both independent axes with matching before/after inputs. Standards and Spec both passed with zero unresolved findings; FDN-ELAB-001/002 are resolved.

Qualified immediate `./check.sh --verify-candidate HEAD` passed at exactF before the local fast-forward at13:55:30UTC. The unrelated baseline file, tracked/index state and accepted Chapter1 history were preserved. No GitHub mutation or push occurred. The authoritative evidence and exact hashes are in `provenance/foundation-acceptance-20261104/acceptance.json`, with full/145/final-review/immediate/fast-forward records. Earlier development paragraphs above are historical, including interrupted or unknown-terminal attempts; their outcomes are not rewritten.

Acceptance checkpoint creation/upload is the remaining durability action; the combined checkpoint checkbox stays pending until that upload actually succeeds. No Chapter2, Chapter3 or other shared-unit acceptance follows automatically.

Accepted inventory coverage is B-002 through B-015: all seven B.1 recurrences and seven properties. B-001 remains the cross-cutting convention; B-016–060 and whole-AppendixB acceptance remain open.


Durability completed 2026-11-04T14:08:43.703250+00:00: verified/uploaded checkpoint0109,22,290,443bytes,SHA949b1525e093857799316ea33e22f82cec9056abbd2ef393a1fa8657b04a1e08,libfile_84959da777948191832d2e322bf6fb16. The earlier pending-upload wording records the capture boundary. See provenance/foundation-acceptance-20261104/durability.json.

# FDSA-XL01 — Shared logarithm bounds

Status: **clean committed five-path draft a601ad713368daf8e18d5a5537a83d47138491fa;
full author/root source assessments complete; checkpoint0063 saved and inspected**.
Original base07e480f; uncompiled and unaccepted. Chapter1 remains active.

## Original report-only investigation

The retained companion Lemmas_log.thy (1,768 bytes /55 lines, SHA-256
`efac8b7ffdbdad1cdc9a825475d9a0ac9558025a092fcfd02f6b8881e2be8d41`)
contains four Real logarithm inequalities. Actual imports occur in the splay
analysis base and multiple pairing-heap analyses. The skew analysis also has
an explicit positive-input, base-greater-than-one logarithm-sum bound. Determine
the exact source uses and whether any missing bounded common fact belongs in
a small shared unit or should be consumed directly from the existing library.

Start with the actual pinned sources, existing inventories and Lean APIs.
Do not assume all source helper names need new wrappers or that all algorithm
potentials coincide. Keep sharp/strict constants, positive versus nonnegative
domains, shifted arguments, Nat-to-Real casts and totalized log behavior exact.
Distinguish pure inequalities from actual operation costs, invariant-local
potential nonnegativity, sequence telescoping and amortized algorithm claims.
Existing XP01 accounting and tree/shape observations must be reused where
appropriate; their unaccepted state is not changed by this investigation.

The three assigned planning reports are:

- research/logarithm-bounds-source-preflight.md: source statements, actual
  consumers, obligation IDs, provenance/license and chapter boundaries.
- research/logarithm-bounds-api-preflight.md: exact pinned interfaces, minimum
  assumptions, proof routes and smallest justified reuse or extension.
- research/logarithm-bounds-case-preflight.md: independently calculated
  connected uses and domain/constant/totalization counterexamples.

Authors may write only their own report. No Lean/source, prior report or
inventory edits; Git ref/index/worktree changes; compiler/checker/project hash
helper; active output inspection; cache/performance action; or final-review
loop is released. C1 attempt3 remains the sole validator. Complete stopped
reports and root assessment precede any source decision. The initial Chapter2
prefix remains c80eec92f5458eccfd1c34c8314d666c2a1e3847 after repaired C1
acceptance. Preserve all original book obligations, findings and earlier
failed/unknown outcomes. No chapter, appendix or shared unit is accepted.

## Frozen source decision — 2026-11-03

All three final reports stopped and were fully read by root, including the
source report's sole namespace correction and all final case deltas. The
assessment is reviews/logarithm-bounds-preflight-assessment.md. The original
report snapshots and corrections remain under provenance/ and reviews/.

The frozen requirements are reviews/logarithm-bounds-requirements.md,
12,432 bytes /213 lines, SHA-256
`d77627f36996722dd938ed6ff5d15d396ff045bf969e43115a7402a95dd2780d`.
The public core has only the sharp base2 logarithm sum inequality and its
strict +1 corollary. Five paths cover that arithmetic module, meaningful
canonical-tree/pairing scalar cases and direct library clients, the source
note/map and public example import. No XP01 or shared-tree draft dependency,
algorithm, resource framework or later chapter activation is selected.

The original source/review base is
`07e480f6ec9958d4975bb90151005b84f2907614`, in the clean source-only checkout
conaled-logarithm-bounds on work/fdsa-logarithm-bounds. The starting record
reviews/logarithm-bounds-start.json captures25 existing source/policy/config
identities, the absent alternative lakefile.lean and three absent new paths,
the pinned package-source link, absent project build and unchanged main/C1
source states. Main's unrelated pre-existing artifact remains protected.

All three authors read the complete freeze/inputs and stopped at readiness;
see reviews/logarithm-bounds-readiness.md. Root must first
create/expose/save the pre-code checkpoint and recheck the exact starting
state before a separate disjoint source release. All later acceptance gates,
original chapter obligations, C1's sole validator and exact initial C2 prefix
remain unchanged.

## Separate source release — 2026-11-03

Checkpoint0062 was immediately exposed and saved successfully as
libfile_95ea6e348d80819193de7cf3d1db2c9d. Root read the full180-line bounded
inspection: all625 payload checksums match; all51 previous refs remain;
the new branch/worktree add exactly two original07e480f refs. Its own save
receipt and content inspection postdate that archive and enter the next one.

At02:02:33.415566 UTC, root immediately rechecked the exact clean base, all25
existing baseline identities, absent alternative lakefile.lean/three new
paths/project build, frozen inputs and unchanged main/C1 source, then recorded
reviews/logarithm-bounds-release.json (1,690 bytes, SHA-256
`756a2e092e50dc6690bd6a604e6a157975f898b73b89a18eefb74c53cc975625`).
Only the frozen disjoint source writes are released. Root retains public
import, combined source review, local commit and checkpoint duties. No
compiler, checker, project hash helper, active-output/cache action or final
review is released. All original book and acceptance requirements remain.

## Complete stopped source and local commit — 2026-11-03

Candidate: a601ad713368daf8e18d5a5537a83d47138491fa.
Parent/original review base:07e480f6ec9958d4975bb90151005b84f2907614.
The clean branch work/fdsa-logarithm-bounds changes exactly five paths with874
insertions. All three authors completed full assigned-source readbacks and
stopped; root read each full initial source and all exact final deltas, the
47-line additive map and32-byte public import. No statement or independent
expected value changed to fit a proof. The bounded peer wording finding
XL01-EC01 is resolved and preserved in the source assessment.

- reviews/logarithm-bounds-source-precommit.json:8,950 bytes /262 lines,
  SHA-256 ec99feff35ad91270c77529c042a5fd414b103bfc2612286eb26a52e7c1230d6.
- reviews/logarithm-bounds-source-final.json:9,868 bytes /279 lines,
  SHA-256 2f4c5bb6ac7632fa879f60cd287f9bc57e0750e73583528adbbea9969785bd1b.
- reviews/logarithm-bounds-source-assessments.md:6,926 bytes /112 lines,
  SHA-256 ab2101aa4a709243a17cb92c4766d60b17c7df8a454dfbcd540a93a557176e1d.

All prior root/map bytes,23 other existing baseline files, absent alternative
lakefile, complete1842-byte notice, frozen inputs and main/C1 source are
preserved. The source checkout has no project build. Checkpoint0063 will
save this commit and the0062 post-archive receipt/inspection/release records.
No compiler, project checker/hash helper, cache experiment or final review
ran for XL01. All original book obligations and later acceptance gates remain.

## Durable source checkpoint — 2026-11-03

Checkpoint0063 is saved as libfile_e3b80e2e60d48191a50022f279b09afc:
75,055,255 bytes, SHA-2561ed33919b386923c37001ea91a4b60341393c52e4bb7ab46e789e40cfa2defec.
All632 payload hashes and53 refs passed bounded inspection; only this branch
and worktree HEAD advanced to the recorded a601ad71 commit. The complete
226-line inspection was root-read. Its own receipt/inspection and the preserved
local-network save recovery postdate the archive and enter the next checkpoint.
Source remains uncompiled and unaccepted; all existing acceptance gates remain.

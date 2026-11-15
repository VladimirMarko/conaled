# XT03 measured-fold draft handoff

## Exact identities and authority

- Local ticket: FDSA-XT03; parent FDSA-000; original whole-book task unchanged.
- Frozen requirements: `tree-fold-resource-requirements.md`, version 1,
  SHA-256 `0a83c0b87873c33f2d5bf5aeef655ae4ab2957bb4100202164b217363ed8fcf8`.
- Original and immediate parent base:
  `64c6b777d828ecfe83234fc2aed94600a1f24297` (saved unaccepted XT01).
- Candidate: `b0fce71fa00b2ff6250b09002176bdc75baf1f46`.
- Branch: `work/fdsa-tree-fold`; checkout: `conaled-tree-fold`.
- Commit: `feat(resources): add measured whole-tree folds (#174)`.
- Seven paths, 975 inserted lines; source clean after commit, confirmed through
  read-only Git operations inside the pinned Nix environment.
- Checkpoint 0031 saved the clean pre-code scope and all three full preflights
  before implementation. Checkpoint 0032 will preserve this committed draft.

Accepted repaired Chapter 1 and accepted XT01 are prerequisites to integration
or acceptance. XT02 is a separate branch and not an implementation dependency.
The initial Chapter 2-first integration plan is unchanged. Preserve this base,
all source history, requirements, findings and original book obligations when
adapting to an accepted tip. No GitHub write has occurred.

## Source scope and connected evidence

`Applications.Resources.TreeFold` specializes ordinary `Trees.fold` at actual
measured values. Raw execution and unconditional value erasure require only
`Add`; independent payload/summary/observation universes remain explicit.
Exact parentheses, nil charge and existing post-body tick are retained.
Ordinary fold fusion supplies value erasure and additive-hom observation
transport; label transport reuses `fold_map` without charging an extra pass.

The natural-cost statements compare actual fixed-callback entry-e and entry-zero
runs. They identify child values before combining costs, giving
`W_e=W_0+e*(2*n+1)`. Constant and upper-bound hypotheses range over summaries
returned by arbitrary finite child trees at fixed parameters; they are not
all-summary laws or input-local subtree laws. One fixed bound covers a family.

Connected source cases include:

- Canonical size and height, zero arithmetic callback work, arbitrary labels
  and `BinaryTree Empty`.
- Actual single, right-associated and left-associated append callbacks;
  actual intermediate-result/value/length connections, node recurrences,
  nil/singleton boundaries and sample work 15/23/25.
- Actual measured smart-node annotation, returned-tree equality, recursive
  validity, erasure and reader/fold connection; size/height sample work 21 and
  actual append-annotation sample work 27.
- Additive FreeMonoid postorder word `[0,2,3,1]`, value-size connection, and
  singleton `E E K E` versus collected `K E E E` inequality.
- Product run with existing inr/fst/snd/sum homs, preserving callback values;
  structural/zero-entry/entry-one equalities and sample pairs `(9,6)`/`(9,12)`.
- A callback returning zero on every run while charging seven at an unreachable
  argument; reached-zero bound plus structural lower bound gives exact work.

The optional zero-helper arithmetic comparison was not added. No source
translator, new reachability framework, second recursive evaluator or broader
algorithm implementation was introduced. The reconstruction note records
literal right append association, explicit tariffs, statement review and
remaining original chapter obligations.

## Independent bounded readings and findings

Complete retained assessments and correction history:
`tree-fold-resource-source-preflight.md`.
Original reading-phase file identities:
`tree-fold-source-preflight-snapshot.json`.
Current exact seven-path identities:
`tree-fold-resource-source-identities.json`.

- `book_inventory`: full core source against XT03-01..03 and exact reused APIs;
  no concrete finding. Separately read the full reconstruction note and only
  appended XT03 source-map section; DOC01 below.
- `tail_examples_preflight`: full primitive/append/annotation client sources
  against XT03-04/05; CP01 below, no mathematical/scope discrepancy.
- `architecture`: full observation client against XT03-06 and core contracts;
  no concrete mathematical/scope/API mismatch. Concrete word simplification,
  hom coercions and wrapped-versus-raw term elaboration remain uncompiled.

| ID | Original concern | Disposition |
| --- | --- | --- |
| XT03-CP01 | Expected `rw` transparency blocker between raw run and `annotateRun` in list-node cost proof | Explicit typed child-read equality and recurrence hypothesis; same-reader source rechecked; compiler and final confirmation pending |
| XT03-DOC01 | Exclusion list inadvertently imposed optional general frameworks/statistics as mandatory future deliverables | Note and map distinguish exclusions from original source obligations; same-reader source rechecked; final confirmation pending |

The original CP01 source and DOC01 note/map bytes are retained under
`tree-fold-preflight-snapshots/` with exact identities. The frozen requirements
were not edited. Source rechecks neither erase findings nor substitute for the
full final axes on the eventual validated integration candidate.

## Validation and limits

Passed: tracked unstaged `git diff --check` and complete staged
`git diff --cached --check`, using the pinned Nix shell. The final source
commit and clean status were recorded. Public closure is intended through
`Examples.TreeFoldObservations` -> `TreeFoldCache` -> `TreeFold` -> core; this
is not a claimed project-checker result.

Not run: any XT03 compiler, focused module build, integrated gate, exhaustive
proof audit or final Standards/Spec review. No second compiler, project checker
or project hash helper ran while old Chapter 1 session 80227 remained active.
The active old candidate stayed `1aabd512284fe86254278ac631eda061d311050b`;
its eventual result cannot accept repaired Chapter 1 or XT03.

Next: preserve and upload checkpoint 0032 immediately. Continue the old gate
unchanged. On its actual exit, preserve historical outcome and evidence, then
follow the saved repaired Chapter 1 acceptance process before Chapter 2.
Integrate this unit only when its accepted prerequisites exist, preserving
history and all corrections. Run focused development checks as appropriate,
full candidate build/guards/audit, both final axes with the complete unchanged
scope and carried findings, then immediately verify the approved candidate.
No chapter or shared unit is accepted by this handoff.

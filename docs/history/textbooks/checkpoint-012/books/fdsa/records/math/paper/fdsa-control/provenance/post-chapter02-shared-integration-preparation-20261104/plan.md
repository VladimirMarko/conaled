# Deferred XP01 / XR01 / XW01 incorporation after complete Chapter 2

Prepared 4 November 2026 by `/root/shared_acceptance_sequence`. This is source-only integration preparation, not a third mathematical review or a candidate approval. The companion `receipt.json` gives exact commits, all 17 unit-path entries, source blobs/SHA-256 values, imports, old-prefix differences and read boundaries.

## Fixed boundary and proposed route

Only Chapter 1 R=`07e480f6ec9958d4975bb90151005b84f2907614` is accepted. The unchanged first route is **F → combined XM01/XD01/XQ01/XU01 → XU02 → XU03 → newly assembled complete C2**. Exact live F remains first priority. Nothing here assembles a candidate, starts C3, uses retired outputs or grants later validation. `CURRENT.md` §§ First acceptance / Fixed subsequent acceptance route and `REQUEST.md` §§ Interpretation / Recovery steering control these boundaries.

After the actual complete C2 acceptance, a concrete later route is to incorporate and finish XP01, then XR01, then XW01, carrying the accepted head forward at each step. This is an operational option, not a newly imposed mathematical ordering or permission to batch the three gates. XR's saved parent includes original XP01, but its theorem has no XP01 import dependency; XW is also independent of XP01/XR at the source-import level. Their separate full frozen scopes and existing round1 findings/review records remain controlling. No chapter-specific obligation is discharged by this ordering.

Do not fast-forward to T or substitute either original XR/XW tree for the future accepted head. T is development over unaccepted Z, and the original XR/XW tips contain obsolete ancestor source. Start each eventual successor from the then-accepted predecessor. Replay the bounded unit change, retain all predecessor paths outside it, reconcile the two shared documentation/import files and commit the result for the existing whole-scope acceptance loop. The future accepted C2 commit is not yet known or bound by this note.

## Exact source identities and unit ownership

| Unit | Exact delta to preserve | New unit-owned paths | Existing paths whose bounded changes belong to the unit |
| --- | --- | --- | --- |
| XP01 | Z=`4b5dbfa07288acc73f25c27838d3fb2f78e77d71` → T=`12cb14fc98b8617b3b625620da8e60936daba340`; original c80→c28 scope plus both preserving corrections | `Examples/MappedPotentialAccounting.lean`; `docs/research/fdsa-potential-accounting.md` | `Applications/Resources/Potential.lean`; `Applications/Resources/FIFOContracts.lean`; `SquareApplications.lean`; `docs/research/fdsa-reconstruction-map.md` |
| XR01 | Original parent `c28ba71863d2a35ee1c3a089caa90464e4cca692` → direct child `d64b4c89fb9f21d1a6a2a603c1dc04f47233d9e2` | `Applications/Resources/AffineRecurrence.lean`; `Examples/AffineRecurrence.lean`; `docs/research/fdsa-affine-recurrence.md` | `SquareApplications.lean`; `docs/research/fdsa-reconstruction-map.md` |
| XW01 | Original parent `a14977b9e316cc484ffad8a470d26b15615956c0` → direct child `7c6bc92c276d39e84351324c442869b8ffa6758c` | `Applications/Probability/AccumulatedWork.lean`; `Examples/AccumulatedWork.lean`; `Examples/AccumulatedWorkBoundary.lean`; `docs/research/fdsa-accumulated-work.md` | `SquareApplications.lean`; `docs/research/fdsa-reconstruction-map.md` |

The original XP01 commit is `c28ba71863d2a35ee1c3a089caa90464e4cca692`, parent c80. Correction1 `cfa413e247c084245a270ae7bcc91fd9ea24b002` repairs the ordered proof terms and the map qualifier; correction2 T repairs only mapped-example proof bodies. Taking T's final single-commit diff alone omits the original generalization. Its complete Z→T six-path delta is the authoritative corrected transfer boundary. The intervening development merge `5ffa882bbcb34c1c533710a0c980423484e5a77d` includes Z and is not a new unit-owned source set. A bounded replay of original c28 plus its two corrections is another way to realize the same source delta, subject to exact reconciliation against the accepted predecessor.

XR and XW are each linear one-commit unit deltas, so later cherry-picking their exact original commits is a possible assembly technique. This note has run no merge/cherry-pick or merge simulation and claims no conflict-free future result. Restrict any resolution to these original scopes plus genuinely necessary reviewed incorporation changes; retain the full source assessment rather than treating a successful patch application as a gate.

## Import dependencies and retained predecessors

| Unit | Complete project-local source import closure | Inherited source to retain |
| --- | --- | --- |
| XP01 | 15 local modules, 12 distinct direct external imports; roots Potential, FIFOContracts, MappedPotentialAccounting | The 12 inherited modules listed in the receipt are byte-identical at R/F/Z/T. These include Measured, Workload, BinaryCounter, SymmetricCosts, AbstractFIFO, the Symmetric modules, ListFusion, Relations and Squares. |
| XR01 | Only its two new modules, six direct Mathlib imports | No inherited project module is imported. In particular, neither Potential nor Growth is imported. Preserve the accepted Growth interface and all other predecessor source independently of the old branch's snapshot. |
| XW01 | Eight local modules, 12 distinct direct external imports | Preserve `Applications/Resources/{Measured,Workload,CallCount}.lean`, `SquareKit/ListFusion.lean`, and `Squares.lean`; all five old-tip blobs equal R/F/Z/T. |

These are direct project-source closure facts, not a count of all transitive Mathlib dependencies or an execution qualification. The receipt records every import edge and source hash. Existing exact Lean/Lake/configuration/dependency pins remain unchanged; no dependency implementation is transferred from an old unit branch.

Concrete old-prefix hazards were verified by immutable Git comparison:

- XR lacks the accepted `Applications/Resources/CallComparison.lean`, `Applications/Resources/SharedDemand.lean`, `Examples/CallModels.lean`, and `Examples/SharedDemand.lean`; its ListCalls and FunctionalNotation blobs differ from corrected F/Z/T. Its inherited Potential blob predates XP01-ELAB-001, and its mapped example predates XP01-ELAB-002. None belongs to XR's five-path delta.
- XW carries older `Applications/Resources/CallComparison.lean`, `Examples/CallModels.lean`, and `Examples/SharedDemand.lean`. Its actual SharedDemand core is already the accepted blob; do not conflate the older example with a core difference. Its Potential/FIFO snapshots predate XP01 and its tree lacks the new shared-foundation/C2 paths. None of these ancestor files belongs to XW's six-path delta.
- Both old tips retain the older Growth blob, whereas Z/T contain the corrected C2 Growth source. Copying whole ancestor files would therefore undo a predecessor change even though neither new analytic theorem imports Growth.
- The old XR public root lacks 31 imports present at T; the old XW root lacks 34. The exact missing imports and all differing nonunit paths are inventoried. Those counts are comparison facts against unaccepted T, not a future acceptance inventory. Preserve the actual future accepted predecessor's full import set.

## Shared root/map reconciliation and factual public status

Each unit adds exactly one public-root import: `Examples.MappedPotentialAccounting`, `Examples.AffineRecurrence`, or `Examples.AccumulatedWork`. The last main module imports `Examples.AccumulatedWorkBoundary`, so its complete boundary proof scope remains reachable. Add these to the then-current root without replacing it with any old whole-file snapshot.

The map additions are similarly bounded: XP01 adds the Chapter19 queued cross-reference, its six-line shared-accounting paragraph and the Chapter1 qualifier; XR adds the 23-line shared-affine section; XW adds the 16-line shared accumulated-work section. Preserve all accepted Chapter1/foundation/C2 mapping and previous factual corrections. The old final map files are not transfer units.

**Carry the resolved XP01-DOC-001 correction verbatim in substance:** “For Chapter 1, the only existing public-interface adjustment is the universe signature of `Resources.erasureSquare`.” T has the exact reviewed two-line sentence recorded in the receipt. XR's old map still has the unqualified predecessor sentence at lines466–471; this is the same inherited finding, not a new ID or a reason to reopen the accepted C1 result. XW predates XP01 and is not retrospectively charged with that finding, but incorporating its map must preserve the current qualifier.

There is also a concrete factual-status reconciliation before each later immutable candidate. T's potential note lines87–89 still says compilation is pending, whereas its actual focused4 and complete20 type evidence now exist. XR's note lines3–5 and225–233 predates complete independent source assessments and already has its public-root import at the original tip. XW's note lines9–14 and its old map section describe the originally uncompiled draft and old Chapter1 gate. Frame retained development prose explicitly as dated history and state only actual secured evidence/current lineage as of that date; retain mathematical contracts, source attribution, notices and all mandatory gates. This note authors no replacement prose and grants no present or future validation. Do not invent an authorship date or describe a historical focused pass as an accepted integrated candidate.

## Contract changes and complete scope retained

XP01 intentionally changes the public generality of `Resources.budget` and `budget_append`: raw observations and charges become independent carriers; the append law retains exactly its required algebra. FIFO's raw zero becomes explicitly Nat. This is the substantive existing-interface change; the source-assessed corrections preserve every statement, minimal assumption and ordered term. Retain all old Nat wrappers, initial-credit counterexample and required counter, symmetric-list, FIFO, random-access and SharedDemand clients. `SharedDemand.run_work_remaining` continues to use the existing Nat contract. The complete original eight frozen requirements, exact/inequality/invariant/signed laws and all connected examples remain required.

XR introduces ordinary scalar results rather than modifying existing resource APIs. Its complete 21-name surface includes the quarter recurrence and every signed/quantifier boundary. Preserve the original five paths and all frozen source-specific exclusions; exact rounded/source constants and selector/cost correspondence remain Chapter3 obligations. XW introduces six ordinary analytic laws plus both complete client modules; retain the single-measure interpretation, ENNReal arithmetic, single-prefix tail premise, actual run/bind/reweight observations and all zero/prefix/noncontraction boundaries. Its two private helpers and anonymous probability instance remain in scope. Later conditional sampling, algorithm tariffs and chapter claims remain deferred.

No new mathematical defect or actual merge conflict is claimed from this preparation. The known concerns are the explicit API generalization, obsolete ancestor blobs, overlapping root/map paths and historical public-status wording. Any actual successor changes or compiler diagnostics must continue the same full-scope independent reviews.

## Existing evidence, type inputs and gates still required

| Unit | Secured prior evidence | Existing inspection input and remaining evidence |
| --- | --- | --- |
| XP01 at T | Both complete original-scope source reports; focused4 outer/native exit0; all20 actual qualified public types fully read on both axes; DOC001/ELAB001/ELAB002 resolved | Reuse the existing 20-name input. This note grants no future reuse: the exact incorporated source/import closure, pins/configuration/runtime and qualified actual build/output lineage must support any later qualification. Retired central outputs cannot supply new captures or execution. |
| XR01 at d64 | Both complete five-path source reports, zero new concrete findings; inherited DOC001 carry-forward remains | Existing 21-name input is prepared only; actual focused build and all21 full type assessments remain unexecuted. Generated recursive/termination declarations remain audit scope. |
| XW01 at7c6 | Both complete six-path source reports, zero concrete findings, including all219 Boundary lines | Existing 78-name input is prepared only; actual build/types remain unexecuted. Establish the anonymous instance's actual generated identity/type without guessing it; retain both private helpers and every generated declaration in full audit coverage. |

No duplicate type program or compiler probe was created. The receipt hashes the existing inputs and all complete reports. Explicit public counts are not counts of new theorems, kernel declarations or completed book obligations.

For each eventual incorporation, preserve the original frozen requirements outside its diff, bind the complete scoped source and successor changes to a committed immutable candidate, obtain applicable qualified focused evidence and complete actual statement assessment, then the README's applicable full guarded candidate check and exhaustive permitted-axiom audit. Continue both existing independent Standards/Spec axes on that exact candidate, retaining prior source assessment only where exact identities support it. Resolve all findings, run immediate qualified `./check.sh --verify-candidate HEAD`, then accept the exact approved local successor and update local tickets/coverage/checkpoint. Apply the repository's actual normal-versus-fresh rules; this preparation creates no fresh-run trigger or waiver. Supported regeneration and resource prerequisites apply before use of any retired output tree.

## Read boundary and no execution

This preparation read all three complete frozen requirements, the three complete current round records, all six complete current independent source reports, all three tickets, both original XR/XW handoffs, governing REQUEST/AGENTS and operative CURRENT/STATUS; current INDEX reading was bounded to the three relevant rows. It inspected immutable scope diffs/parents, complete root/map deltas, the listed import statements/closure identities, selected public-note status contexts, and all three existing type programs. It does not repeat the completed mathematical assessment of every unit source or claim a new full dependency-source review. One oversized earlier display was not credited and all required report/requirement content was reread in complete bounded outputs. Expected missing-path Git lookups were source-absence observations, not compiler failures.

Only this new two-file control package was written. No source/ref/index/output/pin/runtime mutation, new worktree, compiler, process polling, output capture, merge or candidate assembly occurred. Existing F145/279/Order/Tail preparations and all review/control records remain unchanged.

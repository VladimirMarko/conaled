# GitHub issue #459: Reconcile and complete the remaining ADWH Chapter 2 contracts

Source: https://github.com/VladimirMarko/conaled/issues/459
Retrieved: 2026-11-13 (UTC). Live issue snapshot; historical instructions are evidence, not active checkpoint commands.
Issue state at retrieval: open. Updated: 2026-11-12T15:07:17Z.

## Issue body

## Owner clarification, 2026-11-11

Apply #458's deciding criteria: recover useful built mathematics, cover the book with factual corrections, and produce useful `conaled` results. Historical checkpoint contracts and private planning identifiers are evidence, not authority. Reconcile every selected family against book content, corrected mathematics and current implementations; justify replacements or exclusions rather than copying an inferior formulation. The inherited acceptance criteria below are read under this clarification.

Part of #149. Recover the remaining Chapter 2 contracts from the retired external continuation, reconciling them with current code before selecting bounded implementation slices.

Research is preserved locally in `docs/research/adwh-recovered-research.md`; ticket and source disposition is in `docs/research/adwh-recovered-handoff.md`. These files are now published on master. The external source is `059fccc9b409d7ce01361daef9ca17483a343218`; its published integration is commit `1e7bee1e979eeea3fe90bca4504de301426ce073`. Historical private acceptance labels and chapter-order gates are not current authority.

Names such as `CH02-LIST-COST` in the archived drafts are the external agent’s private planning identifiers, not conaled naming conventions or established textbook terms. This checklist uses descriptive subject names; the handoff retains an explicitly labelled historical cross-reference.

Family dispositions and remaining work:
- [x] Selected list costs and concatenation bounds (R1): #468 supplies uniform concatenation and its fold consumer; #469 supplies exact takeWhile extrema and its prefix-fold consumer. Existing generic `ListExecution.head_work`/`reverse_work` and the established growth bridge account for the selected head/reverse summaries; see the R1 disposition below.
- [ ] Composition demand, delayed lists and head of concatenation: cache/request semantics, delayed construction versus forcing, deferred append histories and partial-domain boundaries.
- [x] Selected list-predicate trim and prune (R3): #470 supplies whole-list trim; #471 supplies cut/folded prune and native potential/budget accounting; #472 supplies actual constant guard-dispatch execution, complete zero-price recovery, archived unit-price specializations and new arbitrary-natural-price laws. Independent specifications, TailClosed longest-prefix recovery and ordered consumers remain preserved. This accounts for the selected recovered R3 contracts; printed-book completeness and licensing remain #149.
- [x] Selected literal and eager dynamic arrays (R4): #508 supplies both actual resizing policies, arbitrary surrounding copy windows, complete ordered and per-insertion observations, additive repricing, all-raw-state potential bounds, and execution-derived geometric/growth characterizations. Checked workload crossovers distinguish the policies; neither is uniformly cheaper. This accounts for the selected recovered R4 contracts; printed-book completeness and licensing remain #149.
- [x] Selected digit search and finite averages (R5): #478 supplies actual first-hit measured execution, native ordered List.pi population with a finite-function uniform bridge, the corrected finite mean including terminal failures, and exact finite error/convergence. Printed-book completeness and licensing remain #149.
- [x] Selected counter geometry and output (R6): #479 supplies the actual-execution geometry and ordered bills; #505 supplies the seed-inclusive measured prefix, exact token rendering and representation decoding, digit mass, separate transition/symbol charges, retained loose bounds, and a native traversal/insertion-output consumer. The five-state example emits 23 tokens and incurs 7 writes; the alternative 24-unit tariff is a different observation. Existing counter/workload/potential and traversal owners are retained. This accounts for the selected recovered R6 contracts; printed-book completeness and licensing remain #149.
- [ ] Selection-based and insertion-based permutation costs and growth (R7): #506 supplies positional measured generation, exact ordered values, adequate-fuel full-pair equality, complete-spine observation and execution-derived growth. #507 supplies first-equal removal with a declared unit equality-oracle tariff, data-dependent executed bills, full-pair fuel correspondence and complete-observation growth. Representation-dependent equality computation is outside that tariff. Delayed ordinary/accumulating insertion with explicit forcing/sharing observations remains open. #505's insertion-output example observes existing outputs only; it is not measured recursive generation.

## R1 evidence and remaining boundary

`ListExecution.head_work` gives exact cost 1 for every actual list; for any input family, coefficient 1 at threshold 0 works in both growth-comparison directions. `reverse_work` gives exact `2*length+1`. For positive length this implies bounds `2*length` through `3*length`. For an explicitly given family with length n, coefficients 3 from threshold 1 and 1 from threshold 0 give the two linear-growth comparisons through `Resources.isBigO_natCast_iff` (inclusive-threshold specialization: `Examples.ResourceGrowth.nat_upper_iff_isBigO`). These are mathematical consequences of checked general results, not newly compiled named generic Theta declarations.

Existing reverse/reweighting/fold and builder/head consumers retain values and complete construction bills. Reverse at size zero still costs one, so no all-index homogeneous upper bound is claimed. This accounts for the selected recovered R1 mathematics without copying historical wrapper names. R2 and R7 remain open; full printed chapter evidence/licensing remain #149. Neither this reconciliation nor the two child deliveries completes #459 or Chapter 2.

Acceptance: map each selected source contract to a current equivalent or explicit remaining obligation; split implementation into scoped children as needed; retain discriminating negative/boundary cases and connected consumers. Shared varying-callback measurement should have one owner. Guarded build, growth, sums, discrete estimates, exact arithmetic and recurrence slices are already integrated and must not be reimplemented from stale planning prerequisites. Passing this issue requires the agreed Chapter 2 scope to be accounted for, with any deferrals explicitly approved and linked; it does not close the whole-book umbrella.


## Completed design investigations

#475 assessed demand/forcing/sharing, #476 dynamic-array policy and storage observations, and #477 varying measured callbacks. All five investigations, including #473/#474 under #235, are published in `docs/research/design-challenges/2026-11-11/README.md`, with three independent assessments and a reconciled report each. The investigations are closed; proposed experiments and architectural adoption remain separate decisions.



## Comment 6802829665

Source: https://github.com/VladimirMarko/conaled/issues/459#issuecomment-6802829665

#458's audit is accepted on master at `924542a1cdab7a3637a14fb9c61945b41fea77e4`. Use the updated `docs/research/adwh-reconstruction-map.md` and `adwh-recovered-integration.md` for packages R1–R7 and existing coverage. Preserve the owner's three deciding criteria; checkpoint335 remains evidence only. Timing/Amortized is already delivered under #173. Printed-chapter evidence remains incomplete under #149; do not infer whole-book certification from the audited code correspondence. This issue remains open for the scoped remaining work.


## Comment 6805062127

Source: https://github.com/VladimirMarko/conaled/issues/459#issuecomment-6805062127

#468 is delivered and closed on master at [81b4ce88](https://github.com/VladimirMarko/conaled/commit/81b4ce888746230e6ac795c1636b4327d6482550). The uniform-concatenation portion of R1 now uses the existing native executors for exact costs, arbitrary accumulators, two-parameter finite bounds and an order-sensitive fold consumer, with retained boundary and negative cases. See `docs/research/uniform-concatenation.md` for source dispositions and the checked interfaces.

R1 is still incomplete: best/worst takeWhile and reverse/head growth remain. R2–R7 remain open under this issue. The checklist is qualified accordingly; this issue and #149 remain open. Preserve useful built mathematics, book coverage with factual corrections, and usefulness to conaled as the deciding criteria. Historical checkpoints are evidence only; the incomplete printed-chapter evidence is unchanged.

The combined #466/#468 candidate passed the guarded build of all 2,762 modules, exhaustive proof audit (only `propext`, `Classical.choice`, `Quot.sound`), exact-candidate verification, and independent whole-wave Standards and Spec review.


## Comment 6805487438

Source: https://github.com/VladimirMarko/conaled/issues/459#issuecomment-6805487438

#469 is published and closed at `79182c412783b8939522a32438268f2ace1512e6`. The [takeWhile report](https://github.com/VladimirMarko/conaled/blob/79182c412783b8939522a32438268f2ace1512e6/docs/research/takewhile-extrema.md) delivers sharp measured extrema, an actual ordered prefix-fold consumer, suffix independence and boundary/negative cases using the existing executors. Together with #468, this completes the selected concatenation and takeWhile implementation slices.

Do not yet mark all R1 complete. Head/reverse coverage and the R1 disposition need the separately reviewed documentation reconciliation now being prepared. R2–R7 remain owned by #459; #149 retains wider book coverage and incomplete printed-chapter evidence. Historical checkpoints remain evidence, under the owner's useful-mathematics, corrected-book-coverage and useful-conaled criteria. These counts do not certify physical runtime or unseen book claims.

The published wave passed independent per-ticket and combined Standards/Spec review, all 2,767 modules, exhaustive three-axiom audit and immediate exact verification. Both broader parents remain open.


## Comment 6805547838

Source: https://github.com/VladimirMarko/conaled/issues/459#issuecomment-6805547838

Published the separately reviewed R1 reconciliation at [3601424e](https://github.com/VladimirMarko/conaled/commit/3601424ed036751053ac34463092cce01cad2d4f). `docs/research/adwh-r1-disposition.md` records the selected family as accounted for by #468/#469 and existing exact head/reverse contracts with explicit growth-comparison witnesses. This does not claim a newly compiled generic Theta wrapper.

Only the selected R1 checkbox is complete. R2–R7 remain open, as do #149 printed-book and licensing obligations. The original #458 audit evidence and child implementation scopes are preserved. Independent Standards and Spec review passed for the six-document change and these tracker dispositions; artifact links, declarations, archive hashes and historical JSON preservation were checked.


## Comment 6805901815

Source: https://github.com/VladimirMarko/conaled/issues/459#issuecomment-6805901815

#470 delivered arbitrary whole-list Boolean trim with an independent unique longest-admissible-prefix specification and actual measured recursion. Exact work is work+k²=n(n+1); an ordered fold consumer preserves the independently specified output and its additive bill. Pairwise/adjacent and non-tail-closed examples distinguish the contracts. [Source dispositions and limits](https://github.com/VladimirMarko/conaled/blob/3528432757b3d633c577116d22e39ea0e53dfd6d/docs/research/whole-list-trim.md). Prices are selected abstract costs, not physical predicate measurements. Folded prune, cut, TailClosed equivalence, cumulative potentials and positive-dispatch variants remain #459 R3; R5 and printed-book/licensing obligations under #149 remain open.

Published on master in 3528432757b3d633c577116d22e39ea0e53dfd6d. The combined candidate passed all 2772 modules, the exhaustive proof audit and immediate exact-candidate verification. Both independent review axes passed for each ticket and the complete combined scope. The initial interrupted validation attempt is retained in orchestration evidence; acceptance uses the successful retry.

This parent remains open; this result completes only the linked bounded child.


## Comment 6806215267

Source: https://github.com/VladimirMarko/conaled/issues/459#issuecomment-6806215267

#471 is published at [e80c51d9](https://github.com/VladimirMarko/conaled/commit/e80c51d968925be3809ba3acc3259de7041b504b). FoldedPrune executes tail-first cuts through unchanged WholeListTrim, with an independent unique recursive specification. TailClosed gives original-input longest-prefix recovery; arbitrary decidable Pairwise relations supply that condition. The nonclosed counterexample rejects unconditional recovery.

Native Workload/Potential accounting retains arbitrary initial states, both boundary potentials and actual trajectory charges. The native budget and work are bounded by 3*n*n. The executed fold consumer retains its ordered value and exact additive bill. The nondecreasing fixture has prune work 24, budget 33 and consumer work 31; equal single-trim values have different measured costs.

[Declaration dispositions, consumers and limitations](https://github.com/VladimirMarko/conaled/blob/e80c51d968925be3809ba3acc3259de7041b504b/docs/research/folded-prune.md) and [frozen contract](https://github.com/VladimirMarko/conaled/blob/e80c51d968925be3809ba3acc3259de7041b504b/docs/research/folded-prune-contract.md) are committed. All 2775 modules and the exhaustive three-axiom audit passed. Independent Standards and Spec reviews and the final full-scope coordinator gate passed; immediate exact-candidate verification passed before publication. Local receipts are preserved in 471-handoff, prune-wave-review and prune-wave-completion under /tmp/conaled-wave-20261111.

This completes the selected zero-dispatch folded-prune child. Positive and arbitrary guard-dispatch pricing remain #459 R3; R2 and R4–R7 remain open. Printed-book evidence and licensing remain #149. These are selected abstract prices, with no whole-chapter completion or architectural adoption claimed.

This supersedes the earlier remaining-work note for cut, folded prune, TailClosed equivalence and cumulative potentials. The broader parent remains open.


## Comment 6806477466

Source: https://github.com/VladimirMarko/conaled/issues/459#issuecomment-6806477466

#472 is published at [502e55fd](https://github.com/VladimirMarko/conaled/commit/502e55fdc331a0c7f87609ddf74701c90c2e6d4e). Actual trim/cut/prune runners accept a constant natural guard-dispatch price. Full measured pairs recover the accepted runners at price zero; price one recovers the selected archived positive-price results. Generic natural-price laws are newly proved, not attributed to the archive.

Native Workload/Potential accounting preserves arbitrary initial states and both boundary potentials. The priced budget equals the zero-price budget plus twice price times command count. The ordered consumer retains full values and bills: price one gives prune31/fold38, price two gives prune38/fold45. Empty trim and empty prune remain distinct. The finite coefficient obstruction quantifies all prices and lengths; it does not reject eventual bounds with price-dependent thresholds.

[Source mapping and limits](https://github.com/VladimirMarko/conaled/blob/502e55fdc331a0c7f87609ddf74701c90c2e6d4e/docs/research/priced-prune.md) and [frozen contract](https://github.com/VladimirMarko/conaled/blob/502e55fdc331a0c7f87609ddf74701c90c2e6d4e/docs/research/priced-prune-contract.md) are committed. Exact acceptance checked all 2778 modules and the exhaustive permitted-three-axiom audit; independent Standards and Spec and the full-scope coordinator gate passed. Immediate exact-candidate verification passed before publication. Local receipts remain under /tmp/conaled-wave-20261111/472-handoff and guard-price-wave-review/completion.

Together #470–#472 account for the selected recovered R3 obligations. R2 and R4–R7 remain open, as do printed-book evidence/licensing under #149. Prices are abstract source costs; no physical callback runtime, allocation, general lazy semantics or broader architectural adoption is claimed.

This supersedes the earlier open R3 guard-price note. The parent remains open.


## Comment 6806681503

Source: https://github.com/VladimirMarko/conaled/issues/459#issuecomment-6806681503

The five authorized design investigations #473–#477 are complete and [published with briefs, fifteen independent reports and reconciled syntheses](https://github.com/VladimirMarko/conaled/blob/1ecdea2376786920a043009a35712a5dec93723a/docs/research/design-challenges/2026-11-11/README.md). Both publication review axes passed. Source inspection, paper proposals and executed checks remain distinguished; no architecture was adopted.

#473 recommends testing independent state-valued operations before generic signatures. #474 proposes a bounded Type Σ/Π helper comparison and a separate groupoid experiment. #475 retains partial observations and calls for explicit request/cache/terminal behavior. #476 preserves raw states, ordered event blocks and distinct policy hypotheses. #477 identifies an existing varying-callback traversal in StructuredLinear.Costs that should be evaluated before introducing another owner.

These are proposed experiments for owner discussion. Current bounded #478 first-hit search and finite-uniform mean work proceeds independently under existing interfaces. This parent remains open.


## Comment 6806913999

Source: https://github.com/VladimirMarko/conaled/issues/459#issuecomment-6806913999

Selected R5 is complete through #478, published at `61f94f45c61bfeab35945bd47004d3803fd1ab2f`. The actual first-hit executor and ordered finite population yield E(n) = 2 − 2/2^n, including terminal failures, with checked boundary cases and native convergence. Full 2,781-module build/audit, both independent review axes and exact prepublication verification passed.

The checklist now reflects this selected coverage. R2, R4, R6 and R7 remain open; #149 retains printed-book completeness and licensing. The five design investigations are completed reports, not authorization to adopt their proposed architectures.


## Comment 6806974322

Source: https://github.com/VladimirMarko/conaled/issues/459#issuecomment-6806974322

#479 is the next bounded R6 geometry slice: derive halving/floor-sum laws from the existing actual counter executor, retain cutoff and power boundaries, and expose ordered per-transition bills through the existing workload runner. Native counter/workload/potential owners remain in place. The source assessment found this independent derivation missing; existing potential bounds are reused as preserved contracts, not reconstructed.

R6 token rendering, decoding, digit mass and output charges remain separate open obligations. #479 does not adopt the shared traversal proposal from #477 and must not close all R6 or #459.


## Comment 6807290815

Source: https://github.com/VladimirMarko/conaled/issues/459#issuecomment-6807290815

#479 is complete and published at ca91c755: independent counter geometry now derives exact floor sums and their cutoff remainder from existing execution, with ordered per-transition bills and seed-inclusive indexing. Full 2,784-module build/audit, both independent full-scope review axes and immediate exact verification passed.

R6 remains unchecked because token rendering, decoding, digit mass and output charges are still open. Existing counter/workload/potential owners were preserved. This delivery adopts no shared callback/traversal architecture and does not complete #459 or the printed-book scope under #149.


## Comment 6820244197

Source: https://github.com/VladimirMarko/conaled/issues/459#issuecomment-6820244197

Scheduled #505 as the bounded remaining R6 counter-output child. It will connect actual seed-inclusive prefix execution to concrete tokens, exact representation decoding, digit mass and separately billed transition/output work, reusing existing counter geometry and callback traversal.

The frozen five-state fixture has 23 emitted tokens and 7 transition writes. The #477 alternative 24-unit tariff remains a different observation model. No shared traversal framework is adopted, and R2/R4/R7 plus whole-book obligations remain open. #505 is in progress; this is not a completion claim for R6 or #459.


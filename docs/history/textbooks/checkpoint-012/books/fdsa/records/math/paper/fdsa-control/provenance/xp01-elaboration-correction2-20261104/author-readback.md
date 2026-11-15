# XP01 mapped-example correction 2 — author readback

Recorded 4 November 2026. This is an implementation correction under the existing XP01 whole-unit review loop, not an independent review outcome.

## Exact handoff

Corrected commit: **`12cb14fc98b8617b3b625620da8e60936daba340`**. Parent: `cfa413e247c084245a270ae7bcc91fd9ea24b002`. Branch: `work/fdsa-potential-development`, existing central checkout. Local Conventional Commit: `fix(examples): elaborate mapped potential accounting (#174)`, using command-local `ChatGPT <chatgpt@openai.com>`.

Exactly one source file changed: `Examples/MappedPotentialAccounting.lean`, with 11 inserted and 10 removed lines. Its full successor is 166 lines / 6,932 bytes, Git blob `1fb26b51e9f298bd1ba1d1a5fa2a425142f8d8d7`, SHA-256 `2c83479daec51deb21ec95e26af816bc0dfaa682fdb5ee76ee28cdf1e681386a`. The author directly verified a clean index/worktree and unchanged protected R/F/Z/X refs after committing. Source HOLD began immediately at this handoff.

The original six-path XP01 scope, frozen requirements and required old Nat clients remain in scope. This source correction neither promotes XP01 nor changes the foundation/shared-unit/Chapter 2 acceptance order. Correction1 and its complete 17-payload manifest were verified unchanged, including receipt SHA-256 `e9f9ff7bc4c7968ab5d3cd17e54f793e4437bd45df711f2dbc64bc2927ed9868`.

## Actual input evidence

The complete focused attempt-2 outer log was read: **12,511 bytes / 152 lines**, SHA-256 `8fbbdc6d017240e7984585a02ae04afa3d8ed3ca5a46f3767144c5d7558c84a4`. The outer/native/secured records agree on actual exit **1** at exact clean, unchanged parent `cfa413e247c084245a270ae7bcc91fd9ea24b002`. The 149-line native output is an exact contiguous byte sequence of the outer log. Its original records and the prior correction package remain untouched.

The log explicitly records `Applications.Resources.Potential` built in 3.2 seconds and successful builds of `Examples.PotentialAccounting`, `Examples.FIFOContracts`, `Examples.RandomAccessEndCosts` and `Examples.SharedDemand`. The six-target aggregate still failed: only `Examples.MappedPotentialAccounting` appears in its required-target failure list. No complete XP01 validation or acceptance follows from those individual passes. The previous SymmetricLists success remains in attempt1; no new independent build of that target is invented for attempt2.

There are **20 actual mapped-example error headers**, saved verbatim in `evidence/diagnostic-headers.txt`. They fall into the three concrete categories below; the full original diagnostics are preserved in `evidence/input-full.log`.

## Proof-body corrections — XP01-ELAB-002

| Actual diagnostic group | Narrow correction | Preserved connection |
| --- | --- | --- |
| Old line 75: simplification produces a lambda charge while the goal retains unexpanded, partially applied `charge` under `budget` | Add `change budget clearStep (fun _ t => (1 : Int) - 2 * (t : Int)) is s = _`, then simplify the same supplied theorem using `clearStep` and `potential`. | `InitialCredit.boundary` still derives its universal equality from `Resources.budget_amortized`. The private `charge` definition is unchanged. |
| Ten ambiguous-name errors at old lines 83, 88, 92, 134 and 139, plus three unsolved goals and two follow-on type mismatches | Qualify `Resources.bind` and `Resources.pure` in exactly five existing `norm_num` lists. | The three InitialCredit calculations still rewrite through `boundary`; the two Fractional budget calculations still take `boundary`, simplify its actual run, and use `paid.symm`. |
| Four `Decidable (Valid 0)` failures at old lines 130, 133, 138 and 143 | Replace only those premise proofs with `by norm_num [Valid]`. | The same proposition unfolds locally to `0 ≤ 1`; `Valid`, its domain and all theorem hypotheses remain exact. The arbitrary-list bound still applies `work_bound`. |

No global or local instance was added. No transparency setting, import, option, expected result or mathematical premise changed. The remaining `by decide` in the unrelated InitialCredit nonnegativity proof is preserved; the correction targets only the four observed Valid-premise failures.

## Complete source and statement readback

The complete 165-line input and 166-line successor example files were read, along with the entire 61-line correction diff. An exhaustive byte comparison verifies that the source equals the original with only the recorded local proof replacements. A separate declaration-boundary comparison checks every existing declaration header and definition body:

- **8 definitions:** all headers and bodies unchanged, including the actual transition programs, potential/charge functions, `Valid` and noncommutative trace step.
- **7 named theorems:** every header and hypothesis unchanged; only the private `InitialCredit.boundary` proof changes.
- **16 anonymous examples:** every statement unchanged; seven proof bodies change.

Thus exactly eight existing proof bodies are repaired. These source checks are integrity/readback evidence, not a substitute for elaboration or a proof audit. No new named declaration or example is introduced; no statement-output reuse or generated-declaration count is claimed.

The original expected cases and connections remain:

- Counter accounting still transports the actual local `flipCost_potential` law into the generic mapped theorem. The arbitrary initial bits statement, concrete total work 7 for four increments and zero-initial specialization are untouched.
- InitialCredit still has the actual state change to zero, charges minus one then plus one, raw work two and total charge zero. Its failure without initial potential and its inequality against repeating the original state's charge remain exact statements. The new proof-local lambda is definitionally the original `charge`; it does not replace the trajectory-dependent budget.
- Fractional accounting retains the nonempty domain `s ≤ 1`, the alternating transitions between zero and one, half-unit potential, one-step budget `3/2`, two-step budget `2`, and the arbitrary-list work bound through the invariant-aware theorem. The invalid-state counterexample at state 2 remains untouched. Local unfolding supplies the actual premise `Valid 0`; it does not make invalid states admissible.
- The additive free-monoid case still exercises noncommutative exact telescoping and retains the ordered output `[1, 2]`. Neither that proof nor its raw observation carrier changes.

The relevant generic theorem interfaces and `Resources.bind`/`Resources.pure` definitions were completely read during correction1 and are unchanged in this one-file diff. Their exact source identities and pinned API evidence remain in that package. The actual successful Potential elaboration is recorded by root's closed focused2 evidence; this author did not rerun it.

## Validation and scope boundaries

The author performed only source/diff identity checks, header/definition preservation checks and `git diff --check` (actual exit 0), followed by the authorized local commit. **No Lean/Lake command, compiler probe, cache operation, process polling, printed-type command, proof audit or candidate verification was performed.** The successor handoff is explicitly uncompiled by this author. Root owns all subsequent validation and the independent axes own finding disposition.

The original requirements remain `reviews/potential-requirements.md`, 7,148 bytes / 116 lines, SHA-256 `545b5d2ff4a93594f2b1ca245594233bdfcf461b8f4fe14b3bbe698e6ad1aa2f`. This correction retains all six original unit files and compatibility obligations. Neither this readback nor the prior focused passes supplies final full-unit approval. XP01-ELAB-002 is submitted as a source correction pending actual successor validation and independent reassessment. Every immutable-candidate/audit/review/immediate-verification acceptance gate remains mandatory.

This package contains complete before/after source copies, immutable before/after identities, full diff, original failure copies, all exact error headers and diagnostic mapping, preservation checks and this author readback. The author holds further source and provenance writes after its final readback.

# Uniform-input mean examples: elaboration correction 2

Recorded 4 November 2026 by `/root/shared_acceptance_sequence`. This is an author
handoff within the existing full Chapter 2 implementation/review loop. Root and
the independent Standards and Spec axes retain all validation and acceptance
ownership. No compiler was run for this correction.

## Actual failure and immutable input

Focused10 actually closed with exit 1 at clean, unchanged central candidate
`8ba7ae11a657e8a4af025f60b4e1a54dddb3c512`. Its outer log is 19,463 bytes and
170 lines, SHA-256 `35f0f9ea785a94ec66026c0483d566be1a611efb9a699362d0a5b5eed3941ccd`.
The closed record reports a successful individual build of the Tail main example
in 331 seconds. Uniform failed with 23 error headers at ten source sites. Neither
the individual Tail pass nor this failed focused run is a full acceptance check.
The historical execution session is closed and was not polled by this author.

The complete 93-line Uniform diagnostic block was read. Its exact 6,925-byte
copy is `actual-diagnostics.txt`, SHA-256
`284b94feb0773ef436d7de66658ea3932f29ff6234d5b3d01853de42fd211175`.
The actual result and secured-terminal records were read in full; their identities
and the verified complete log identity are in `start.json`.

The isolated worktree began clean on `work/fdsa-ch02-uniform-input` at
`c4355db67f6006f58496cc10c2eca1c75ef1aa95`. Its complete 352-line example is
byte-identical to the actual failed input: Git blob
`cc0432e8fc56f76380a1e48259954cd559937a1b`, SHA-256
`83e4407bec884caeb3d1ff285a9e6932f52a9f84431f2a5874e322e18773aeb5`.
The 789-line Uniform core is also byte-identical at these two commits and is not
edited. No other repository source is part of this correction.

## Repairs and preserved connections

| Original site | Actual diagnostic | Correction |
| --- | --- | --- |
| 71 | Unknown `List.length_eq_one.mp`, followed by failed destructuring | Use pinned `List.length_eq_one_iff.mp`; retain the actual restricted-order length and singleton-cost argument. |
| 89 | Generated `Fintype` completeness rewrite fails at the list/multiset nodup coercion | Use the separately authorized explicit `instFintypeLabel` over exactly the four unchanged constructors, with completeness by constructor cases and ordinary `simp`. |
| 117 | Thirteen `No goals to be solved` diagnostics | Use `simp_all` after the existing constructor cases; retain precisely the selected-support and key-equality hypotheses. |
| 191 | Remaining ENNReal equation `3⁻¹ + 3⁻¹ = 2 / 3` | Prove the same sum in NNReal and transport with `coe_add`, explicit nonzero-denominator `coe_div`, `coe_one` and `coe_ofNat`. The event-union/disjointness and actual head-mass applications remain. |
| 204 | Cannot synthesize `IsFiniteMeasure law` | Unfold the existing `law` alias only inside the same local conditioned-probability proof, then apply the same `cond_isProbabilityMeasure` and proved positive head mass. |
| 253 | Rewrite cannot match opaque `comparator` alias | Unfold `comparator` locally, then use the same `meanBy_eq_closedForm`, selected-key proof and selected cardinality. |
| 266 and 273 | Conditional-integral rewrites cannot match opaque `law` alias | Unfold `law` locally; retain `child_integral_cond`, the actual child containment, child identities and `meanBy_empty`. |
| 291 and 319 | `List.nodup_range` is applied as though `n` were explicit | Supply `(n := n)` to the exact pinned implicit parameter; retain the existing map/injection and arbitrary-payload range arguments. |

`diagnostic-mapping.json` retains every actual error header, the affected
declaration, original source site and proposed correction. These are source
repairs, not compiler-confirmed resolutions.

## Explicit Fintype repair and generated-declaration accounting

The pinned 200-line `Mathlib/Tactic/DeriveFintype.lean` was read completely and
verified against Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Its source SHA-256 is
`ccc5fecbe99adf96964457156d006c07af730e83ec7af678dc90e289745c2e4e`.
For an enum, `mkFintypeEnum` produces an enumeration list, two accompanying
theorems, then a Fintype instance whose completeness proof rewrites
`Finset.mem_mk`, `Multiset.mem_coe` and `List.mem_iff_getElem?`. The actual error
arises in that generated final proof, outside an existing user theorem body.

Root explicitly authorized the smallest explicit instance over
`{Label.high, Label.low, Label.middle, Label.outside}`. The inductive declaration
and its four constructors remain verbatim, and `deriving DecidableEq` remains.
No order, inhabitance/default instance or additional mathematical assumption is
introduced. All four existing measurable-space/singleton instances are unchanged.

The entire change is therefore **not wholly proof-body-only**. The new explicit
source declaration is `Examples.UniformQuickSortMean.instFintypeLabel`, with
source type `Fintype Label`. The failed deriving route's three helper names are
not recreated:

- `Examples.UniformQuickSortMean.Label.enumList`.
- `Examples.UniformQuickSortMean.Label.enumList_getElem?_ctorIdx_eq`.
- `Examples.UniformQuickSortMean.Label.enumList_nodup`.

Before the replacement, immutable `git grep` searches for the literal `enumList`
over all tracked `*.lean` paths at both the isolated base and failed central
candidate returned no matches. This includes all three helper-name strings.
`generated-helper-search.json` preserves both exact commands and actual exits.
It is a bounded project-source reference search, not a compiled-environment scan.
Root approved omission of those unused deriving-only helpers after that check.

The new instance needs its own actual fully explicit printed type and inventory
accounting. Root and Standards will update the prepared program after the exact
commit. No printed-type credit or numerical kernel-declaration delta is inferred
from this source inventory; the exhaustive audit still covers actual generated
and private kernel-safe declarations.

## Complete source readback and preservation

The original 352 lines and unchanged core's 789 lines were read in the preceding
bounded Uniform preparation; their byte identities were verified here against
both immutable inputs. This correction's complete 366-line successor and full
103-line diff were read back after editing.

Source comparison confirms all 45 existing theorem headers are byte-identical.
All seven existing definition blocks, four existing explicit instance blocks,
five imports, two options, namespace/open commands, universe declarations and
variables are unchanged. Only the nine mapped existing proof bodies change,
together with the separately approved Fintype deriving replacement. The source
inventory has 57 explicitly named declarations before and 58 after; those counts
exclude automatically generated declarations and are not proof-audit counts.

All expected values and public-law connections remain: empty/singleton and pair
tariffs; the actual 21/25 conditional costs and one-third head masses; the
two-thirds event mass; both derivations of 71/3; outside key collision; actual
empty children; arbitrary payload occurrences; equal-key quadratic boundary;
and growing-family exercise/literal bounds. No theorem premise, result, source
cost model, distribution or conditioning event was changed.

`git diff --check` passed. A source marker search found no `sorry`, `admit`,
`axiom`, `unsafe`, `partial`, `native_decide`, `trustCompiler` or `implemented_by`.
These inspections do not replace elaboration, printed-type review or the audit.

## Instructions, remaining gates and write boundary

The repository AGENTS, implementation and example-driven-development instructions,
review loop, applicable README environment/build/audit sections, domain/glossary,
architecture guidance and relevant ADRs were read. The frozen Chapter 2
requirements and original probability dependency handoff were read, preserving
the complete C2 and shared-unit scopes. The historical Chapter 1-unaccepted
wording in frozen requirements is superseded by accepted R; no requirement or
source obligation is removed. Truncated batched instruction passages were reread
in bounded outputs before implementation; the read ledger records that boundary.

The Nix waiver does not waive exact pins, the qualified native profile, proof
restrictions, complete candidate check/audit, both independent reviews or immediate
candidate verification. No compiler, cache, central worktree, foundation worktree,
process, existing control report or unrelated source was touched by this author.
The exact foundation remains separately owned by root. The current acceptance
sequence and Chapter 3 queue remain unchanged.

The local commit identity and clean final status are recorded in `receipt.json`
and `commit-record.json`. The successor remains **uncompiled**. All required
validation, independent final review, verification and acceptance remain pending.
After this bounded handoff, source and provenance writes are held for checkpoint0097.

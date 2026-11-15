# C03-CHOP-MAP-ELAB-001 — proof-only correction

Exact candidate `bd4e273f82de2c2bab2a69d84c2f8daea310eeec`, tree `ed3211ed959af55ee7ccea9ff51bd33e17a6eeea`, parent `557d00df979d95788f093e55551abd02f17dd049`, branch `work/fdsa-ch03-mom-execution`. Worktree is clean. Actual local commit `fix(resources): normalize measured median map proofs (#174)` closed0 (`e91988`) with command-local ChatGPT identity.

## Actual failure and readback

The original557d00d focused attempt1 closed1: owned9908, terminalc9803a, complete root closuref09667. The complete8261-byte log has SHA256 `3aabe6cd6f1f01c4bfb66f4cc3053262b4ea445e6d8e0147c5c8b1f265206e0a`; author read it fully in60c042 and read result/terminal/closure fully in4e03fc. Applications.Resources.Chunks and Examples.ChunkCalls passed. SelectionMedians had three proof groups: dependent-match reduction, attached map-sum normalization, and a Nat scalar coercion. Examples.SelectionMedians was not established. Historical session9908 is closed and must not be polled. The copied verification still names acceptedXRc1ce, not this candidate or a new full gate.

## Correction scope

Only `Applications/Resources/SelectionMedians.lean` changed, with10 inserted and3 removed lines. Three proof bodies changed:

1. `slowMedianValueRun_of_some` now explicitly splits the unchanged dependent match. Its impossible none branch contradicts established nonemptiness; the actual some equality yields the same payload by constructor injectivity.
2. `mapSlowMedianRun_cost` now applies the existing `List.attach_map_val` equality explicitly under the sum-plus-entry observation. There is no new traversal or observation term in the execution.
3. `mapSlowMedianRun_bound` uses the pinned `Nat.nsmul_eq_mul` specialization, avoiding the redundant Nat cast introduced by the generic identity. The standard finite-sum bound, callback bounds and final polynomial remain unchanged.

Full corrected source read309c0c, complete diff reade7416e, and pinned Nat specialization readfb3087 are recorded. The read-only broader rg7f3403 found the current lemma but exited2 because three guessed paths were absent; it is not a compiler result.

All68 public headers, all four execution definitions, all examples and eleven other source files remain exact. The scope remains4 definitions and64 theorems, with no private or anonymous declarations. All36 old records remain exact. Generic group size, zero/empty behavior, actual callbacks, both chop traversals, exact costs,47/48/10n+48/15n+49 bounds and every case target are preserved. No restriction, suppression, hypothesis, fallback, cost law or mathematical weakening was introduced. No F commit or import was added.

## Next gate

Root should focus the same full four-module scope on this immutable candidate:

- `Applications.Resources.Chunks`
- `Applications.Resources.SelectionMedians`
- `Examples.ChunkCalls`
- `Examples.SelectionMedians`

The exact68-name explicit-@ input is unchanged and is reused from `../chop-map-slice1-20261104/ChopMapStatements68-candidate1.lean` (4076bytes, SHA256 `3e1de6e46c407771794f4b315b2c8836e35d5c9cc141d4ca167a554d5a2fd4ac`). The new inventory proves all68 headers match that preparation. Actual printed types remain pending.

Only source/identity/header comparisons, exact diff and whitespace checks, staging, the local commit and clean-state checks were executed by this author. The correction has not been compiled; C03-CHOP-MAP-ELAB-001 is not claimed resolved by a new terminal. Root remains sole compiler owner. Full candidate checks, exhaustive audit, independent full-scope axes, immediate verification and integration acceptance remain required. Nested execution and actual run≤F remain outstanding.

Source and own provenance writes are HELD after author-hold.json pending the new focused terminal and root release.

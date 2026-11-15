# Universal endpoint worst-path handoff

Candidate: `3c04405d207a7b8c6f7452598da88fa3a7a05ac3`  
Tree: `d8daeb1fd680f7b1b22391517391d3aebcafa458`  
Parent: `2b5ff20504d8811587859e6eb3351cb1598a4504`  
Branch: `work/fdsa-ch03-random-selection`  
Commit: `feat(selection): derive universal endpoint worst paths (#174)`

The worktree is clean. The commit adds only `Applications/Resources/RandomSelectionWorst.lean` and `Examples/RandomSelectionWorst.lean`. All 16 prior random-selection source files remain byte-identical. Root remains the sole compiler owner. **Neither new module nor its statement input has been compiled by the author.**

## Mathematical scope

`EndpointTrace` is a recursive structural proposition, not an executor. It records the actual current size and occurrence index, minimum policy at positive worker rank / maximum policy at zero, the actual `stepRun` child, and a singleton terminal state at the end of the trace. It contains no assumed target equality, probability, work, source-cost or distinctness field. Target success and valid rank are derived from actual step semantics.

The universal witness keeps **every arbitrary distinct input and every valid worker rank**. Its induction uses the existing exact endpoint child, actual `prepend`, and `run_child_atom`; factorial algebra uses the restricted ENNReal inverse-product law with finite-cast side conditions. It derives the complete Outcome atom `1/n!`, then derives support, then invokes the checked on-support `traceLaw_atom` bridge to obtain the exact **projected trace probability** `1/n!`. It retains `n` actual trace entries, `2W=n(n+1)`, `W=n(n+1)/2`, the actual sorted-index return value, and the existing source transport `W≤T≤9W+2`.

The natural-range family quantifies every positive size and every valid rank, with explicit actual source inequalities `n*n≤2*T` and `T≤11*(n*n)`. The unbounded theorem chooses `n=B+1>B`, retains every valid rank, and gives actual cost `T>B`. The universal example proves **W** is maximal among actual supported outcomes. No theorem asserts that this endpoint path maximizes exact **T**.

## Expected cases and connected clients

The original independent model, 719-case historical output, first 14 stage09 expected cases and all previous source examples are preserved. The new range-four interior case was calculated before source: value2, trace `[(4,0),(3,0),(2,1),(1,0)]`, W10, T48, full/trace mass1/24. It is now connected through actual step and atom laws, with a separate public family-bound client.

The unsorted interior path `[3,1,2]`, rank1 retains value2, W6, T33 and full/trace mass1/6. The signed five-element path retains value5, W15, T67 and mass1/120. Requested endpoint ranks0/2, singleton, empty, invalid singleton, universal invalid-rank exclusion, and the all-equal one-step countercase are included.

An additional pre-source boundary from the unchanged model is `[1,1,2]`, rank2: actual trace `[(3,0),(1,0)]`, value2, W4, T23 and mass1/3. The new checked client establishes a structural endpoint path although the input is not Nodup. Thus the structural predicate alone does not imply distinctness, one-element decrements, triangular work or factorial mass. The universal theorem retains its explicit Nodup premise.

## Statement and source review

The complete inventory has **335 authored headers: 314 public, 21 private, 26 definitions/abbreviations** across 18 sources. This stage adds 25 public declarations, three private helpers and one structural definition. `EndpointTrace` itself is included in the explicit-@ program; no inductive constructors were authored. These are source counts, not generated declaration or kernel-audit counts.

All 28 new headers, surrounding contexts, three private derivations, quantifier order, domains, conclusions and case connections were read and assessed. The full core was read in `7cf849`, examples in `faa16d`, and all new recorded headers/reviews plus the final one-line arithmetic-explication delta in `c3d282`. The existing 307 headers/contexts and 25 definition bodies are unchanged. There is no sorted-only or endpoint-requested-rank narrowing, payload inhabitation/countability premise, artificial independence, assumed probability, assumed desired cost law, replacement larger-side process, or linter suppression.

`Statements314-stage09.lean` has 314 explicit-@ checks and preserves the previous 289 names/order plus the exact six print options. It is 18,231 bytes, SHA-256 `5d4b19d87d87761158e03b322c87834171c9bb7e5fb1e5504399bb1c48a38996`. The precommit preparation record is retained as written; the separate candidate-binding record supplies the exact immutable commit/tree. No elaborated type output is fabricated.

Source bindings:

| Path | Bytes | SHA-256 | Git blob |
| --- | ---: | --- | --- |
| Applications/Resources/RandomSelectionWorst.lean | 10712 | b766d2f5a5e44cad32c35c709ec2f5b878a54b81d3fd5b17ac90e25e1b2f2b49 | 03b683c8040bdcc7b92ac6898f1464a77c61d360 |
| Examples/RandomSelectionWorst.lean | 12775 | ea06643849f8d958d17659d26886e132fc92d471008d1fa7c1455af808ddf0cb | daccfebe9a1f0b6b57534562d28f8c13d4c567ca |

The staged whitespace check returned actual exit0 (`2fc056`), and the local commit returned actual exit0 (`b58607`). Those checks provide no Lean validation credit. The original Karp1994 source remains inaccessible; no source recovery or quotation is invented.

## Validation boundary and requested next action

The exact parent trace pair and its 23 delta statements passed under root's qualified compiler, with all actual closed evidence preserved. All earlier failed/interrupted histories remain exact, including the known-native-failure/missing-transport-terminal distinction for trace attempt1 and the different unknown-terminal drift attempt2. No historical process identifier was polled.

Requested root focused targets:

- `Applications.Resources.RandomSelectionWorst`
- `Examples.RandomSelectionWorst`

After the exact pair and actual type checks, the full immutable candidate check/audit and both independent axes remain required in the existing Chapter3 loop. This handoff claims no whole-chapter acceptance. **All source and provenance writes are held after the final author-hold record, pending root's actual result or explicit release.**

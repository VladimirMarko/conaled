# Frozen integer-lattice author trial

Two independent agent authors completed the same integer-order task against
`a38e05358d47f1739aa2f1fbcae8f9cc0d120f86`. The native author additionally
constructed the selected law-bearing paths and complete recovery witnesses in
both models. Neither attempt required a library repair or a higher resource
limit. This is evidence that another author could use the frozen interface for
this case; it does not establish a general authoring advantage.

The [protocol](native-lattice-author-trial/protocol.md) was frozen before either
assignment (SHA-256
`fd834e2f03128c234ad9d493afc4f43237c62af300a663a5def32a16a4d19377`).
It fixes the mathematical task, assistance, success criteria and budgets.
The independent [direct](native-lattice-author-trial/direct-attempts.md) and
[native](native-lattice-author-trial/native-attempts.md) archives retain source
versions, failed checks, exact commands, measurements, harnesses and author
reports. Their final checked sources are integrated without changes as
`Examples.LatticeAuthorTrialDirect` and `Examples.LatticeAuthorTrialNative`.
The archives are evidence for the frozen trial; later library changes must not
rewrite them into a different experiment.

## Task and independence

The usual integer lattice admits translation `z ↦ z + 3`, with inverse
`z ↦ z - 3`. For arbitrary `x ≤ y`, the dependent pair becomes `(x+3,y+3)`
with its order witness. Inverse transport recovers the whole pair, and the gap
`y-x` remains unchanged. The selected strict pair `(-2,4)` becomes `(1,7)`;
zero becomes three. Meet and join are preserved. Negation is a bijection but
fails monotonicity on `0 ≤ 1`, so it cannot preserve this ordinary lattice.
These arithmetic expectations were specified before implementation, independently
of the native API. The infinite chain and gap theorem extend the retained
Boolean and geometric worked cases.

The two fresh-context authors were assigned the repository-approved
`gpt-6-astra`/`high` configuration. Neither authored #621 or #691. Runtime model
metadata beyond the selected configuration was unavailable and was not inferred.
The direct author could use ordinary Lean/Mathlib, but could not inspect the
native implementation or reports. The native author could use the frozen public
API, its dependencies and documentation. Neither could see the other's solution,
request proof help, use a further agent or change the library. The only
clarification concerned the unavailable exact assignment timestamp. Both stopped
proof work at their first successful final check.

Each had a 20-minute bound, at most 25 Lean invocations, a 30-second bound per
invocation and an eight-minute cumulative checking bound. Local budget
experiments were permitted by the protocol but were not needed. Both retained
depth 512 and 200,000 heartbeats, using the pinned Lean 4.35.0 and dependency
manifest at the baseline. No transparency or kernel-checking override was used.

## Checked results

`DirectTrial692.transport` implements ordinary subtype transport through an
`OrderIso`. Its two inverse theorems recover whole proof-bearing pairs.
`transport_translation`, `gap_translation` and the selected observations establish
the common task. `negation_not_monotone` is a proved rejection, not a failed
attempt to encode negation.

`NativeTrial692` independently supplies the integer isomorphism and arithmetic
observations. Each native model constructs actual admissions and a named
`latticePathData` package, with equations identifying the exact source, target
and law-bearing path. `selectedRecovery` retains the complete selected structured
equivalence; `pathRecovery` retains the whole native path recovery.
`witness` uses `pathOrderedPair`, hence actual native transport along the
law-bearing path's carrier projection. `witness_direct`, `witness_gap` and
`witness_inverse` recover the complete dependent values and common arithmetic
observations. `nativeSolution_recovery` recovers the entire original native
solution. The decoded meet/join fields are checked, and
`negation_native_rejected` rejects the actual native preservation family.
`decoded_models_agree` compares complete decoded dependent values across the
models; it does not equate independently selected ua paths.

Both routes establish the common specification. The native route has additional
internal path and recovery capabilities, so their total implementations are not
equal-work benchmarks. Whole subtype equalities use Lean's proof irrelevance;
native recovery homotopies retain the selected data required by the existing
contracts. No arbitrary higher-coherence theorem or internal universe of
propositions is claimed.

## Measurements and failed attempts

| Observation | Direct | Native |
|---|---:|---:|
| Lean invocations, including failed checks | 4 | 3 |
| Cumulative command wall time | 5.571 s | 4.764 s |
| Maximum reported child RSS | 3,435,348 KiB | 3,607,992 KiB |
| First locally recorded UTC clock | 00:12:41 | 00:13:04 |
| Successful check UTC | 00:14:17.746811 | 00:15:23.061415 |

All times are on 2026-11-24. The exact assignment timestamps were not captured;
reading instructions preceded the first local clock observations. The intervals
between those observations and success are therefore lower bounds on author
elapsed time, not precise assignment-to-success durations. Both attempts ended
within their bounds, but these records do not support ranking authoring speed.
Wall measurements include `direnv`/Lake launch overhead; RSS includes imported
libraries and is not an allocation count. The archives record CPU counters and
negligible lock waits. These are single runs, not distributions.

Both authors encountered Python unavailable outside the development shell and
an external-source invocation missing Lean's `--root`. The native author also
found `/usr/bin/time` unavailable and used Python child resource accounting.
These are environment failures. Both initially gave `omega` inverse goals whose
function applications needed explicit arithmetic `change` statements. The direct
author also needed that step for order reflection. These are local encoding
failures; none establishes a mathematical obstruction or a Lean defect. Failed
compiler logs can contain `sorryAx` for unsolved goals; those runs failed and
are retained only as trial evidence. The successful sources contain no admitted
proofs or additional axioms.

## Adoption and remaining work

Retain direct `OrderIso`/subtype transport for clients needing only integer-order
observations. Retain the native API for clients needing internal law-bearing
paths and complete selected recovery: this author reused its existing proofs
without a library change. The native author used the geometric worked example's
package pattern; documentation and examples were part of the permitted interface,
not proof assistance supplied during the trial.

Shared preparation in #621/#691, including admissions, descriptor interpretation,
law semantics, total structure identity, decoder contracts and package boundaries,
is excluded from measured client effort. The new client still supplies the
isomorphism, arithmetic observations and rejecting example. Both native adapters
need separate instantiation and observation declarations; this trial does not
justify a new abstraction solely to shorten those declarations. Maintenance of
the two retained clients and underlying library remains a cost.

Adopt the checked integer case as a regression consumer and retain both routes.
No missing contract was exposed that requires a prerequisite repair or a new
issue. #680 owns universe generalization, #687 selected-equivalence coherence,
and #688 broader native model comparison. These capabilities remain separate
from this successful bounded author trial. #235 owns future usability assessment;
further productivity claims need independently frozen tasks and authors rather
than replaying this now-known example. The result neither mandates migration nor
ranks unexplored signature or correspondence designs.

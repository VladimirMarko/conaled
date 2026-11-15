# Upstream probability intake: 04514fc1

Date: 2026-11-14. Status: read-only source assessment; no compiler run, source edit, acceptance approval, or new textbook coverage is claimed.

## Exact scope

The assessed upstream change is [`983d0b6b602b71541f182737011621a8805be27b` → `04514fc144dcebdd2b6d4aea5faf2f9cbf229362`](https://github.com/VladimirMarko/conaled/compare/983d0b6b602b71541f182737011621a8805be27b...04514fc144dcebdd2b6d4aea5faf2f9cbf229362). GitHub's exact-commit compare reports three commits, eight paths, 1,004 added lines and seven removed lines. The three new Lean modules total 432 lines; one public import and four documentation paths complete the delta.

| Commit | Subject |
| --- | --- |
| `c64da5c9fe0410321d847d8419664680c9d927d4` | Research mathematical suppression and its formal contracts |
| `72da80957902b175b8df9f09ea06b683a25f31b2` | Clarify suppression as derived reasoning representations (#550) |
| `04514fc144dcebdd2b6d4aea5faf2f9cbf229362` | Realize productive rational Markov streams (#542) |

The comparison changes no `AGENTS.md`, skill, architecture guide, checker, toolchain, dependency manifest, Nix pin, or existing textbook implementation. The accompanying JSON records the eight resulting blob identities. The source comparison establishes the delta's scope; it does not establish successful integration compilation.

The prior textbook candidate inspected for prospective connections is `16440863ddb14d95c402ce65498e22497e246e72`. This note does not change the original full-spec review base or declare the new upstream pin merged.

## What the new Lean actually supplies

### One continuing rational-table execution

[`TableProducer.lean`](https://github.com/VladimirMarko/conaled/blob/04514fc144dcebdd2b6d4aea5faf2f9cbf229362/Applications/Probability/TableProducer.lean) builds on existing `PreparedRow`, `RowChain`, `Progress.Producer`, `Progress.Delivers`, and probability productivity interfaces. A producer state carries the current semantic state together with the row sampler's actual cursor and incomplete rejection block. A completed transition emits its new state, including a self-transition, then starts the next row at the returned cursor. Silent steps retain the unfinished sampler state.

The bridges `evaluates_of_row` / `row_of_evaluates` connect next-emission evaluation to an actual row evaluation, including arbitrary partial row states. `delivers_of_trace` / `trace_of_delivers` connect finite producer deliveries and finite-chain traces in both directions, retaining the ordered outputs, final state and cursor. They account explicitly for the finite-chain machine's one terminal administrative transition. `delivers_work` identifies producer steps with inspected bits and cursor advancement.

The subsequent `prefix_mass` and `endpoint_mass` recover the rational table's path and iterated-kernel laws. `almostSureProductive` and `ae_coherent_prefixes` give one conull set on which this same continuing producer supplies a coherent family of every finite prefix. This is a simultaneous same-tape result; no independent restart is substituted for the continuing execution.

The probability claims require the stated finite carrier, decidable equality, explicit enumeration `Fin m ≃ α`, rational transition table and fair-tape law. Bit inspection counts do not include arbitrary arithmetic, table lookup, physical entropy, host runtime or memory costs. [Scope documentation](https://github.com/VladimirMarko/conaled/blob/04514fc144dcebdd2b6d4aea5faf2f9cbf229362/docs/probability.md).

### Joint finite-block stationarity

[`TableProducerStationarity.lean`](https://github.com/VladimirMarko/conaled/blob/04514fc144dcebdd2b6d4aea5faf2f9cbf229362/Applications/Probability/TableProducerStationarity.lean) defines a block by dropping a finite number of outputs from a longer actual delivery of the same producer. Its decomposition retains the row's returned cursor; `block_succ_mass` uses the existing stopped-mass/fresh-suffix theorem to justify composition.

`stationary_blocks` preserves the entire ordered finite-block law under any finite emission shift. Its generic hypothesis is the displayed stationary equation for weights `π : α → ℝ≥0∞`; the theorem itself does not assume that these weights sum to one. The finite Metropolis–Hastings specialization `producer_stationary_blocks` uses the normalized target and its established stationarity. Initial target selection is represented by the explicit independent mixture over tape probabilities.

These are joint-law statements preserving correlations within each block. They supply neither independent successive outputs nor convergence, mixing rates, burn-in, confidence intervals or empirical accuracy.

### Cases that distinguish the intended observations

[`Examples/TableProducer.lean`](https://github.com/VladimirMarko/conaled/blob/04514fc144dcebdd2b6d4aea5faf2f9cbf229362/Examples/TableProducer.lean) includes an unfinished block resumed from its actual state, rejection followed by retry, two consecutive emissions, self-transitions and an asymmetric MH stationary pair. Its pair `(false,true)` has probability `1/4` after every finite emission shift under target initialization.

The example also supplies an exceptional all-true tape that never completes a deterministic singleton sampler, separating almost-sure productivity from productivity on every tape. `changes_not_productive` shows that discarding unchanged states destroys productivity on a singleton. The completed MH transition table does not expose acceptance flags: an unchanged state can be an accepted self-proposal or a rejection. Those are different observation policies with different obligations.

## Architectural fit and useful textbook work

The implementation reuses concrete row execution, existing progress semantics and probability composition laws. It connects implementations by proofs of retained observations; it does not introduce a competing sampler semantics. This matches the repository's [architecture guidance](https://github.com/VladimirMarko/conaled/blob/04514fc144dcebdd2b6d4aea5faf2f9cbf229362/docs/agents/architectural-quality.md) and [composition ADR](https://github.com/VladimirMarko/conaled/blob/04514fc144dcebdd2b6d4aea5faf2f9cbf229362/docs/adr/0010-composition-and-proof-audit.md).

The surrounding probability interface already interprets tables through `RawMap` / `MapLaws` into Mathlib's Markov category. Its documentation explains why arbitrary stochastic operations cannot be forced through the cartesian frontend: equal marginals do not identify joint distributions. Shared sampling and independent sampling must remain distinguishable. [Probability architecture](https://github.com/VladimirMarko/conaled/blob/04514fc144dcebdd2b6d4aea5faf2f9cbf229362/docs/probability.md).

There are concrete prospective FDSA clients. At the recovered candidate:

- `Applications/Resources/RandomSelectionRun.lean` (blob `4af2a079ad55005657eeac2eaf4d3dd2a3a3ac11`) models fresh uniform occurrence-index choices, the actual choice trace and source-call observations. Its PMF recursion terminates by strict decrease in input length; valid-rank correctness includes duplicates. `run_source_bridge` explicitly excludes a random-bit charge.
- `Applications/Resources/RandomQuickSortMean.lean` (blob `a9ce110d5aca6f04cc8d68cfd1ef5238832dbc0a`) proves integrability and expectation equations for actual measured run outcomes. Its tariffs explicitly omit pivot sampling, index lookup/removal and random-bit implementation costs.

A useful future integration is therefore an explicit realization theorem relating tape-based rational choices to these existing PMF runs, preserving occurrence choices, shrinking input domains, ranks, duplicate behavior, source costs and the unused tape suffix. Add sampling costs as a separate proved observation. The finite row sampler and stopped-suffix laws may be the smallest sufficient interface; these terminating algorithms do not acquire a need for stationary infinite streams merely because that interface now exists.

That bridge is a proposed mathematical obligation, not a result supplied by this upstream delta. Neither VFA nor PFDS gains automatic chapter coverage. PFDS's sharing, suspension, persistence and amortized-cost obligations also remain distinct from probabilistic producer productivity.

## Process implications for continuing mathematics

The [current README](https://github.com/VladimirMarko/conaled/blob/04514fc144dcebdd2b6d4aea5faf2f9cbf229362/README.md) explicitly allows focused development with `lake build <actual-module>`. Its routine acceptance command remains `./check.sh`, covering source policy, public-module coverage, all integrated compilation and the exhaustive axiom audit. Candidate acceptance adds `--candidate HEAD` and immediate `--verify-candidate HEAD` against stable inputs.

The user's explicit instruction permits delegating that final full validation to the receiving integrator's normal environment. Record it as **deferred full validation of the exact final candidate**, including a real terminal result, complete audit and required reviews. Focused checks and mathematical development can continue in the meantime. Neither upstream inclusion nor delegation is evidence that this combined candidate has passed.

[ADR 0010](https://github.com/VladimirMarko/conaled/blob/04514fc144dcebdd2b6d4aea5faf2f9cbf229362/docs/adr/0010-composition-and-proof-audit.md) already explains why routinely rebuilding unchanged sources is costly as the library grows; routine acceptance uses Lake's dependency tracking, with fresh validation for specified circumstances. This delta changes no build tooling or pins and introduces no new tooling-change trigger. Any separately recorded integrity concern still follows the existing runbook. Thread limits, host quotas and runtime estimates belong to the separate build-resource assessment.

The [example-driven-development skill](https://github.com/VladimirMarko/conaled/blob/04514fc144dcebdd2b6d4aea5faf2f9cbf229362/.agents/skills/example-driven-development/SKILL.md) requires intended statements, actual public-theorem connections, meaningful cases and scope review. Kernel acceptance cannot establish that a theorem captures the intended textbook claim. Continue the existing implementation/review loop and local issue tracking; use these requirements to prioritize semantic and cost bridges.

Finally, [mathematical-suppression.md](https://github.com/VladimirMarko/conaled/blob/04514fc144dcebdd2b6d4aea5faf2f9cbf229362/docs/research/mathematical-suppression.md) is a research note about derived representations for search and discovery. It explicitly adds no Lean definitions or tests and selects no new interface. Its relevant lesson is to retain source identities, hypotheses and observations, distinguish recoverability from lossy preservation, and verify suggested connections against the original mathematics. It neither changes validation policy nor justifies erasing distinctions to make textbook developments appear equivalent.


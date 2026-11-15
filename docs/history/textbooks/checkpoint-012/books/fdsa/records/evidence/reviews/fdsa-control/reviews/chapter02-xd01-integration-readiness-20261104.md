# XD01 integration readiness for the natural-run client

Read-only preparation, 4 November 2026. This adds verified current ancestry
and a concrete source-path lemma to the existing natural-run operation plan;
it is neither an integration nor a source/validation approval. The author
worktree remains clean at `3d5238737299cd365f36e39e5e8a61d34138cba5`.
No source, ref, index, dependency, cache or build operation was changed.
This dedicated handoff is the only write in this preparation.

## Minimum history and files

The complete frozen XD01 requirements, preflight and its retained provenance
erratum, candidate/source-assessment record, ticket, shared integration plan,
current Chapter 2 requirements/clarification and exact candidate core,
examples and documentation were inspected. Read-only Git confirms:

| Role | Exact commit |
| --- | --- |
| Accepted Chapter 1, R | `07e480f6ec9958d4975bb90151005b84f2907614` |
| Exact pending foundation, F | `f17cc6b1a2bf44215b16202ed0fcee2b5c130761` |
| Original foundation prefix, P | `c80eec92f5458eccfd1c34c8314d666c2a1e3847` |
| Common fork of XD01 with both R and F | `a14977b9e316cc484ffad8a470d26b15615956c0` |
| XD01 implementation commit | `ffeaf8aed84184f49a13acb5c84e1fd608c9b7e8` |
| XD01 documentation correction / exact tip | `62809ced86c561c7a6cce8b71e727177a3f17fb8` |

Only the last two commits are absent from R. They introduce exactly these
five paths: `Applications/Resources/DifferenceListCosts.lean`,
`Examples/DifferenceListCosts.lean`, `SquareApplications.lean`,
`docs/research/fdsa-difference-list-costs.md`, and
`docs/research/fdsa-reconstruction-map.md`. The correction changes only the
difference-list note; preserve it with the implementation and retain
XD01-DOC-001. No subset omitting examples, public exposure or provenance is a
complete acceptance scope. The actual root import is
`import Examples.DifferenceListCosts` in `SquareApplications.lean`.

The exact XD01 tip contains no insertion/list-foundation, potential, affine,
probability or tree draft beyond its Chapter 1 fork. P is not its ancestor.
F has both R and exactly P in its ancestry, through merge `0c93725` and
corrections `9875bfd`/`f17cc6b`. Substituting `c28ba718` or a later shared tip
would add a different scope and is unnecessary.

Direct imported project inputs `CallCount`, `Workload`, `Measured` and
`SquareKit.ListFusion`, plus `lean-toolchain` and `lake-manifest.json`, have
identical Git blobs at the fork, R, F and XD01. In particular, the accepted R
corrections changed CallComparison/CallModels/SharedDemand, not XD01's imported
interfaces. This establishes source compatibility inputs, not elaboration.

Rechecked XD01 SHA-256 identities:

- Core: `567683626b9a46d07c465ceb44faaafc941e2dc1c83491b093599ca7f8c698a5`.
- Examples: `09165e6a1ccb0b0e45b7ddc6083883aa5bf67bc931c59ff44707d1726ffbe102`.
- Corrected note: `fd01432541c9b27ad83def6192e4a3b75d6b77ae7490ec11a2bf665324f1246e`.

## Reconciliation and gates

XD01's source imports need accepted R and pinned Batteries, not XP01 or the
foundation additions. The user's first outstanding acceptance nevertheless
remains exact F. Complete that candidate's retained gates without changing it;
then a new integration candidate can preserve F and merge exact XD01 history.
Do not reset/rebase saved branches or replace accepted files from the older
XD01 snapshot.

The inspected changed-path intersection is only `SquareApplications.lean`
and `docs/research/fdsa-reconstruction-map.md`. Retain the accepted call-model
imports, all four foundation example imports and the new XD01 import. Preserve
F's accepted Chapter 1 wording, Chapter 2 status and every foundation section
while adding XD01's complete section. No merge/conflict experiment was run.

XD01 has author-side source/architecture assessments and the implemented
provenance correction. Its focused elaboration, full immutable candidate
check/audit, final independent Standards/Spec axes and immediate candidate
verification remain pending. The old reports' historical compiler sessions
are not live sessions. A future candidate must retain the complete frozen
requirements, cases and source correction; the existing source assessment
is not either final review axis. Keep the recorded Chapter 1 fresh baseline
and apply the actual normal/fresh triggers to the new candidate.

## Concrete ascending-client proof boundary

Reuse `Builder`, `Rep`, `AppCost`, `createSingleton`, `pushRun`, `buildFrom`
and `toDList_pushRun` directly. The future actual mutual operational scanner
should take an ordinary `Builder` at an ascending entry; Rep/AppCost proofs
belong in its laws, not in a new closure datatype. Its initial ascending
branch binds `createSingleton first`; each continuation binds `pushRun current
f`; each terminal/restart branch invokes the actual returned callback on
`[current]`. Its emitted result must feed the real restarted scanner.

The following additional lemma makes C02-111's source-path correspondence
concrete. It is a proposed proof target, not a new checked result. Under the
existing proposed operation tariff, suppose every comparison on
`a :: middle ++ [last]` continues ascent. Set:

```text
t = middle.length + 1
built = buildFrom (a :: middle) f
applied = built.1 [last]
```

Prove directly from the actual ascending branch equations:

```text
value(ascOps lt a f (middle ++ [last])) = [applied.1]
cost (ascOps lt a f (middle ++ [last]))
  = built.2 + applied.2 + 2*t + 3
```

The extra terms count each continuation's worker entry/comparison, followed
by the terminal entry, singleton suffix cell and outer emitted-run cell.
The empty-tail base is separately `([value(f [last])], cost(f [last])+3)`.
Neither statement needs Rep or AppCost: the application retains its actual
suffix and observation. Prove this by continuation induction using
`buildFrom_cons`, not by equating only the final DList values.

Then, for an actual ascending source run `first :: middle ++ [last]`, bind
`createSingleton first` into `buildFrom middle`. Its construction and later
application counts each become `1+2*middle.length`, using the existing
separate laws. The preceding path lemma connects this exact construction
to the scanner. With run length r=middle.length+2, derive `count+3=2*r`
before `count=2*r-3`. This includes the two-element run; empty/singleton
scanner inputs bypass the builder path. It also supports the planned
ascending scanner count `6*r-5` for r>=2 under that declared tariff.

For arbitrary supplied builders, use Rep only for the value bridge to
`ascBy lt a (toDList f prefix rep) ys`, with `toDList_pushRun` at each
continuation. A uniform bound additionally requires `AppCost f k` over
every suffix and includes k. The raw D-law worker keeps its existing full
semantic scope. Retain XD01's padded-empty, shared-self-composition, charged
identity and repeated-application counterexamples unchanged.

C02-112 still needs the actual complete mutual scanner bounds and the common
BottomUp empty/single-run operational dispatch. That dispatch is a separate
integration dependency; neither the closure laws nor the held comparison
draft proves it. No full operational or chapter obligation is closed here.

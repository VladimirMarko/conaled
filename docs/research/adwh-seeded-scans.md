# Seed-inclusive partial-spine scans

## Source and scope

The sixteen selected declarations are from
`project/adwh-lean/ADWH/Chapter01/LazyListEvaluation.lean` in the supplied
successor archive. The canonical member SHA-256 is
`4f6308bd80e6b10c58d2eb97dbccf40abb8e3b625e2f93b1d5288c6e277ad01c`.
The exact source coordinates, statements, and destinations are recorded in
[`adwh-seeded-scans-declarations.tsv`](adwh-seeded-scans-declarations.tsv).
There are no selected anonymous source cases. Strict left folds and
function-accumulating concatenation belong to separate slices.

The implementation uses the existing finite `PartialSpine`, standard
`Order.Ideal`, the observation owner's pointed ideal CPO, and the single
`IdealCompletion.extend` operation. It does not reproduce the source package's
custom domain framework. Chapter 1 and the textbook remain open.

## Input constructors determine seed availability

`SquareKit.PartialSpine.scanl` retains the source's three clauses:

```lean
scanl f e .bottom = .bottom
scanl f e .nil = .cons e .nil
scanl f e (.cons a s) = .cons e (scanl f (f e a) s)
```

The distinction between unknown and completed ends matters even when there
are no known labels. Completely unknown input does not expose an initial seed.
A known nil exposes the seed and a completed end. A known cons exposes the
current seed while the continuation uses the updated state.

The independent prefix/end contract uses ordinary `List.scanl`:

| Input view | Output view |
|---|---|
| `(xs, true)` | `(xs.scanl f e, true)` |
| `(xs, false)` | `((xs.scanl f e).dropLast, false)` |

Consequently, completed input with n labels has n+1 scan labels. An open
prefix with n labels has n scan labels. The `view_scanl`, `scanl_ofList`, and
`scanl_openPrefix` theorems connect the actual finite executor to these
ordinary-list observations. Fixed-label spine refinement supplies monotonicity
for every `f : B → A → B`; no order on the labels or monotonicity/continuity of
f is assumed. Input and result labels have independent universes.

## The existing ideal extension supplies semantic scans

`SquareKit.PartialSpine.Observations.scanl` interprets each finite input
observation by the principal ideal of its finite scan and applies the existing
`IdealCompletion.extend`. Its continuity and principal laws specialize that
owner's general results.

The small `Observations.mem_extend_principal` addition in `Limits.lean` exposes
the useful membership contract:

```lean
q ∈ IdealCompletion.extend (fun s => Ideal.principal (g s)) I ↔
  ∃ s ∈ I, q ≤ g s
```

The source of g may be any preorder. The target is the existing partial-spine
observation ideal with its actual CPO instance; the theorem does not quantify
over an unrelated arbitrary CPO on the same carrier. It uses the already
established directed-union membership law and monotonicity of g.

The scan specialization retains exact membership, principal, bottom, nil, and
cons equations. The semantic cons proof uses the existing continuous-map
extensionality theorem and agreement on principals. No old constructor or fold
signature changes.

## Independent infinite meaning

`PartialSpine.scanStates f e sigma` is the stream

```lean
fun n => (sigma.take n).foldl f e
```

This replaces the source's recursive state helper with ordinary prefix-fold
meaning. The zero, successor, and shifted equations are derived from standard
prefix and fold laws. The finite bridge is

```lean
(scanStates f e sigma).take (n + 1) = (sigma.take n).scanl f e
```

Removing its final value yields the n-output open-prefix bridge. The semantic
stream equation and availability of every finite output prefix then use exact
ideal membership and finite-spine monotonicity. This retains the source index:
state zero is the seed, and state n is the result after n inputs.

The inspected standard contracts are Lean 4.35.0's `List.scanl_cons`,
`List.scanl_ne_nil`, `List.dropLast_cons_of_ne_nil`, and `List.foldl_append`,
plus pinned Mathlib's `Stream'.take_succ'`, `Stream'.dropLast_take`, and
`Stream'.take_theorem`. Their sources are `Init/Data/List/Scan/Lemmas.lean`,
`Init/Data/List/Lemmas.lean`, and `Mathlib/Data/Stream/Init.lean` at the pinned
Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.

## Actual Mealy realization and observation consumers

`Progress.SeededScan.lagged` supplies the ordinary existing Mealy operation

```lean
fun accumulator input => (accumulator, f accumulator input)
```

The existing `runList` therefore returns `(xs.scanl f e).dropLast`.
The bridge follows `unfold_mealy` through the standard coalgebra stream-prefix
law to `scanStates`; the existing observation adequacy theorems then connect
guarded and paused lagged realizations to semantic scan of their input
observations.

`Examples.PartialSpineScans` consumes these equalities through the existing
`PartialSpineLimits.allCuts` operation. Its theorem covers every constructor
budget at once. Actual `Delivers` and `Evaluates` witnesses are stated
separately using `mealy_realizations`, `paused_delivery`, and
`mealy_evaluates`.

The independently fixed case is counting from four, addition, and seed zero:

| Interface | Expected observation |
|---|---|
| Completed finite input `[4,5,6]` | Completed `[0,4,9,15]` |
| Open finite prefix `[4,5,6]` | Open `[0,4,9]` |
| Three infinite source-scan outputs | `[0,4,9]` |
| Existing updated-state scan outputs | `[4,9,15]` |

The lagged Mealy states are `(0,4)`, `(4,5)`, `(9,6)`, and `(15,7)`.
Its guarded and paused producers have three- and six-transition witnesses for
the first three outputs. The finite list machine has four transitions,
including its empty-tail test, and returns only `[0,4,9]`. It does not emit
the completed scan's final `15`; that would require an explicit end flush.

Existing `scanCoalgebra` and `scanProcessor` emit the updated accumulator and
retain their implementations and signatures. The new ordinary-list bridge
identifies the former's `scanList` with the tail of standard `List.scanl`, and
the examples retain both existing interfaces' `[4,9,15]` result.

Further cases retain silent-input bottom, the known-cons/unknown-tail result
from the existing once-then-silent producer, and an accumulator type different
from its input label type. The actual Mealy coalgebra bridges use the existing
Progress owner's common-universe interface. They do not introduce a generic
transformation or scheduler for arbitrary silently progressing producers.
Observation equality forgets transition time; the separate witnesses retain
the existing atomic transition model. No allocation or host-runtime result,
machine-overflow result, or queens-16 numerical proof is claimed.

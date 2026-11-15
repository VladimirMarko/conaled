# Partial predicates, stopping tests and completed prefixes

This development adapts sixteen declarations from the supplied checkpoint335's
`ADWH.Chapter01.LazyListDemand`. The operation consumes arbitrary partial or
infinite observation ideals. Its stopping theorem distinguishes a false test,
which completes an accepted prefix, from an undefined test, which leaves that
prefix open. The retained clients compose the semantic operation with actual
producer observations and existing first-output and truncation consumers.

## Shared owners and meaning

`SquareKit/PartialSpine/TakeWhile.lean` extends the existing
`SquareKit.PartialSpine.Observations` owner. It uses the existing `Order.Ideal`
carrier, fixed-label spine order, CPO instance, semantic constructors and one
shared fold/ideal extension. `Option Bool` is ordinary predicate-result data;
there is no new predicate domain, information order on labels, order hierarchy
or continuity framework.

The step interprets a result as follows:

| Predicate result at a known input head | Output |
|---|---|
| `none` | Bottom: the test supplies no result. |
| `some false` | Known nil: the output is completed at this boundary. |
| `some true` | The same head followed by the recursively consumed tail. |

Step continuity follows from the existing constant-map and cons-continuity
laws. The whole operation is the existing semantic right fold with known nil
as its seed. Input continuity and the bottom/nil/cons equations are direct
specializations of the established fold laws. An undefined predicate does not
force the result on known empty input to bottom: the empty input has no head
on which to test it. Conversely, even a constant-false predicate cannot produce
a known nil when no input constructor has been observed.

`takeWhile_ofList` connects total predicates on completed finite input to
standard `List.takeWhile`. It does not add label equality, finiteness or totality
assumptions to the general ideal operation.

## The boundary after an accepted prefix

For every accepted ordinary prefix and arbitrary suffix,
`takeWhile_prepend` passes the suffix to the same consumer beneath the known
prefix. This common law factors both boundary results. If the next test is
false, `takeWhile_stops` states that the result is the completed accepted
prefix. `takeWhile_suffix_independent` preserves exact equality for every pair
of suffix ideals beyond that test, including bottom and infinite streams.

If the next test is undefined, `takeWhile_undefined_after_prefix` instead
appends bottom to the completed accepted prefix. Existing append laws identify
that result with an open prefix. No conclusion about the suffix is assumed or
needed. The source's distinction between an undefined and a false test remains
visible in the final output end.

`takeWhile_openPrefix` states the stronger finite observation law: every open
prefix whose known labels all pass remains the same open prefix. This implies
the source's `takeWhileFold_streamPrefix` helper using the already proved
`foldr_principal` refinement. The source helper assumes every value of the
entire stream passes; the retained local law needs acceptance only for the
finite labels being observed.

`takeWhile_stream` then consumes the existing directed family of independent
`Stream'.take` prefixes. The open-prefix law fixes each principal observation;
Scott continuity and uniqueness of the existing least upper bound identify the
result with the original stream. No bounded prefix search is treated as the
infinite semantics, and no second stream model is introduced.

## Connected input and output observations

`Examples/PartialSpineTakeWhile.lean` imports the existing Progress observation
bridge and the first/allCuts consumers. The generic guarded and paused laws
retain any predicate accepting every value of the independent corecursive
stream. The concrete boundary starts the existing counting coalgebra at4.

| Test at7, after accepting4,5,6 | Semantic output | `allCuts` budget4 |
|---|---|---|
| False | Completed `[4,5,6]` | Retains the final nil. |
| Undefined | Open `[4,5,6]` | Retains the unknown end. |

The cases use the public stopping laws after decomposing the actual producer
observation via the standard corecursive stream equation. Both guarded and
paused inputs refine the same stream. `counting_first` consumes the false-test
result through the established first-output law and obtains the independent
expected value4. The paired cuts and independent finite `view` end flags
distinguish the false and undefined results.

The actual input prefix `[4,5,6,7]` has existing guarded4/paused8 transition
witnesses and final state8. Those witnesses certify available input tests. They
are not a transition-count, allocation, sharing or runtime theorem for the
noncomputable semantic consumer.

Further retained cases cover:

- An all-true predicate retaining the counting stream and its first three cuts.
- An emit-once input followed by silence: true retains its open singleton,
  false yields known nil, and undefined yields bottom.
- A constant-false test on a silent input, which remains bottom.
- Known empty input versus an unknown input under an undefined predicate.
- The accepted open prefix `[4,5,6]` without a fourth input test, which remains
  open and differs from the stopped completed result.
- An arbitrary suffix compared with an actual infinite suffix beyond the
  failed test, through the public suffix-independence theorem.
- Total finite input `[4,5,6,7,0]`, connected to standard `List.takeWhile`.

The existing producer interface has no completed-end transition.
`stopped_not_producer` uses its existing `ofList_not_mem` theorem to show that
the completed stopped result cannot equal any observation ideal of a producer
under that interface. This identifies the precise interface boundary; it does
not postulate a terminated producer or introduce an end-event extension.

## Source and validation scope

`adwh-partial-takewhile-provenance.tsv` preserves all sixteen selected source
rows exactly once, including their original statements, coordinates, source
hashes and qualifications. Fifteen rows map to matching local operation/law
names. The finite stream-prefix helper maps to the stronger accepted open-prefix
law plus existing principal fold refinement. The extra accepted-prefix prepend
law factors the shared boundary argument.

Canonical source SHA-256:
`403a687ddf40f94adcc8a05b8a6f30fc826f77ad36940674abec93b5f038f608`.
Supplied archive SHA-256:
`9e8bee022149e8456c9c4ab318f3be0d5d7f8361c25e7409cfe1c12bf8eb812c`.
Standard owners are pinned with the repository's Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679` and Lean4.35.0.

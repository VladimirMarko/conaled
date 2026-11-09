# Complete cached emitted-family statement review

The adopted artifact is unchanged from accepted #135 at `209a8f85a14b21cdb531497f97b159fe2af7408f`. The final branch incorporates published base `8925b914dc49322d323a1c1475451f3b8d4b81ec`. The ConLeche source pin is `8e166ca53cd1f864b63c13cc1d326d38316d00ea`, using Lean 4.35.0. This review covers the completed claims; earlier checkpoint reviews retain their narrower historical scope.

## Backward theorem and composition

`CachedPending10Stages` checks the actual emitted backward header inference, sort, proposition test and value guards. `CachedPending10Open` opens all eight actual lambda binders, retaining the reached inference and weak-head states. The opened application is the actual Exists.intro at carrier level `succ (param v)`, with four arguments. `CachedPending10Spine` checks its head, four argument inferences and first three conversions. `CachedPending10Equality` checks the remaining conversion between the inferred And proposition and the predicate applied to the witness. Its beta comparison uses the original predecessor fuel, actual quick/proposition/weak-head operations, and exact final cache insertion.

`CachedPending10SpineJoin` assembles the exact application operation. `CachedPending10Value` abstracts and rebuilds the eight binders, then inserts the outer value inference into the post-body map. `CachedPending10FinalEquality` checks conversion of this inferred type to the actual emitted header. `CachedPending10.run` composes the operations at unchanged `checkFuel = 2^62`, position 13, visibility 19, fresh memo and actual predecessor environment. `accepted_final` uses the one-record suffix and unchanged tables to restrict the final canonical environment to that prefix.

The new `CachedPendingRunComposition.thm_ops_run` and `thm_run` require successful header inference, sort, proposition-level equality, actual value guards, body inference and final conversion. The existing definition-specific assembler is not used to bypass theorem guards. The whole-operation-record equality and prefix equality are explicit premises of the generic wrapper and discharged in the concrete application. All generic intermediate states are quantified and connected by exact success equations; none assume arbitrary cached/pure agreement.

## Whole-family endpoint and consumers

`CachedEmittedAcceptance.groups` proves all eleven `GroupChecked` obligations by the actual pending certificates. Indices beyond the queue length use the pinned `groupChecked_of_ge` theorem. `checked` packages the list-indexed certificate. `installedArray` preserves the same concrete FEnv and pending queue while transporting only the installation proof across `List.toList_toArray`; `checkedArray` packages its checks. This avoids hiding the output environment behind a transported data object.

`CachedEmittedAcceptance.accepted` is exactly:

```lean
ConLeche.Cached.checkDecls .verified []
    EmittedEnvironment.declarations.toArray =
  .ok EmittedEnvironment.environment
```

It has no success hypothesis or SetTheory premise. The input includes the three primitive blocks, nine native helpers and both emitted theorem records. The complete output index, tables and twenty constants are fixed. The pinned `fullyChecked_checkDecls` theorem supplies the final operation equation. Pure acceptance is not used to infer cached success.

`CachedAcceptedEmission.model_exists` applies cached soundness with the verified-mode equality and the endpoint above, then converts the returned environment model using the existing model conversion. `model` selects such a model. Both retain `[SetTheory V]`. `source_comparison` and `emission_comparison` instantiate existing semantics at this model and preserve their universe, assignment, encoding and denotation premises. `closedTruth` instantiates the checked application of both actual emitted theorem records; it preserves carrier/function membership and premise/conclusion denotation assumptions. This supplies an actual emitted-record client in addition to the generic comparisons.

The three unconditional exported malformed-input equations are reviewed in [the controls checkpoint](../checkpoint-417-rejections/statement-review.md). They are rebuilt in the combined focused run. Their changed actual families, earlier successful checks and reported positions remain explicit. The missing-helper diagnostic remains the exact opaque formatter expression, without an invented normalized message.

## Validation and limits

`measurements.json` retains a consecutive focused build/audit of nineteen modules after incorporation of the published base, including the changed generic wrapper, matcher regression, complete backward stages, endpoint, model clients and all seven control modules. The final endpoint module took about 0.60 seconds and its model client about 0.55 seconds in that run. These are module construction/checking measurements, not bounds on executing the checker. The records include source hashes, limits, separate generation/insertion/render phases and capped output.

`failed-attempts.json` and `failed-sources` preserve five further Lean failures. The direct last-argument conversion timed out in generation; its split beta proof subsequently checked. An early equality module had ambiguous open-namespace names and an absent import; its timeout does not establish an operational failure. Two theorem-wrapper attempts had elaboration errors, then the corrected wrapper checked. The first endpoint attempt transported an entire FullyChecked value, obscuring the final environment; transporting only the installation proof fixed that typing join. A separate script typo tried to build an equality module before creating it; no Lean process or proof result existed for that missing file.

The unused structural-expression diagnostic is retained as `.lean.txt` in `diagnostic-sources`, outside automatic discovery. The historical pending checkpoint retains its old unfinished drafts as text. All active top-level Lean sources are intended proof modules; the portable runner discovers the completed endpoint, client and controls without a hand-maintained module list. Four runner tests pass, including the cached plan assertions, failure of output-directory reuse, timeout handling and exhaustive audit controls for private/transitive axioms and unsafe-source policy.

These are focused development results with reused dependency objects. Final acceptance still requires the frozen candidate's fresh isolated upstream/native/graph closure, exhaustive closure audit, ordinary main candidate build/audit and exact verification, plus independent Standards, Spec and supervising originator reviews. No inherited receipt is candidate approval. The main dependency graph and #107/#108 ownership gates are unchanged.

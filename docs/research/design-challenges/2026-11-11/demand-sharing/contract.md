# Contract and foundations assessment

Recommendation: retain the current finite runners and partial-spine semantics, and test a small explicit request runner for head of concatenation before selecting a shared evaluator. Its state must retain identities and the results of previous requests. Its observations must distinguish an unknown end from a completed empty list and must record ordered requests separately from their bills. Existing laws do not imply memoized reuse, but they already supply substantial semantic and accounting obligations that should remain theorems rather than become new proof fields.

This assessment concerns pinned commit `e80c51d968925be3809ba3acc3259de7041b504b` in `source/`. All declaration references below are relative to that checkout. It recommends an experiment, not architectural adoption.

## What the current contracts establish

`Resources.CollapseDemand.Label` in `Applications/Resources/CollapseDemand.lean` is `(Unit → Measured Int Nat) × List Int`. `lazyLabels` builds delayed sums, while `cachedAux` keeps a scalar running sum and consumes each selected label once. Its name describes retained accumulation; it does not assert that invoking the same thunk twice reuses a result. For arbitrary labels, `cachedAux_value` relates the run to the corresponding eager-label fold, not necessarily to actual sums of their payloads. The sum correctness and closed cost formula use `lazyLabels` and `Steepness.sumRun`. This distinction matters when preserving arbitrary callbacks.

The strongest retention evidence is specific:

- `cachedAux_positive` shows that the total test avoids even the next outer spine case. `cached_first_positive` gives exact selected sums and counters independently of the discarded suffix.
- `cached_selected` retains empty selected blocks and the first-positive-prefix condition. `cachedAux_used_eq_plain` and `values_equal` connect optimized and plain selection and values. Flattened output alone loses this information.
- `cached_zeroBlocks_work`, `plain_zeroBlocks_work`, and `quadratic_sum_work_witness` preserve the exact linear and quadratic source work distinction under stated sum costs.
- `CollapseMaterialization.labelStep_cons` charges demanded label production separately from forcing its sum. `buildAux` tests, produces a label, forces its sum, and stores a reverse history. `leftMaterialize` and `applyFunction` then charge different full observations of that history. `applyFunction_value` quantifies over every supplied tail, and `applyFunction_work` is independent of that tail.
- The native client `Examples/CollapseResources.lean` composes `differenceSquare` with `measuredSum` through `observedDifference`. `observed_work` includes the consumer's work. Its `no_unconditional_improvement`, empty-block, arbitrary-tail and signed-input examples are useful acceptance cases, not merely migration conveniences.

These are total finite source-model executions. Their module comments explicitly exclude host evaluator, allocation, memory and machine-time claims. `CollapseDemand.Run` records selected sum inputs but not a complete interleaving of tests, spine requests and forces. No inspected theorem turns it into a replayable cache protocol.

## Necessary distinctions and derivability

A minimal sequential experiment can use consumer-specific state with the following information, without requiring a universal language:

| Information | Why it is needed |
|---|---|
| Stable cell identity or equivalent explicit sharing graph | Two references to one cell must be distinguishable from two independently allocated cells computing equal values. Extensional result equality does not establish sharing. |
| Suspended versus resolved cell contents | After a force succeeds, the next request must consult changed state. A function returning a measured value lacks that transition. |
| Current producer/inner cursor and deferred append frames | A head request must resume at the outstanding work and must not require full materialization. Left-associated history and right-associated blocks can have different bills. |
| Outstanding request/control state | A silent producer may need several steps before responding; repeated requests must continue or reuse the same work under the selected policy. |
| Distinct unknown, completed nil and cons observations | Unknown end cannot justify advancing to a fallback block. |
| Ordered events and their local costs | Request order, callback evaluation, cache lookup, allocation, traversal and append-frame work cannot be reconstructed from an undifferentiated total. |

These are semantic information requirements, not mandated record fields. A continuation can encode control state; an indexed store can encode identities; an inductive transition derivation can retain events without placing a growing trace in runtime state. Do not require a permanent trace allocation just to prove a trace theorem. A per-cell “evaluating” state is needed only if the experiment admits reentrant forcing/cycles or concurrency; sequential nonrecursive callbacks do not justify it yet.

Use constructor rules for first force and cache hit, then derive at-most-one successful evaluation per retained cell and repeated-request cost by induction over executions. A new interface need not ask each caller for separate “memoized”, “same answer twice”, “no second callback”, and “cached cost” fields if those results follow from the transition rules and store invariant. Conversely, these claims do not follow from value preservation alone: a runner that recomputes the same deterministic thunk on every request has identical values and can satisfy the same denotational refinement.

The accumulated scalar in `cachedAux` is useful state. Counts such as tests and scalar additions already have derived theorems (`cachedAux_tests`, `cachedAux_scalarAdds`). `BuildRun.history` and `used` have `buildAux_history_blocks`; storing both is useful as an observation report, but that does not make both necessary execution state. Deriving a bill by folding a charged event trace would make a separate total-consistency proof field redundant. It would still require an independent adequacy argument that the event vocabulary accounts for every operation claimed by the model.

The lookup/hit charge must be declared, not silently set to zero. A no-eviction retained-cell model supports at-most-once evaluation. Eviction or recomputation would change that guarantee and belongs in a different policy or theorem hypothesis. If callbacks are arbitrary but pure measured functions, memoization preserves their values. Stateful callbacks require an explicitly different semantic contract; caching may change externally observed behavior. Do not infer a purity or termination guarantee merely from the desired optimization.

## Partial information is already a useful semantic owner

`SquareKit.PartialSpine` has distinct `bottom`, `nil` and `cons`; `viewEquiv` identifies it with an ordered finite prefix plus a completed-end flag. Therefore it already supplies the necessary finite end distinction. `Observations` in `SquareKit/PartialSpine/Observations.lean` uses ideals and admits streams that `stream_ne_principal` proves cannot be represented by one finite spine.

`Observations.append_bottom` and `append_openPrefix` in `SquareKit/PartialSpine/Append.lean` establish the obstruction: an unknown left end prevents fallback to the right. `append_stream` hides an arbitrary suffix after an infinite stream. `Observations.concat` in `SquareKit/PartialSpine/Concat.lean` preserves these distinctions; `concat_bottom`, `concat_nil`, `concat_cons`, and `concat_infinite_first` are directly usable. `foldr_concat` assumes a complete partial order for the result and Scott continuity of every step. It does not assume finite inner lists or a productive outer source.

The native `Examples/PartialSpineConcat.lean` consumes these laws in `first_concat`, `first_concat_once`, and `allCuts_once_guarded`. It exhibits an emit-once, nonproductive outer producer whose first inner stream supplies arbitrarily many observable outputs. Requiring global outer productivity or completed outer construction would reject an existing intended example. Its bottom-inner example also shows why a later nonempty block is inaccessible when the first inner list has unknown end.

Two limits need preservation in any bridge:

1. `PartialSpine` orders labels as fixed values. A label can be a reference to a separately partial computation, but the existing spine order alone does not express gradual information refinement within an arbitrary label. `concat` likewise treats inner ideals as fixed outer labels. Proving continuity for changes inside those labels is a separate question, not supplied by outer-spine continuity.
2. `PartialSpineLimits.first` in `Examples/PartialSpineLimits.lean` is a proposition-valued positive first-output observation with seed `False`. By unfolding its fold, both bottom and completed nil give `False`. That consumer alone cannot certify an operational distinction between “no answer yet” and “finished empty”; retain the spine semantics or use a result domain that distinguishes them. This is an observation limitation, not an error in the theorem.

`Progress.Evaluates` and `search` in `Applications/Progress/Evaluation.lean` already separate finite evaluation from unknown search results. `search_complete` requires a finite evaluation derivation and sufficient fuel. `Progress.Producer` in `Applications/Progress/Streams.lean` emits or performs silent work but has no terminal constructor. Correspondingly `SpineObservations.ofList_not_mem` excludes completed observations from that producer's observation ideal. A native finite-list producer therefore needs an explicit terminal reply, or a separately stated encoding of termination; silently treating lack of a delivery as nil would be unsound.

The guarded and paused consumers give equal denotations but different delivery counts (`PartialSpineAppend.counting_allCuts_and_deliveries`). Thus denotational equality cannot derive exact demand costs. The concat examples explicitly leave nested scheduling unproved. A new operational runner needs a bridge to these observations and its own scheduling bill.

## Small alternatives and discriminating evidence

The smallest useful alternative is two consumer-specific sequential runners with the same requests and observation projection: delayed recomputation and retained memoization. Their separate transition definitions can demonstrate which bookkeeping is truly shared. A small common store/force layer becomes justified if both head-of-concat and a repeated outer-label consumer use it without artificial adaptation. A broad delayed evaluator remains admissible, but no inspected consumer demands its syntax or general recursion machinery yet.

Freeze these proposed tests before implementation:

- Allocate one cell with a hypothetical callback bill `c`, then request it twice. Both runners return the same value. Delayed behavior charges the callback twice; memoized behavior charges it once plus explicitly declared allocation and request/lookup/update charges. Request two distinct cells with equal callback outputs as a separate case. Memoization by value must not pass as memoization by identity.
- Construct/count an outer spine of delayed labels with an arbitrary measured callback. The event trace contains no callback force. Fully observe it and check all callback and inner-spine charges. Repeat one label request and check the policy-specific delta. Do not collapse repeated occurrences merely because their values coincide.
- Request the head of concatenated completed blocks `[[], [a], ...]`. Record all empty-block end observations and the request yielding `a`; the later payloads remain unforced. Compare left-associated deferred history and right-associated execution using exact bills, not an assumed ordering of performance.
- Replace the first completed empty block with unknown bottom. No fallback request to `[a]` is justified. A finite fuel timeout remains unknown, not empty and not a proof of divergence.
- Use the existing emit-once outer producer with a guarded or paused infinite inner stream. Head delivery succeeds without outer completion; the trace and bill retain the inner silent-step difference. Compare the output observation with `concat_once_guarded`/`concat_once_paused` and preserve `concat_infinite_first` for arbitrary remaining outer observations.
- Apply a deferred concatenation to an arbitrary tail and observe a finite demand. Prove the value equation uniformly in the tail; do not use equality only at `[]` to claim a difference-list representation theorem.

Acceptance requires an independent event/accounting specification and a refinement theorem relating actual runner traces to the chosen spine observation. Exact bills can then be checked for these fixtures. A theorem equating one runner with its own field projection would not establish the correspondence. Costs for nonterminating requests should be stated on finite prefixes of execution, with eventual delivery conditional on a finite witness or an appropriate progress hypothesis.

## Evidence and exposure limits

I inspected the pinned definitions, theorem statements, relevant proofs, and native clients named above. The unknown/nil distinction, lack of cache mutation in thunk types, and separation of existing delivery counts from concat scheduling are source-established limitations. The proposed minimal state and derivability arguments are paper-level design arguments. No Lean experiment, build, proof audit, runtime benchmark, or upstream comparison was executed. No external factual claims about Haskell evaluation are needed for this recommendation. I did not inspect recovered historical drafts as authorities.

I had no prior involvement in this task, received only the brief and the contract/foundations assignment, and did not read other assessments or coordinate conclusions. There is no established model diversity. I read repository architecture/domain guidance, relevant ADR 0001, the design-challenge and scope-check instructions, and the prose guidance. The pinned current results support retaining their mathematical contracts; they do not settle whether a shared machine saves author effort. That remains the experiment's decision.

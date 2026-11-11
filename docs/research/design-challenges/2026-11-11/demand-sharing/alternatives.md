# Demand and sharing: alternatives and generality assessment

Recommendation: retain the existing mathematical observations and finite resource executors. Compare a consumer-specific transition system with a small reusable cache component before selecting shared machinery. The next head-of-concatenation consumer needs explicit demand boundaries and resumable production; repeated requests additionally need identity and retained evaluation state. Neither capability requires a general lambda evaluator. A broader evaluator remains a legitimate competing foundation if later consumers need nested shared closures, recursive dependencies, or contextual program equivalence.

This assessment uses source commit `e80c51d968925be3809ba3acc3259de7041b504b` in the pinned checkout. It does not assess #472. I have no prior involvement in this design in the supplied context, have not read other reports, and have not coordinated conclusions. Fresh context supplies no model diversity guarantee.

## Evidence for retaining the current pieces

`Applications/Resources/CollapseDemand.lean:26–86` represents sum labels as functions and explicitly records the selected sum inputs. `cachedAux` carries the accumulated integer and consumes each selected label once. Its cache is the accumulated sum across iterations; there is no reusable heap cell updated by forcing a label. This is an appropriate specialized algorithm. Calling it an invalid memoization implementation would misdiagnose its actual contract.

`Applications/Resources/CollapseMaterialization.lean` separates history construction from full materialization. `buildAux` (line 146) demands one `labelStep`, forces its sum, then updates the history. `buildAux_apply` (291) and `build_apply_difference` (361) quantify over arbitrary tails. `left_quadratic_work_witness` (508) preserves a meaningful difference between realizations that agree on values. These proofs remain useful even if the next consumer uses a different operational foundation. Full materialization costs should not be reused as head-only costs.

The strongest semantic retention evidence is the actual producer/consumer composition in `Examples/PartialSpineConcat.lean`: `concat_once`, `concat_once_guarded`, `concat_once_paused`, and `first_concat_once` establish useful output despite a silent outer continuation. `SquareKit/PartialSpine/Concat.lean:43`, `concat_infinite_first`, permits an arbitrary outer continuation after an infinite first inner stream. `Examples/PartialSpineAppend.lean`, `allCuts_openPrefix`, and the explicit `append_bottom` example preserve the obstruction caused by an unknown end. These are stronger tests than finite flatten equality.

`Examples/PartialSpineAppend.lean`, `counting_allCuts_and_deliveries`, deliberately retains equal observations with different producer step counts. The current design already demonstrates why value semantics cannot determine cost. `Resources.run` and `reweight_run` in `Applications/Resources/Workload.lean` supply ordered execution and additive transport without commutativity. There is no reason to rebuild that accounting algebra.

## Operational alternatives

| Approach | State and capability | Principal cost or limitation |
|---|---|---|
| Separate consumer runners | Outer producer state, current inner state, append frames where needed, and an optional local retained result | Small proofs and direct correspondence to the algorithm; duplicated cache rules become a concern only after distinct consumers need the same rules |
| Small shared cache plus consumer control | Stable cell identities, suspended/resumable computations, completed results; the consumer still chooses requests | Reuses force/update behavior while preserving algorithm-specific demand; requires an explicit policy for partial results and cache lifetime |
| General heap evaluator | Syntax, environment/heap, evaluation rules, shared recursive bindings, demand contexts | Can express sharing across nested programs; introduces binding and evaluator adequacy work that the current consumer alone does not demand |
| Denotational demand specification plus separate realizations | Partial observations and a relation to operational traces, with delayed and memoized implementations admitted separately | Best separation of meaning and mechanism, but an extensional ideal alone cannot establish request order or memoization costs |

The fourth approach can accompany any of the first three. A competitor should not be rejected for failing to implement today's runner interface. Its admission test should be the required observations and author obligations.

A concrete external alternative is Launchbury's heap semantics. Its normalized language has distinct bound variables and applications to variables; a heap maps variables to expressions. In its Variable rule, evaluating a binding removes that binding while evaluating its expression, then reinstalls the evaluated value. The rule assumes a successful finite evaluation derivation; it does not promise termination for all expressions. See Sections 3.1–3.2 and Figure 1 of [A Natural Semantics for Lazy Evaluation](https://launchbury.blog/wp-content/uploads/2019/01/semantics-of-lazy-evaluation.pdf). This supplies a precise sharing mechanism worth comparing. It does not itself establish our ordered event tariffs, finite-end protocol, or Lean runtime costs. I use its rules as an alternative design, and do not rely on its denotational correctness proof here.

## What the minimal extension must distinguish

The following are design requirements inferred from the intended observations, not discovered defects in current declarations.

1. Identity differs from payload equality. Two references to one allocated cell must share; two independently allocated cells with equal payloads need not. Function-valued labels rule out deriving identity from decidable payload equality. Stable natural addresses or structurally allocated handles suffice for a bounded experiment.
2. A constructor result differs from a fully observed payload. A retained cons can contain a still-suspended head and tail. Caching an entire `List α` only after fully evaluating it would fail the infinite-inner test. Cache entries should match the demand granularity actually used.
3. Unknown differs from known nil. A bounded runner may report suspension or budget exhaustion; it must not equate that with completed emptiness. An unknown response must retain a continuation if later requests are meant to make progress. Whether retries restart or resume is an explicit execution policy.
4. Cache hits have an observation and a declared price. A successful first force may remove subsequent callback work, while later lookup, dispatch, and delivery remain charged. Zero hit price is an allowed tariff, not a theorem of memoization.
5. Ordered event history is richer than accumulated Nat work. Keep allocation, request, producer step, callback execution, update, and hit events in actual order, with request grouping if the contract observes per-request bills. Define scalar tariffs afterward.

For total, nonrecursive callbacks, a suspended/done cell can be enough. If callbacks can force other cells recursively, active evaluation needs a specified reentry behavior. Do not add a universal busy/error state merely by analogy with a full evaluator before that capability is required. Conversely, a two-state cache must not be advertised as implementing arbitrary recursive lazy programs.

A genuine existing boundary is `Progress.Producer = S → Sum (A × S) S` in `Applications/Progress/Streams.lean:16`: its alternatives are output and silent work, with no terminal constructor. `SpineObservations.ofList_not_mem` explicitly says this observation interpretation never contains a completed list. Therefore direct reuse cannot justify fallback after known finite exhaustion. A next-step protocol with a distinct terminal result, or a separate finite-source realization, is needed for that case. This is an extension boundary, not a failure of its stream contract.

## Discriminating experiment

Freeze one independently specified request/event vocabulary and compare the first two approaches on these fixtures. These are proposed tests, not executed results.

- Allocate one delayed payload, request it twice, then allocate an equal but distinct payload and request it. Expect equal returned values but one callback execution for the shared cell and another for the distinct cell; retain both hit and miss bills.
- Count outer cells whose labels are callbacks, including function-valued labels. Expect no callback executions. Fully observe the same finite structure and retain all values, callback charges, inner cons observations, and terminal observations, including empty payloads.
- Head of `[known empty, nonempty, untouched suffix]` should request the first two blocks in order and stop. Replacing the first known empty block with an unknown empty prefix must prevent fallback, even though the visible list prefix is still empty.
- Use the existing emit-once outer producer with an infinite guarded or paused inner producer. Head must be obtainable without obtaining a completed outer tail or a complete inner list. Preserve the distinct guarded/paused costs despite equal head values.
- Repeat a suspended request with an extended budget. Compare restart and resume policies explicitly, and verify that neither turns suspension into nil. Test the cache at the same granularity as head/tail demands.
- Compare left-associated deferred append frames and right-associated head traversal on the same finite blocks. Compare values, request order, and full event bills; do not require equal bills merely because flatten agrees. Include an arbitrary supplied tail when checking difference-list semantics.

Judge shared machinery by whether a second consumer, such as delayed insertion outer-count versus full observation, reuses the cache transition proof without importing concat control. If it does, extract that component. If most obligations remain consumer-specific, retain separate runners. A general evaluator earns adoption if the same fixtures plus a nested shared-closure example substantially reduce repeated author obligations under the same observation contract.

## Validation and exposure limits

I inspected declarations and their consumers and read the primary external semantics rules. No Lean experiments, builds, proof audits, benchmarks, tracker changes, or source edits were performed. Proposed transition laws and experiment outcomes remain paper-level reasoning. This report adds no theorem fields: cache behavior should first follow from the chosen transition definitions; a general abstract interface should expose only laws consumers actually need. The external comparison is bounded to one heap semantics, not a survey of graph reduction, interaction trees, or demand-analysis systems. No claim is made that the current theorem inventory supplies an operational adequacy bridge for the proposed cache.

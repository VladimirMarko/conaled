# Supplement: when demand scheduling belongs first

The initial report is unchanged. This supplement answers the coordinator's targeted challenge without access to other judges' findings or withheld preferences.

## A workload that reverses the priority

Consider a bounded monitoring application with independently requested views. This is a proposed workload, not a measured application already in the repository.

- View A requests an ordered merged batch from remote sources L and R at time t. R has not certified that time, so A remains pending.
- View B requests a projection of a local source S at time u. S has certified u, B's evaluator terminates, and B's sink accepts output.
- The application admits both requests within its advertised capacity. B must complete under fair scheduling even if R never certifies t. Cancellation of A must release A's resources without cancelling a shared dependency that another admitted request still owns.

This requirement makes bounded demand scheduling an early deliverable. The guarantee concerns independent progress, not a speculative speedup. A globally exclusive request owner either rejects B as busy or blocks B behind A; neither satisfies the stipulated admission and progress contract. The current `Exclusive.step` explicitly reports busy when a request is pending (`Applications/FRP/Exclusive.lean`, `step`, `begin_busy`). That is correct for its current interface, but insufficient for this workload. Similarly, `IndefiniteIO.serve` writes and flushes an output before reading the next byte (`Applications/FRP/IndefiniteIO.lean`, `serve`); a blocked sink can stop the whole session. Its existing correctness is not challenged.

If this application is the intended first client, D's bounded slots, dependency wakeups, cancellation ownership, and backpressure test the central user requirement sooner than A's affine evaluator or B's startup selector. The smallest useful D can use discrete finite values and source frontiers. Rational continuous phases need not precede it. A direct synchronous implementation remains a reference and comparison, but completing a globally serial driver first should not be a delivery dependency.

There is one decisive observation choice: independence requires separate output channels, or a multiplexed protocol that allows B's identified response before A's response while preserving each request's internal occurrence order. If the client instead requires one globally ordered response stream in admission order, A must precede B. That requirement deliberately reintroduces blocking at publication, even if B computes early. No scheduler can both satisfy that total order and publish B while A is unresolved. The client contract must settle this before comparing progress claims.

## Synchronous meaning does not require globally serial execution

My initial recommendation of a synchronous session core should not be read as requiring a single pending request, a blocking transition, or globally serial publication.

`Feedback.Initialized` specifies a total transition on an explicit state; its stream index counts logical transitions, not elapsed time or exclusive use of a worker (`Applications/Progress/Feedback.lean`, `Initialized`, `Solution`). A state can contain several bounded request slots, and commands can represent admission, dependency completion, cancellation, and retirement. Each command can have a small terminating state transition while expensive or unavailable work remains pending. `Engine.step` already demonstrates a distinction between updating knowledge and delivering a demand, although its concrete state has only one request (`Applications/FRP/Engine.lean`, `MachineState`, `step`).

A sequential command trace can therefore specify concurrent or event-driven execution. Establishing its refinement still requires an ownership/linearization argument and an observation contract. A shared sink must not block the entire event loop; distinct sinks or buffered publication require their own capacities and fairness premises. A single event-loop thread can satisfy the example if it never blocks on unresolved work. Multiple worker threads alone do not establish independent progress.

Thus the choice is not synchronous semantics versus asynchronous implementation. It is whether the first executable admission protocol already handles multiple pending demands and dependency-specific progress. For the workload above, it must.

## Can local push-pull composition meet this without a centralized graph?

In principle yes, for a fixed bounded network, but the current archive does not establish it.

A candidate organization assigns each demanded computation a local promise/residual computation and subscribes only to its dependencies. Source updates wake subscribed computations. Independent ready outputs can advance while A waits. Shared dependencies require a shared memo cell with explicit owners; cancellation removes the caller's ownership and cancels underlying work only after the final owner releases it. Bounded subscribers and result buffers establish capacity limits locally. A ready-task dispatcher can remain centralized without maintaining or scheduling a global dependency graph. Alternatively, callbacks can enqueue work at local owners.

Elliott's [2009 push-pull paper, sections 7–11](https://conal.net/papers/push-pull-frp/push-pull-frp.pdf) gives compositional reactive values, futures, and residual sampling as a relevant starting point. Its compatible-choice premise excludes racing arbitrary effects, and its discussion of nested losing computations identifies cancellation cleanup as unfinished implementation work. It does not discharge the ownership or bounded-storage obligations above.

The direct library alternative therefore removes the requirement to materialize a centralized graph, not the dependency structure or scheduling obligations themselves. Without shared identity, it can recompute a shared node independently; that may preserve values but fail an advertised work budget. Without per-owner cancellation, cancelling A may break another request. Without a bounded local queue, decentralization merely moves the storage problem.

The discriminating experiment is the workload above with a shared dependency and a deliberately blocked unrelated source/sink, implemented both as local subscriptions and as D's explicit DAG. Require the same dependency-specific progress and cancellation observations; account for subscriber tables, memo cells, queued callbacks, and result buffers in both. No numerical integration or policy ranking is necessary. Which implementation is simpler or cheaper remains unmeasured.

## Limits and revised recommendation

Demand scheduling should be early when independently admitted requests must make progress independently, or when avoiding unnecessary work is part of an explicit resource contract. In that case I recommend starting the bounded discrete D experiment alongside the reference semantics, rather than deferring it behind a serial session implementation. If the first client permits exclusive admission and one ordered sink, the simpler serial runtime remains a useful first delivery.

This supplement is a paper analysis supported by inspected source declarations and the previously read primary paper. No new code, Lean checks, benchmarks, or counterexample scripts were executed. Only the supplied archive was read; no original checkout, project issues/history, peer report, or withheld preference was accessed. The supplement changes the conditional priority recommendation and clarifies terminology; it does not alter the initial report.

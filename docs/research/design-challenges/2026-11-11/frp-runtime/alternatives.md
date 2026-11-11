# Alternatives and generality assessment

Assessment date: 2026-11-11. Baseline: `1ecdea2376786920a043009a35712a5dec93723a`, read only through the supplied source archive. Lens: alternatives and generality.

## Recommendation

Retain the independent denotational specifications, compiled transition machinery, numerical contracts, and optional recovery contracts. Treat the proposed demand-driven hybrid runtime as a candidate execution organization, rather than the shared foundation that every capability must await. Compare it against a synchronous session core with explicit commands and optional demand scheduling. Run the comparison using both a stateful numerical client and a nontrivial state conversion. Those tests would constrain the architecture more than startup ranking alone.

The strongest case for retaining the candidate is concrete reuse. `ReactiveCompiler.realize_compile` and `run_sound` establish source correctness through local target laws; `Feedback.run_related` accepts arbitrary related starting states; `Indefinite.Program.seq` and `par` construct composed machines with resource results. These are usable components rather than promises of a universal runtime. The candidate also explicitly separates source switching from backend replacement, includes failed preparation and single ownership in G, and does not pretend that recovery follows from frontiers. Its strict order requirements match actual clients: `Examples/ReactiveTarget.lean` distinguishes an emitted empty batch from silence, while `Examples/IndefiniteService.lean` exercises retained delayed state and a redundant state representation.

The question is therefore which additional operations belong in a common execution contract, and which should remain library-specific. I found sequencing risks and unanswered architectural choices, not a contradiction that invalidates the whole candidate.

## ALT-1: The demand scheduler does not need rational phase execution as a prerequisite

**Status:** established separation in inspected interfaces; the benefit of choosing one organization is unmeasured.

Stage D requires a finite dependency DAG, bounded demands, finite discrete values, and explicit delays, yet is placed after A's rational phase execution. Nothing in that initial D scope needs rational affine phases or real-valued `denoteRNF`. Existing `Progress.Feedback.Initialized` has only a transition and initialization (`Applications/Progress/Feedback.lean:9`); the compiled Boolean circuit service already supplies finite transition evaluation and composition (`Applications/FRP/Indefinite.lean:34`, `:43`, `:108`, `:114`, `:125`). `Frontier.State` and its soundness theorem are generic over a linear order and payload (`Applications/FRP/Frontier.lean:43`, `:101`). This is evidence that the dependency is a research choice, not a prerequisite established by current declarations.

A smaller alternative is an event-driven synchronous session: each admitted command makes a bounded pure transition, returns observations, and retains state. Here synchronous means one logical transition per admitted action, not periodic sampling or an assumption that external sources arrive together. `Pipeline.responseMealy` already makes this distinction: silence stutters, while every emitted batch ticks the consumer (`Applications/FRP/Pipeline.lean:22`). A scheduler can later implement admission and completion around that interface. Static computation inside a transition need not become runtime graph nodes.

**Smallest correction:** remove A as a compulsory dependency of the finite discrete D experiment. Keep A as a separate client of the eventual scheduler if it benefits from asynchronous demand. Preserve the current circuit and pipeline APIs as ordinary library entry points.

**Discriminating test:** implement the same bounded diamond dependency with a shared expensive node under (a) a direct synchronous transition and (b) a bounded demand executor. Include sparse requests, two simultaneous owners, cancellation of one owner, and a blocked sink. Compare ordered observations and residual state, accepted-request progress, peak live storage, author obligations, and actual work. The synchronous baseline may duplicate work; the graph executor may pay more bookkeeping than it saves. Either result is informative. This is a proposed experiment, not a measured outcome.

**Compatibility:** existing discrete clients remain unchanged. Demand-specific cancellation and independent progress are additional capabilities. A periodic sampler that drops batches would not be a compatible alternative.

## ALT-2: Affine phases can pass while the decisive numerical state/effect boundary remains untested

**Status:** plausible architectural risk supported by a concrete difference between existing clients.

A's constant/affine evaluator is a useful exactness test, but queries of an affine function can be recomputed without an approximation packet. E also allows an exact affine ODE instead of the existing approximate motion client. Choosing both easy routes could leave the common phase interface untested against rejected solver attempts, accumulated error, and commit ownership.

The numerical implementation already distinguishes these operations. `Numerical.run` returns `none` for a rejected sequence (`Applications/Orbifold/NumericalExecution.lean:14`), while `run_correct`, `run_append`, and `run_error` preserve endpoint relations, composition, and carried error (`:32`, `:56`, `:78`). The driver retains committed observations and pending events separately. `Driver.drive` gives retries the same incoming packet; only accepted intervals advance it (`Applications/Orbifold/Driver/Execution.lean:27`). `drive_partition` proves the committed/pending partition (`:72`). These facts should guide the phase boundary instead of being hidden behind a function returning a value at a time.

A relevant external alternative is the hybrid synchronous organization of [Bourke and Pouzet, Zélus, HSCC 2013, sections 3.1–3.2](https://www.di.ens.fr/~pouzet/bib/hscc13.pdf). Its compiler separates combinational, discrete, and continuous blocks; discrete changes and side effects occur on discrete clocks. Continuous evaluation can be repeated by a solver while discrete state is held fixed. Causality analysis requires discrete loops to contain delays and continuous loops to contain integrators. This is evidence for a useful execution boundary, not a proof of numerical accuracy, termination of every zero-time reaction sequence, or compatibility with this repository's strict switching.

**Smallest correction:** before declaring A's phase interface reusable, add one finite numerical client that distinguishes evaluation attempts from committed advancement. Reuse the existing driver rather than writing another integrator. An exact affine client can remain the initial evaluator example, but cannot close the numerical boundary question.

**Discriminating test:** from one incoming packet, make one unsuccessful subdivision attempt and one successful attempt, query the same endpoint twice, then switch control and continue. Require unchanged committed state after the failed attempt, no extra discrete tick or publication from repeated evaluation, carried error after switching, and correspondence with existing `run_append`. Also query a later endpoint after an earlier query and compare with the declared chunking/error contract. Exact output equality between different numerical partitions should not be assumed.

**Compatibility:** retain mathematical `Behavior` and `RNF`. Stateful numerical evaluation may expose a residual packet and a commit operation without changing the exact denotation. A new generic phase law is justified only after the client shows which laws are needed; the existing numerical append/error results should discharge their part.

## ALT-3: Scalar source frontiers should not become a graph-wide readiness barrier

**Status:** unanswered design choice. The candidate does not explicitly require a global barrier, so this is a constraint on the next design, not a defect in existing code.

`Frontier.observeMerge` waits for both source frontiers because its observation is the complete ordered concatenation of both batches (`Applications/FRP/Frontier.lean:123`). That requirement is correct for this merge. It does not imply that a query for a node depending only on the left source must wait for the right source. Nor does it require a single minimum frontier for every node of D.

A paper separating case is a graph with one output depending only on source L and a second output merging L and R. L certifies time t, while R remains silent without certifying t. The first output can be determined under all completions of its dependencies; the merged output cannot. A global barrier preserves soundness but can destroy the useful independent progress that motivates asynchronous scheduling. The proposed conditional-progress statement should identify dependency-specific source completion, otherwise it may mask this loss by demanding unrelated completion.

[Naiad, SOSP 2013, section 2.3](https://www.microsoft.com/en-us/research/wp-content/uploads/2013/11/naiad_sosp2013.pdf) provides a different placement of progress knowledge: timestamped locations and graph path summaries determine whether outstanding work can still cause an event at a requested location/time. Notifications become eligible when no active predecessor remains. This depends on structured graph/time constraints and accounting for outstanding events; it is not a theorem that arbitrary operators are deterministic or that queues are bounded. It suggests comparing local dependency knowledge before generalizing the scalar merge protocol.

**Smallest correction:** specify readiness per requested observation and its dependencies. For D's fixed DAG, finite predecessor sets may suffice; do not import distributed pointstamp machinery without a client needing it. Keep the existing two-source merge as a specialization.

**Discriminating test:** the independent-output example above, followed by cancellation of one owner of a shared dependency. Require the independent output to complete without R, the merged output to remain pending, and surviving ownership to prevent premature cancellation. This tests progress and ownership separately from output soundness.

**Compatibility:** preserve left-before-right ordered occurrences at a merge. Replacing ordered batches with an unordered dataflow multiset would change client semantics and is not justified by the external analogy.

## ALT-4: Live conversion tests the backend abstraction earlier than startup ranking

**Status:** sequencing recommendation; existing transport evidence is stronger than a need to invent a new generic simulation law.

B deliberately uses the function and circuit targets of the same initialized source. `ReactiveCompiler.realize` realizes both into `Val B s` (`SquareKit/ReactiveCompiler.lean:18`), and `realize_compile` proves equality at that representation (`:45`). This is useful compiler reuse, but cannot by itself test transfer between different retained-state encodings. The candidate recognizes that gap in G. Deferring the first G test until after policy instrumentation would delay the more consequential architectural question while exercising an already general chooser.

There is a smaller existing starting point than designing another target first. `Examples/IndefiniteService.lean` defines `redundant`, `related`, and `related_step`: a delayed Boolean is represented by a Boolean plus its complement. It already proves output transport and a retained-state bound. The new work is an executable transfer and session ownership, not another proof of all-suffix simulation. `Feedback.run_related` (`Applications/Progress/Reactive.lean:93`) takes any related starting states, so it applies after a consumed prefix; stream transport can likewise use machines initialized at the transferred states.

**Smallest correction:** bring a between-ticks conversion experiment alongside the first session package. Let an explicit migration command select the pair; ranking remains optional. Conversion `x ↦ (x,!x)` and projection back give a small concrete pair with existing simulation evidence. This does not replace G's eventual pending-work contract or C's artifact requirement.

**Discriminating test:** consume a prefix that leaves a noninitial delayed value, convert in both directions, and compare every suffix through the existing transport results. Include failed preparation and a stopped sink to test authority and deferral. Charge both retained states during preparation. A test merely comparing the last published value would miss reset corruption.

**Compatibility:** preserve B's session-start policy functionality if useful; do not require it for direct library use or explicit migration. The sample pair establishes transfer feasibility, not performance benefit or a universal converter.

## A third execution organization worth retaining as a comparator

[Elliott, Push-Pull Functional Reactive Programming, Haskell 2009, sections 7–12](https://conal.net/papers/push-pull-frp/push-pull-frp.pdf) supplies a compositional alternative to global graph scheduling: reactive values select nonreactive time functions, monotonic sampling returns residual computations, and futures/improving values expose partial temporal knowledge. Its unambiguous choice requires alternatives to agree wherever both are defined; it is not arbitrary racing of effectful jobs. The paper explicitly identifies cleanup of nested losing work as a concern. Its integration discussion relies on interval additivity and retained previous samples, without providing the repository's numerical certificates.

A bounded direct library implementation of phase composition and residual sampling should therefore remain a comparator to D. It could retain denotational composition with less explicit graph machinery, but would still need explicit Lean ownership, sharing, reclamation, and resource evidence. Host-language laziness or the paper's concurrent implementation cannot be assumed to supply those properties. This alternative deserves a matched client even if its first Lean representation differs substantially from the candidate.

## Evidence and limits

I inspected declarations and consumers in the archived source, including the compiler, feedback, finite circuit service, frontier merge, pipeline, byte driver, numerical execution, numerical driver, `Examples/ReactiveTarget.lean`, and `Examples/IndefiniteService.lean`. Source declarations described as proved have proof bodies in that archive; I did not run Lean, rebuild, audit, benchmark, or execute new counterexamples. The tests above and the independent-output separating case are paper proposals. No target files, caches, issues, or external messages were changed.

I read the required archived guidance, relevant ADRs 0001/0002/0008/0010, and the example-driven-development statement/counterexample criteria. External evidence comes from the fixed 2009, 2013 HSCC, and 2013 SOSP papers linked above. Fetching the separate Zélus CC 2015 PDF timed out; no conclusions rely on that unavailable paper. This is a focused comparison, not a survey of all FRP, hybrid semantics, effect systems, or verified compilers. I did not inspect an external implementation or reproduce its guarantees in Lean.

Missing evidence includes a real workload requiring a global demand graph, measured overheads against direct composition, a phase authoring trial using rejected numerical attempts, and a constructed running-session ownership transfer. The candidate already calls for several of these guarantees; my recommendation changes when and how they are tested.

I had no prior involvement in this project available in my task context. I accessed only the supplied local archive and external primary literature, not the original checkout, project history, live project issues, previous handoffs, or other judges' reports. The archive itself contains policy statements and historical issue references; these were read as supplied evidence, and none of their external project links were followed. No accidental exposure to withheld preferences is known. Available metadata identifies this as a Codex/GPT-6-family agent through the governing instructions; an exact model build and sampling configuration were not exposed. Independent report writing does not establish model diversity or independent proof checking.

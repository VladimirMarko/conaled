# Temporal proof objects and FRP delivery observations

Research for [#205](https://github.com/VladimirMarko/conaled/issues/205),
2026-10-28. Local declarations inspected at
`c4f469dd2dfdf4dce471fb355b9ab478d3d62dd5`. This note specifies the bounded
experiment for [#206](https://github.com/VladimirMarko/conaled/issues/206) and
the monitor scope for [#207](https://github.com/VladimirMarko/conaled/issues/207).
The proposed definitions and theorem obligations below are not implemented or
claimed as checked Lean results.

Use **discrete processing steps** for the first temporal interpretation, with
FRP query timestamps retained as separate values. Adapt a next/until witness
fragment and connect it to the existing one-shot demand trace. Keep its
proof-object interpretation separate from the online machine whose behavior
it certifies. Reuse the existing finite evaluation and stream-processor laws
for executable observations. This delivers a useful temporal correspondence
without claiming a port of an entire reactive language or a synthesis engine.

## Which temporal correspondence applies?

| Primary source and fragment | Clock, proof meaning, and computation | Assessment for this experiment |
|---|---|---|
| [Jeffrey, Functional Reactive Types, sections II–IV](https://asaj.org/papers/lics14.pdf) | Discrete time; a family `A : Nat → Type` has a stream of witnesses `∀ n, A n`. FRP combinators also express constructive temporal rules, including streams of types. | Adopt time-indexed witness families. A function on complete streams still needs a separate no-lookahead theorem. The paper's Agda development is source evidence, not a Lean dependency we have built. |
| [Davies, A Temporal-Logic Approach to Binding-Time Analysis](https://www.cs.cmu.edu/~fp/courses/15816-s10/papers/Davies96.pdf) | The next modality of constructive linear-time logic corresponds to binding-time levels in `λ○`; Mini-ML○ has stage-respecting operational semantics. | Keep phase time distinct from processing time. Residual code for a next stage does not schedule an FRP response. Staging is owned separately by #214. |
| [Bahr–Graulund–Møgelberg, Lively RaTT, v2, sections 1–2 and 4](https://arxiv.org/pdf/2003.03170v2) | Discrete reactive steps; inductive until requires eventual delivery. A separate guarded-recursion modality supports recursive objects. The language proves causality, productivity, liveness and an operational space discipline. | Borrow the finite-until distinction. Do not equate temporal next with guarded later or import its fixed point. Its space result depends on its language and machine, and does not apply to retained FRP logs. |
| [Sterling–Harper, Guarded Computational Type Theory](https://arxiv.org/abs/1804.09098v1) | Guarded dependent types use later and clock variables; clock intersection supports a broader class of productive coprograms. It is a computational language and a metalanguage for other semantics. | Useful for a later recursive object model. A clock abstraction is not a physical-clock bound or a source-advancement guarantee. No guarded recursion is needed in the selected fragment. |
| [Vardi–Wolper, An Automata-Theoretic Approach to Automatic Program Verification](https://www.cs.rice.edu/~vardi/papers/lics86.pdf) | Classical temporal properties of infinite computations are related to automata and verification. | Formula recognition is distinct from constructive inhabitants. Our bounded monitor has its own finite-prefix semantics below; it is not justified solely by an infinite-word automata theorem. |
| [Pnueli–Rosner, On the Synthesis of a Reactive Module](https://doi.org/10.1145/75277.75293) | Reactive synthesis asks for a module responding to environment inputs under a temporal specification, rather than merely a satisfying trace. | A future synthesis route needs an input/output game, strategy observation order, and realizability proof. The present adapter supplies none of those by itself. |
| [Clarke–Emerson, branching-time synchronization skeletons](https://www.cs.cmu.edu/~emc/papers/Invited%20Conference%20Articles/Design%20and%20Synthesis%20of%20Synchronization%20Skeletons%20Using%20Branching%20Time%20Temporal%20Logic.pdf) | Branching-time specifications distinguish possible executions through path quantification. | A theorem for one fixed action sequence is not a theorem for every scheduler. An eventual response on some branch does not establish delivery on all admissible fair branches. |
| [Alur–Henzinger, Real-time Logics: Complexity and Expressiveness](https://research-explorer.ista.ac.at/record/4589) | Timed state sequences add a time interpretation; expressiveness and decidability depend on the chosen logic and time structure. The cited assessment studies discrete time. | Metric and dense-time cases remain separate survey entries. Processing indices do not inherit timestamp distances; no decidability result here is transferred to arbitrary real-indexed behaviors. |

The adaptation is deliberately smaller than these languages. It certifies
finite waiting and gives a causal executable consumer using existing APIs.
It does not claim completeness for constructive LTL, a normalization theorem
for Lively RaTT, or equivalence between all temporal logics and FRP.

## Current declarations and ownership

The following are existing results, inspected in their source files.

| Local entry point | Reuse and boundary |
|---|---|
| [Spec](../../Applications/FRP/Spec.lean) | `Behavior α := ℝ → α`; `Causal` is real-prefix noninterference. `Event` includes `never`, and `warp` permits offline reindexing. A value of `Behavior` or `Event` alone is not an online guarantee. |
| [Trace](../../Applications/FRP/Trace.lean) | `run`, `count`, `sourcePrefix`, `observe_ready`, `run_persists`, `eventual_observation`, `traceRep`, and `executionSquare` already connect processing to known batches and source truth. `process` consumes a rejected message while preserving its state. |
| [Demand](../../Applications/FRP/Demand.lean) | `request`, `response`, `responseFor`, `responseSquare`, `pending_or_emitted`, `at_most_once`, and `eventual_response` supply the one-shot consumer contract. An emission is transient; the absorbing `done` state is persistent. |
| [Finite evaluation](../../Applications/Progress/Evaluation.lean) | `Evaluates`, fuel-bounded `search`, `search_sound`, `search_complete`, and `searchSquare` supply the existing operational certificate boundary. Fuel exhaustion means unknown. |
| [Producers](../../Applications/Progress/Streams.lean) | `Delivers`, `Productive`, `productive_of_next`, and guarded/paused examples distinguish finite observation delivery from termination of an infinite object. Reuse them when a producer is actually supplied. |
| [Processors](../../Applications/Progress/Processors.lean) | `Mealy`, `runList`, `runStream_prefix`, `mealy_delivery`, and `mealySquare` provide synchronous finite-prefix computation and transport. `Progress.Causal` is relative to `demand n`, which can exceed `n`; `dropProcessor 1` is the existing counterexample to interpreting that property as no lookahead. |
| [Constant-sheaf streams](../../Examples/ConstantSheafStreams.lean) | `prefixIso`, `comparison_not_iso`, and `transported_not_final` show why preservation of every finite prefix cannot silently be strengthened to preservation of the full stream object. |

[#131](https://github.com/VladimirMarko/conaled/issues/131),
[#144](https://github.com/VladimirMarko/conaled/issues/144), and
[#146](https://github.com/VladimirMarko/conaled/issues/146) are accepted sources
of those bounded contracts, not work to repeat. The new obligation is the
temporal witness/operational observation comparison.
[#27](https://github.com/VladimirMarko/conaled/issues/27) retains runtime scope;
[#30](https://github.com/VladimirMarko/conaled/issues/30) owns the existing demand
experiment; [#31](https://github.com/VladimirMarko/conaled/issues/31) owns its
incremental command machine. Its implementation is not a blocker: the reference
trace already computes the observations needed here. The
[demand record](frp-demand.md) and [trace record](frp-traces.md) explain their
accepted operational and source assumptions.

## Clock and observation choices

Fix `T`, `[LinearOrder T]`, payload type `α`, initial inputs `s`, message streams
`ms`, and actions `a`. Use natural-number transition indices `n` throughout the
temporal fragment. Keep the query `t : T` fixed during a one-shot run.

Define abbreviations for existing operations:

```text
S n = Trace.run s ms (Demand.sourceSchedule a) n
Q n = Demand.request s ms a n
R n = Demand.response s ms a n
O n t = Trace.observe (S n) t
```

`S n` and `Q n` are the states **before** action `a n`. `R n` is the emission
of that action, computed from those states. The request after that action is
`Q (n+1)`. Thus `R n = some (t,out)` implies `Q n = pending t` and
`Q (n+1) = done`; it does not imply `Q n = done`. A registration at action
`r` can first be pending at state `r+1`. Responses require a strictly earlier
registration, as `pending_registered` proves.

The observable frame is `(Q n, O n t, R n)`, with query `t` fixed externally.
It retains three distinctions:

- `O n t = none` means the query is not yet certified by both source frontiers.
  `O n t = some []` is certified silence, with a strict `t < frontier` test.
- `R n = none` means no emission at this transition; it can occur before
  registration, while waiting, or after delivery. It is not a truth value for
  whether the source event exists.
- A validated packet establishes structural admissibility. The `traceRep ms`
  relation additionally requires initial validity, initial completion and
  `Honest` accepted windows, including omitted timestamps, to identify output
  with external truth.

No sampling of `ℝ → α` is required. The bridge works for the existing ordered
timestamp parameter, with rational examples executable and real timestamps
usable semantically. A later sampling map `τ : Nat → ℝ` would require its own
monotonicity, coverage and observation assumptions. It cannot recover arbitrary
events between samples, establish physical latency, or exclude Zeno behavior
merely from an increasing processing index. Inserting idle steps changes next
and bounded-until observations even when eventual delivered batches agree.

## Proposed next/until certificate fragment

The first representation is a **trace-indexed certificate calculus**. It is
not a type system claiming that every denotation is an online strategy.
This separation lets #206 prove the correspondence it actually uses while
retaining a precise route to a richer modal language later.

Choose atomic symbols `Atom` and valuations `V : Atom → Nat → Type u`.
Formulas are `atom p`, `unit`, `A × B`, `next A`, and `A until B`.
There is no general recursion, guarded fixed point, implication, clock
quantification or dependent object-language binder in this first fragment.
Payload dependence remains in atomic valuations. Define meanings:

```text
⟦atom p⟧ n    = V p n
⟦unit⟧ n      = PUnit
⟦A × B⟧ n     = ⟦A⟧ n × ⟦B⟧ n
⟦next A⟧ n    = ⟦A⟧ (n+1)
⟦A until B⟧ n = Until (⟦A⟧) (⟦B⟧) n

Until.now  : B n → Until A B n
Until.wait : A n → Until A B (n+1) → Until A B n
```

`Until` is inductive in `Type`, so each inhabitant contains a finite sequence
of waiting witnesses and a terminal witness. `Eventually B = unit until B`.
The proposed equivalence, with mutually inverse conversions, is

```text
Until A B n ≃ Σ k : Nat, ((j : Fin k) → A (n+j.val)) × B (n+k).
```

The wait interval is `[n,n+k)` and the terminal position is `n+k`. `k=0`
requires no `A`, and permits immediate `B`. This is strong until; a never
arriving event has no inhabitant when every `B n` is empty. An inductive
certificate can expose its finite horizon during proof processing; that
does not make future source input available to an online consumer.

Contexts are finite lists of **absolute time-labelled** assumptions `(m,A)`.
`Γ ⊢[n] A` is an inductive family in `Type`. A variable uses an occurrence of
`(n,A)` in `Γ`; unit, pairing and projections have their ordinary same-time
rules. The remaining rules are:

```text
Γ ⊢[n+1] A                     ⇒ Γ ⊢[n] next A
Γ ⊢[n] next A                  ⇒ Γ ⊢[n+1] A
Γ ⊢[n] B                       ⇒ Γ ⊢[n] A until B
Γ ⊢[n] A, Γ ⊢[n+1] A until B  ⇒ Γ ⊢[n] A until B
```

Next elimination moves the judgment to `n+1`; there is no `next A → A`
eliminator at `n`. Future assumptions remain visibly time-labelled. The
environment is the dependent product of their interpretations, and evaluation
maps a derivation and an environment to `⟦A⟧ n`. This environment may contain
future certificates, so evaluation alone is not a causality proof.

For a concrete waiting witness of horizon `k`, use a context containing
`(n+j, atom pending)` for each `j < k` and `(n+k, atom delivered)`.
Iterated wait/now constructs a derivation in that context; the inspected trace
supplies its environment. Evaluation must recover the original finite witness.
This specifies the connection between derivations and observed data without
postulating a closed proof of an arbitrary atomic fact.

Use simultaneous substitution: a substitution `Δ ⇒ Γ` supplies, for every
occurrence `(m,A)` of `Γ`, a derivation `Δ ⊢[m] A`. Prove identity and
composition, and
`eval (subst σ d) η = eval d (evalSubst σ η)` by induction. The index must
remain unchanged through substitution. Weakening/exchange/contraction are
admissible for these certificate assumptions; no linear-resource claim follows.

Until elimination is structural recursion on its certificate. For arbitrary
`C : Nat → Type`, handlers `nowC : ∀ n, B n → C n` and
`waitC : ∀ n, A n → C (n+1) → C n` define `fold : Until A B n → C n`.
Prove its two constructor equations and the horizon equivalence. This is a
meta-level certificate eliminator, not an online instruction exposing `B`
before arrival. Derived `mapUntil` takes pointwise witness maps for `A` and
`B`; it preserves the horizon and composes. Those maps and the substitution
lemma are the initial reusable transport laws. No normalization, reflection
or completeness claim is required for this certificate fragment.

## Operational witnesses and conditional delivery

For the fixed demand run and query, use these atomic valuations:

```text
Pending n   = PLift (Q n = pending t)
Delivered n = Σ out : List α, PLift (R n = some (t,out))
Correct n   = Σ out : List α,
                PLift (R n = some (t,out) ∧
                       out = truth left t ++ truth right t)
```

The list and horizon are computational data; equality evidence is in `Prop`
and can be erased. `PLift` puts predicates into `Type` without recovering
information already erased by an existential proof.

Specify two distinct routes for #206:

1. **Conditional existence.** Under exactly the premises of
   `Demand.eventual_response`, prove
   `Nonempty (Until Pending Delivered i)` when `Q i = pending t`.
   The premises are a legal `Delivery (sourceSchedule a)`, its `Fair` proof,
   `ProcessingFair s ms a`, and for each source an available finite prefix
   whose frontier strictly exceeds `t`. Reuse `eventual_response`; select the
   earliest response in the finite prefix ending at the response it supplies.
   `pending_or_emitted` then proves pending at every earlier position.
   This theorem remains in `Prop`; it promises no extracted deadline.
2. **Executable bounded witness.** Define the existing `Progress.Machine`
   instance with state `j : Nat`: inspect `Demand.responseFor s ms a j t`;
   return `.inl (j,out)` on `some out`, otherwise `.inr (j+1)`.
   Run `Progress.search machine fuel i`. Reuse its soundness/completeness
   rather than adding a generic search engine. A successful result
   `some ((j,out),cost)` must establish `j ≥ i`, `cost = j-i+1`,
   response at `j`, and no response for this query on `[i,j)`.
   Together with `Q i = pending t`, package a witness of
   `Until Pending Delivered i` with horizon `j-i`. Construct the finite
   waiting proof from `Evaluates` and `no_lost_work`.

Provide a proof-carrying wrapper around that search which returns
`Option (Until Pending Delivered i)` under the pending precondition. It must
return `none` on insufficient fuel and must compute its horizon and payload
from the search result. Do not use `Classical.choose` to define its data.
Construct the `Until` data by recursion on the returned natural-number horizon;
use induction on `Evaluates` only to prove its `Prop` equality obligations.
There is no elimination of a multi-constructor `Prop` proof into computational
data. Payloads come from the returned list, not an existential proof.
Prove `fuel_complete`: a first emission at `j ≥ i` is found whenever
`j-i+1 ≤ fuel`. The existence route therefore implies that some fuel succeeds,
not that a particular uniform fuel works under unbounded fairness delays.
The bounded search evaluates a supplied trace; it is not a live scheduler.

With `h : (Trace.traceRep ms).Rel s truth`, lift `Delivered` to `Correct`
pointwise using `Demand.responseSquare` and `responseFor_iff`, then apply
`mapUntil`. This is the proposed commuting comparison between the temporal
witness and external semantic batches. Compose the terminal observation with
`mapObservation f` to obtain exactly
`List.map f (truth left t ++ truth right t)` without another delivery proof.
Honesty is required for this value comparison, not for existence of emission.

An arbitrary `Until unit Delivered` witness need not be the earliest response;
the specific search constructor chooses the first one. Avoid making minimality
part of every temporal witness or every model. Native `Event.never` can map to
a stream with no emissions, but cannot map to guaranteed `Eventually Delivered`
without an additional, satisfiable progress premise.

## Causality, productivity and retention obligations

For synchronous stream functions define the intended observation contract as

```text
prefixOf x k = prefixOf y k
  ⇒ prefixOf (F x) k = prefixOf (F y) k.
```

Reuse `Progress.mealyProcessor` with demand `id`, `runStream_prefix`,
`mealy_delivery`, and `mealySquare`. An initial example maps response payloads
by `List.map f` while preserving `none` and `some []`. A second example is a
prefix scan accumulating the number of actual emissions; it depends only on
the input observed so far. `compose_delivery` and `composedMealySquare` supply
composition without a new processor framework.

`Progress.Causal` for general processors permits the declared input demand
`p.demand k`. To deduce the synchronous property require `p.demand k ≤ k`
for every `k`, then restrict prefix equality using `prefix_take`.
`dropProcessor 1` can satisfy the demand-relative contract while failing the
synchronous contract. The Boolean shift `F x n = x (n+1)` supplies a negative
case: inputs agreeing at index zero can differ at index one and thus yield
different first outputs.

Also prove a **reference-trace prefix theorem**: for the same initial states,
two action streams agreeing for every `j ≤ n` and two message streams agreeing
at every source index `k < n` have equal `R n`. Before step `n` at most `n`
messages were consumed; `request` uses only actions before `n`, and `emit`
uses the current action. Induction on `request` and `Trace.run_step` proves
this without fairness or honesty. This sufficient finite-input bound is not
claimed minimal. It prevents a total Lean trace function from being accepted
as online merely because it terminates on each requested index.

Productivity of **frames**, which include `none`, is different from repeated
delivery of responses. A Mealy map over frame inputs has finite delivery for
each supplied finite input prefix. Filtering out `none` can wait forever;
the one-shot demand machine emits at most once, so it cannot be a productive
infinite producer of response values. Reuse `Progress.filter_no_match` and
the stalled demand case to preserve this distinction. Processing fairness
does not manufacture available closing source messages, and source fairness
does not schedule enabled consumer work.

No retention or space theorem is proposed. Current traces retain logs and
recompute prefixes. Atomic transition counts in `Progress` omit the host cost
of computing a transition. A space bound would need explicit retained-state,
allocation, reclamation and input-access models, owned with #31/#27 and the
resource work. The next/until distinction alone establishes none of them.

## Required examples and statement checks for #206

Reuse [FRPDemand](../../Examples/FRPDemand.lean) and
[FRPTrace](../../Examples/FRPTrace.lean) as the source of concrete cases.
The new checked applications exercise the temporal adapter, not duplicate
the existing fairness and truth proofs.

| Case | Exact proposed temporal check |
|---|---|
| `start`, `packets`, `late`, query `2` | Initial frontiers are `2`; right then left packets close to `3`; registration is action `2`; state `3` is pending; response `3` is `(2,[3,4,3])`. At `i=3`, horizon `0` and fuel `1` suffice. Reuse `available`, `available_fair`, `processing_fair`, and the closing-prefix proof with one packet per source. |
| Same packets, `early`, query `2` | State `1` is pending. Responses at `1,2,3,4` are absent; response `5` is `[3,4,3]`. Produce four wait constructors followed by now; fuel `5` succeeds and fuel `4` returns unknown. This checks the boundary indexing. |
| `emptyQuery`, query `1` | Response at `1` is `some (1,[])`. The terminal witness contains the empty list, not an empty type or absent response. |
| `stalled` with `late` | Fair source consumption and consumer processing hold, but no prefix closes query `2`. Reuse the all-step no-response theorem to refute any `Until unit Delivered i` witness. |
| `starved` with `packets` | Available closing prefixes and fair source consumption hold; processing fairness fails and responses are always absent. No temporal witness can be manufactured from source progress alone. |
| Always-idle source schedule | Closing packets may be available; `Delivery.Fair` fails. This separates source availability from consumption. |
| Dishonest accepted source window | Structural acceptance can preserve an internally computed output while external truth disagrees. The value comparison requires `traceRep`; the emission witness alone must not discharge it. |
| Mapped consumer and prefix scan | Reuse Mealy proofs for synchronous causality and finite frame delivery. Compose the value adapter; compare with shift and with filtering out all absent responses. |

Before accepting the formal statements check that the pending premise is
satisfiable without presupposing a response, all frontier inequalities are
strict, the terminal list retains order and duplicates, and `until` excludes
its terminal index from the waiting interval. Check zero wait, zero fuel,
known-empty emission and post-delivery `none`. For transport, assert only
the observed finite witness; #144 rules out promoting the result to a general
stream-object equivalence. Formal implementation must use example-driven
development, statement review, the applicable fresh build and proof audit,
and independent review. This research note itself introduces no Lean claims.

## Bounded monitoring contract for #207

Choose processing-step formulas
`atom p | not φ | and φ ψ | next φ | untilWithin h φ ψ` with `h : Nat`.
Atoms are **total decidable predicates of the observable frame**, not predicates
of unknown source truth. Initial atoms include pending query, certified-ready
query, response present and response equal to a supplied list (the last needs
decidable payload equality). `O=none` is a known fact about knowledge, not a
false assertion about the underlying source event.

Define independent satisfaction on infinite frame traces. `next` shifts by
one processing step. Bounded until holds at `n` iff some `k ≤ h` satisfies
`ψ` at `n+k` and `φ` holds at `n+j` for every `j<k`. Define the structural
lookahead bound:

```text
H(atom p)=0; H(not φ)=H(φ); H(and φ ψ)=max(H(φ),H(ψ));
H(next φ)=1+H(φ); H(untilWithin h φ ψ)=h+max(H(φ),H(ψ)).
```

For the first implementation, the monitor stores the prefix from its requested
start index. It returns `pending` until it has `H(φ)+1` frames, then evaluates
the finite semantics and returns `satisfied` or `violated`. Terminal verdicts
are absorbing. This conservative monitor need not report every violation as
early as possible. Its finite retention bound is relative to formula horizon,
and counts frames, whose payload lists may be arbitrarily large. It is not a
byte bound, a bound for the FRP source logs, or a general online formula optimizer.

Prove finite-evaluation agreement for every infinite extension of the observed
prefix, soundness of terminal verdicts, completeness once enough frames are
present, and fold composition over concatenated input prefixes. Early
end-of-input before the horizon remains `pending`; there is no implicit
end-of-trace assertion. Test `untilWithin 4 Pending Delivered` on the early
example from index `1`, and the bound `3` on the same trace. Include a
known-empty terminal answer, delayed knowledge, idle steps, and a rejected
packet. Rejection can preserve source knowledge yet consumes a processing
position, so next and step-bounded formulas are not generally invariant under
its insertion.

Unbounded eventuality is outside this decidable fragment: a prefix with no
response has both a no-response extension and an extension with a later
response. The monitor cannot conclude either infinite future from that prefix.
A hypothetical Boolean specification `output n = input (n+1)` has satisfying
complete traces but no causal implementation against unrestricted future
inputs: two environments can share the current prefix and choose different
next inputs. These are distinct reasons why monitoring is not synthesis.

## Remaining routes and adoption decision

Proceed with the certificate fragment, bounded search adapter and existing
Mealy consumer. Treat the derivation interpreter, conditional existence theorem,
executable witness search and online causality theorem as separate deliverables.
Their comparison is the new reusable result. Ordinary callers should use the
existing demand/progress functions plus witness constructors; encoded
derivations remain opt-in, consistent with the
[shared language direction](../language-direction.md).

Actual controller synthesis still needs controlled/uncontrolled actions and a
winning-strategy contract. Branching-time claims need quantification over
admissible executions. Metric deadlines need a clock map and delay bounds;
dense-time claims additionally need an appropriate behavior/event semantics.
Probabilistic liveness needs a measure and an almost-sure or quantitative
contract, rather than replacing universal fairness by an informal likelihood.
The existing [probabilistic progress work](../probabilistic-progress.md) is a
source of separate contracts, not an automatic premise for this deterministic
bridge. Recursive modal programs and memory reclamation require additional
language and operational work. None is needed to validate the selected finite
correspondence, and none is implied by it.

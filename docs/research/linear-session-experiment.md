# Finite linear protocols as communicating processes

[Issue #212](https://github.com/VladimirMarko/conaled/issues/212) implements a
finite additive/unit session fragment. A proof translates to a typed process;
principal proof-cut reductions simulate synchronous communications. The checked
client selects twice on one session, closes it, then runs a second typed session.
Its observable result is a five-event communication trace and an explicit
remaining endpoint. This is not a theorem about unrestricted concurrent programs.

## Selected calculus and context discipline

The source is [Wadler, *Propositions as Sessions*, ICFP 2012, §2 and Figures 1
and 3](https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-sessions/propositions-as-sessions.pdf).
The selected CP rules are additive selection/offer, multiplicative close/wait,
and cut. Contexts assign types to distinct channel names; cut combines disjoint
remaining contexts. The duals exchange `1` with `⊥` and `A ⊕ B` with
`A.dual & B.dual`. Selection communicates which offered continuation will run.
Close synchronizes with wait and releases the waiting continuation.

[Session.Process](../../SquareKit/Session/Process.lean) presents contexts as lists
with explicit exchange. `Valid` requires distinct names, regardless of their
types. `Typed.valid` proves every typed context satisfies this requirement.
The rules are:

| Rule | Premises and conclusion |
|---|---|
| close | `close x : x:1` |
| wait | `p : Γ`, fresh `x`; `wait x p : x:⊥, Γ` |
| select left/right | `p : x:A, Γ` or `p : x:B, Γ`; selection has `x:A⊕B, Γ` |
| offer | `p : x:A, Γ` and `q : x:B, Γ`; offer has `x:A&B, Γ` |
| cut | `p : x:A, Γ`, `q : x:A.dual, Δ`, disjoint remaining names; cut has `Γ,Δ` |
| exchange | permute a context without changing the process |

The offer rule shares the remaining context between alternative branches;
only one branch executes. It does not run both branches with the same resource.
There is no weakening, contraction, Mix, general parallel operator, channel
payload transmission, channel delegation, link rule, recursive type or recursive
process. The formalization omits CP commuting conversions and symmetric cut
congruence. Its operational relation contains only the three displayed
principal communications in the selected orientation.

`Proof Γ` retains derivation data in `Type`. `Process` is separate syntax without
type annotations; `Typed p Γ` is its judgment in `Prop`. `Proof.erase` removes
the proof bookkeeping, and `Proof.typed` proves translation typing.
`CutStep` relates actual proof derivations at the same residual context.
`CutStep.simulates` maps each such reduction to `Step` on their erased processes.
This is a proof/process theorem, not a conclusion inferred from an ordinary
function's input/output equality. The source-level preservation conclusion
comes from the unchanged context index. No general subject-reduction or
cut-elimination theorem for all CP processes is claimed.

## Focused completion and typed composition

[Session.Protocol](../../SquareKit/Session/Protocol.lean) packages the fragment
needed by ordinary protocol clients. A `Protocol` is a finite binary choice tree
ending in close. A `Selection` chooses a path. A `Receiver Γ` supplies both
branches and a separately typed `Proof Γ` continuation at every leaf. Different
leaves can contain different components, provided their external interface is
`Γ`. `connect` composes translated dual endpoints by the actual cut rule; the
session channel must be fresh for `Γ`.

`progress` proves that every such focused connection has a next communication.
`completes` proves a finite sequence of `Step` communications reaches the selected
leaf continuation. `Selection.length_le` bounds that phase by the finite protocol
tree's maximum branch depth, including close. These results require no fairness
assumption: they exhibit a finite execution in the specified principal-step
relation. They do not assert that an arbitrary external scheduler takes steps,
or that arbitrary typed CP networks reduce under these restricted rules.

`completes_then` composes the first actual reduction sequence with a supplied
execution of its selected continuation. It retains the continuation's linear
context rather than treating the first close as global termination.
The [checked network](../../Examples/SessionProtocol.lean) uses channel 0 for
left selection, right selection and close. The selected leaf is a second typed
session on channel 1, which selects left and closes. Its complete trace is

```
label 0 false, label 0 true, closed 0, label 1 false, closed 1
```

The residual process is `close 2`, with context `2:1`. A checked negative shows
it has no principal communication step by itself. An environment must provide
its dual peer before any further communication can be claimed. Other branches
of the first receiver go directly to that external close. This tests composition
with a distinct component, including a branch-dependent continuation.

## Independent trace contract and reuse

`Accepts channel protocol events` specifies permitted traces directly from the
protocol tree: a matching label followed by a permitted branch trace, ending
in close. It does not call process erasure, a process evaluator or `Step`.
`Selection.accepts` connects selected source paths to this language.

`Step.deterministic` and `Steps.same_length` show that executions of the selected
principal-step relation agree at equal lengths. `trace_refines` uses these laws
and actual completion to construct an existing
[Interaction.Refines](../../SquareKit/InteractionContracts.lean) contract. Every
actual execution through the phase's specified communication boundary has an
observation in the independent language. The target set explicitly fixes the
phase length. It is not a claim about arbitrary longer runs: those may include
the selected continuation. Zero-step prefixes are likewise not complete protocol
traces. The checked client applies `Interaction.Refines.property` to transfer the
protocol property that every event uses its declared session channel onto actual
process observations. No replacement behavior-set framework is added.

This interface shares trace refinement and sequential composition with existing
interaction work. Its linear endpoint contexts and synchronous rendezvous rules
are additional structure. FRP batches, pending requests and source progress do
not thereby become sessions. An adapter to
[#196](https://github.com/VladimirMarko/conaled/issues/196) would need an explicit
mapping of communication events to obligations and evidence, plus its own
preservation theorem. The [cross-domain integration assessment](correspondence-contracts-and-integration.md)
therefore gains a concrete trace-refinement consumer, but no universal source
syntax or automatic session adapter.

## Client effort, rejected compositions and limits

Ordinary Lean clients may construct `Process` terms and prove `Typed` and `Steps`
directly, as the separate channel-3 example does. Authors who want proof data may
use `Proof` and its erasure theorem. The `Selection`/`Receiver` layer handles
repeated typing and communication proofs once; a client does not repeat either
induction when composing protocols.

The composed example supplies two protocol trees, a two-selection path and a
one-selection path, receiver trees with three and two leaves, and the external
close component. It names three channels and discharges two freshness obligations
for the connections. The residual context remains explicit. The general layer
supplies duality, context validity, translation typing, principal simulation,
completion, trace refinement and composition. This is a bounded author interface,
not automatic extraction of protocols from ordinary Lean code or minimization
of a construction's logical requirements.

`no_duplicate` rejects any process typed with two uses of the same endpoint name,
including after exchange. A second checked case rejects combining two residual
contexts that each own endpoint 2. The current cut cannot compose those components
by silently duplicating the resource. Adding shared servers would require a
separate exponential discipline, including its admissible contraction/weakening
and replication rules, rather than deleting `Valid`.

`no_unbounded_server` proves a fixed finite protocol cannot supply arbitrarily
long communication traces. An unbounded service requires recursive protocol and
process structure, with separately stated productivity and progress assumptions.
The finite completion theorem does not establish that extension. Likewise,
asynchronous buffers, payloads, arbitrary network topologies and scheduler
fairness need additional operational contracts. No runtime-performance claim,
full abstraction, reverse extraction or general CP deadlock theorem follows
from this experiment.

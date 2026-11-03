Prompt 1:
````md
In https://www.youtube.com/watch?v=rfmkzp76M4M, Conal Elliott mentions that https://conal.net/papers/push-pull-frp/ failed. His slide (https://conal.net/talks/essence-and-origins-of-frp-lambdajam-2015.pdf) says the following:
```markdown
# 2009: Push-pull FRP
- Minimal computation, low latency, provably correct.
- Push for reactivity and pull for continuous phases.
- “Push” is really blocked pull.
- Modernized API:
  - Standard abstractions.
  - Semantics as homomorphisms.
  - Laws for free.
- Reactive normal form, via equational properties (denotation!).
- Uses lub (basis of PL semantics).
- Implementation subtleties & GHC RTS bugs. Didn’t quite work.
```
1) Trace back what actually happened.
In https://www.youtube.com/watch?v=9vMFHLHq7Y0 / https://github.com/conal/talk-2015-essence-and-origins-of-frp, Conal Elliott gives his newest formulation of the FRP specification to date.
2) Restate this using his later https://github.com/conal/felix approach mentioned in https://haskell.foundation/podcast/62/. Do this in Lean, if possible. (We might need to use Agda instead, because of Lean's incompetence with infinite data structures.) Make constraints that were not expressible in the 2015 Haskell work explicit. The specification should be elegant, which just means "simple, precise, and adequate".
3) Give a sketch of a correct push-pull FRP implementation with respect to the specification from (2) in Lean or Rust + Aeneas/hax + Lean. The idea is to at least fix (1), or even improve upon it conceptually. Highlight what needs to be proven.
````

Response 1:
````md
The historical evidence supports a narrower conclusion than “push-pull FRP was disproved”: **the implementation depended on a difficult interaction between lazy evaluation, speculative concurrency, cancellation, and GHC’s runtime. Some library problems and genuine runtime bugs were fixed, but Reactive was still published with unresolved bugs.** That does not certify every old instance or implementation equation, either; those need separate scrutiny. [GitHub](https://raw.githubusercontent.com/conal/unamb/master/wikipage.tw)

My proposed reconstruction keeps the simple denotation, but replaces *implicit information encoded by blocked thunks* with *explicit information and progress certificates*. The proof then has two distinct parts: preservation of denotation, and operational safety/productivity.

A source correction matters here: the second video has a separate companion repository, **`conal/talk-2015-more-elegant-frp`**. Its final event formulation—not merely the older representation as timestamped lists—is the appropriate starting point. [GitHub](https://github.com/conal/talk-2015-more-elegant-frp)

I have included a FRPSpec.lean[Lean specification draft](sandbox:/mnt/data/FRPSpec.lean). It contains the semantic definitions, categorical operations, homomorphism obligations, and several small proof scripts. **I did not have a Lean toolchain available to typecheck it; it is not a completed verified implementation.** The historical reconstruction below uses the papers, slide sources, code, and contemporaneous discussions, rather than a verified transcript of the videos.

## 1. What actually happened

### 1.1 Why concurrency entered an apparently pure implementation

The central difficulty is not producing a timestamped occurrence. It is deciding which occurrence comes first **without waiting for the later occurrence**.

Suppose one input will next occur at time \(10\), while another will next occur at time \(100\). A representation that must evaluate both exact timestamps before comparing them reacts at \(100\), not \(10\). The implementation therefore needs partial information: for example, knowing that the second input cannot occur before \(20\) is already enough.

The 2009 design addressed this using improving temporal information, futures, and unambiguous choice. Two computations could calculate the same answer by different routes; whichever established it first could supply the result. The agreement requirement is essential: this was not supposed to make program meaning depend on which unrelated input happened to win a runtime race. [Conal](https://conal.net/papers/push-pull-frp/push-pull-frp.pdf)

There are two orders here:

\[
\text{semantic time order}
\qquad\text{and}\qquad
\text{order in which information becomes available}.
\]

The implementation must exploit the second without accidentally substituting it for the first.

### 1.2 The documented failures were a combination, not one bug

| Period | What the primary record establishes |
|---|---|
| **December 2008: thread leaks** | Elliott’s initial race implementation killed its immediate competing threads, but not necessarily the descendants created by nested races. Losing speculative computations could leave substantial useless work running. [Conal](https://conal.net/blog/posts/smarter-termination-for-thread-racing/) |
| **December 2008: a representation/strictness bug** | Elliott changed `AddBounds (Improving t)` to `Improving (AddBounds t)` while fixing a `join`/`mappend` problem that delayed reactions. The placement of the improving-information layer mattered operationally; this was not simply a GHC defect. [Google Groups](https://groups.google.com/g/reactive-haskell/c/4kBYi5vpbVw) |
| **December 2008: cancellation and shared thunks** | More thorough cleanup exposed another problem. Exception handlers could turn cancellation into a synchronously rethrown exception, leaving a shared thunk permanently associated with `ThreadKilled`. Other arrangements suspended a computation whose resources had already been dismantled. [Haskell Mail](https://mail.haskell.org/pipermail/glasgow-haskell-users/2008-December/016395.html) |
| **January 2009: confirmed RTS defects** | Simon Marlow identified actual deadlocks involving `throwTo`, including a finished thread created with exceptions blocked continuing to block a sender. He explicitly distinguished these confirmed defects from the still-unexplained reports of bogus `<<loop>>`. [Haskell Mail](https://mail.haskell.org/pipermail/glasgow-haskell-users/2009-January/016433.html) |
| **Later outcome** | The `unamb` notes report recursive cleanup/restarting working with the January 15, 2009 GHC HEAD fixes, and later describe `unamb` 0.2.2 as working well with GHC 6.10.3. Nevertheless, Reactive 0.11.5, uploaded in July 2010, still warned of serious bugs, especially involving the `Event` monad. [GitHub](https://raw.githubusercontent.com/conal/unamb/master/wikipage.tw) |

The cancellation issue deserves precision. It is **not** generally true that killing any thread evaluating a pure expression permanently poisons that expression.

The problematic combination involved shared evaluation exposed through `unsafePerformIO`, cleanup handlers, and resumption. Bertram Felgenhauer’s diagnosis distinguished asynchronously interrupting a computation from catching the exception and rethrowing it synchronously through the usual cleanup machinery. The latter can change what a subsequent evaluation of the shared thunk sees. Marlow linked that exception-handling issue to GHC ticket **2558**. [Haskell Mail](https://mail.haskell.org/pipermail/glasgow-haskell-users/2008-December/016395.html)

The later `Data.Unamb` implementation documents the other half: restarting a suspended race cannot simply resume waiting on an old `MVar` after its producing threads have been killed. Its `restartingUnsafePerformIO` machinery was intended to restart the action appropriately. Thus, both **cleanup ownership** and **restart semantics** mattered. [GitHub](https://raw.githubusercontent.com/conal/unamb/master/src/Data/Unamb.hs)

### 1.3 What can—and cannot—be concluded

The strongest surviving statement about the remaining Reactive bugs is Elliott’s own package description: some problems had been GHC concurrency bugs, but he did not know whether the residual failures were further runtime problems or subtle laziness bugs in Reactive. [Hackage](https://hackage-content.haskell.org/package/reactive)

Consequently, I would not identify one particular RTS ticket as *the* explanation for the 2015 slide. The record supports this reconstruction:

> The algebraic design relied on operational properties of partial information and unambiguous choice. Implementing those properties with shared lazy thunks, asynchronous cancellation, and runtime black-hole machinery proved substantially harder than deriving the higher-level combinators.

That is an interpretation of the combined evidence, not a newly discovered final postmortem. In particular, “the RTS fixes landed” and “Reactive became reliable” are not equivalent claims.

The lesson for a verified replacement is important: **a semantic homomorphism proof above an assumed primitive does not establish that the primitive’s implementation has the required operational behavior.**

## 2. A Felix-style restatement in Lean

### 2.1 Preserve the 2015 simplification

The final “More Elegant FRP” formulation treats an event as a behavior of lists, with a sparsity condition:

```haskell
newtype Event a = Event (Behavior [a]) -- discretely non-empty
```

Behaviors retain real-valued semantic time, and the standard operations are specified by preservation of their corresponding semantic operations. The presentation also explicitly says that the equality used to inherit laws is **semantic equality**. [GitHub](https://raw.githubusercontent.com/conal/talk-2015-more-elegant-frp/lambdajam-2015/more-elegant-frp.lhs)

The unresolved phrase is “discretely non-empty.” It should become a condition, not remain a comment.

I propose the following **total, initialized fragment**:

\[
\begin{aligned}
\mathsf{Behavior}\,A
  &:= \mathbb R\to A,\\
\mathsf{Event}\,A
  &:= \left\{
       e:\mathbb R\to\mathsf{List}\,A
       \;\middle|\;
       \forall t,\ 
       \{s\mid s<t\land e(s)\ne[]\}\text{ is finite}
      \right\}.
\end{aligned}
\]

In Lean:

```lean
import Mathlib

abbrev Behavior (α : Type) := ℝ → α

def PastSupport {α : Type}
    (e : ℝ → List α) (t : ℝ) : Set ℝ :=
  {s | s < t ∧ e s ≠ []}

structure Event (α : Type) where
  at : ℝ → List α
  finite_past : ∀ t, (PastSupport at t).Finite
```

This choice makes three decisions explicit.

**Simultaneous occurrences form a finite ordered batch.** A list retains multiplicity and order; it is not a set.

**An infinite future is allowed.** Finiteness is required only before each finite observation horizon.

**Infinite prehistory and finite-time accumulation are excluded.** This is deliberately stronger than merely saying that each occurrence time is isolated.

For example, the times

\[
t_n=1-\frac{1}{n+2}
\]

are individually isolated, but there are infinitely many before \(1\). A generic “take the last update before \(1\)” operation is then undefined. Past-finiteness removes that problem.

This is a refinement of the informal specification, not a claim to model every divergent or Zeno-valued Haskell expression. An alternative is locally finite events on all of \(\mathbb R\), together with an explicitly supplied initial state at an origin \(t_0\). The important requirement is **finite relevant history plus initialization**, not this particular packaging.

### 2.2 Most operations really are immediate

For behaviors:

\[
\begin{aligned}
\mathsf{pure}(a)(t)&=a,\\
\mathsf{map}(f,b)(t)&=f(b(t)),\\
\mathsf{ap}(f,b)(t)&=f(t)(b(t)),\\
\mathsf{time}(t)&=t.
\end{aligned}
\]

For events:

\[
\begin{aligned}
\mathsf{never}(t)&=[],\\
\mathsf{mapE}(f,e)(t)&=\mathsf{List.map}\ f\ (e(t)),\\
(e_1\mathbin{\oplus}e_2)(t)&=e_1(t)\mathbin{+\!\!+}e_2(t),\\
\mathsf{snapshot}(e,b)(t)
  &=\mathsf{map}\;(\lambda a.(a,b(t)))\;(e(t)).
\end{aligned}
\]

The support proofs are elementary. Mapping and snapshotting do not enlarge support; merging takes a subset of the union of two finite supports.

Event merge needs **no `Monoid A` constraint**: the monoid operation is list concatenation. It is associative, but not generally commutative. Consequently, an implementation must not let thread scheduling choose the order of simultaneous occurrences.

“Continuous time” here concerns the domain. It does not assert that every behavior is a topologically continuous function; switching itself can introduce discontinuities.

### 2.3 Preserve the strict switching boundary

The historical specification is explicit: switching at \(\tau\) affects times **strictly after** \(\tau\), not the value at \(\tau\). [Conal](https://conal.net/talks/essence-and-origins-of-frp-lambdajam-2015.pdf)

Let \(\mathsf{past}(e,t)\) concatenate the batches before \(t\), ordered by timestamp and preserving each batch’s list order. Then:

\[
\mathsf{switcher}(b_0,e)(t)
=
\left(
  \mathsf{foldl}\;(\lambda\_\,b.\,b)\;b_0\;
  \mathsf{past}(e,t)
\right)(t).
\]

The corresponding Lean definition is small:

```lean
noncomputable def past {α : Type}
    (e : Event α) (t : ℝ) : List α := by
  classical
  exact (((e.finite_past t).toFinset).sort (· ≤ ·)).flatMap e.at

noncomputable def switcher {α : Type}
    (initial : Behavior α)
    (changes : Event (Behavior α)) : Behavior α :=
  fun t =>
    ((past changes t).foldl (fun _ next => next) initial) t
```

These are mathematical definitions, not an instruction to enumerate real numbers at runtime. The use of `noncomputable` is appropriate at this layer.

For an update at \(\tau\), the old phase supplies the value at \(\tau\); the new phase supplies subsequent values until another switch. Multiple updates at \(\tau\) are ordered, and the final one determines the subsequent phase.

In particular:

\[
\mathsf{snapshot}\bigl(e,\mathsf{stepper}(a_0,e)\bigr)
\]

observes the **pre-update** state at each occurrence time. An implementation that silently uses `≤` instead of `<` implements a different specification.

### 2.4 What “Felix-style” should mean here

The useful part of Felix is not merely using Agda instead of Haskell. Its organization separates raw operations, equivalence and laws, and structure-preserving interpretations. Its homomorphism records make preservation obligations explicit; its equivalence machinery can pull an equivalence relation back through an interpretation. [GitHub](https://raw.githubusercontent.com/conal/felix/master/src/Felix/Homomorphism.agda)

I would use the same organization:

\[
\text{programs}
\overset{\llbracket-\rrbracket}{\longrightarrow}
\text{semantic functions}.
\]

Take products and the semantic types above as objects. FRP operations become typed morphisms, for example:

\[
\begin{aligned}
\mathsf{pureB}&:A\to BA,\\
\mathsf{apB}&:B(A\to C)\times BA\to BC,\\
\mathsf{merge}&:EA\times EA\to EA,\\
\mathsf{snapshot}&:EA\times BC\to E(A\times C),\\
\mathsf{switcher}&:BA\times E(BA)\to BA.
\end{aligned}
\]

The attached Lean file defines a `Raw H` record containing these operations and the Cartesian operations, followed by a `Homomorphism H r` record. Its obligations include:

\[
\begin{aligned}
\llbracket\mathsf{id}\rrbracket&=\mathsf{id},\\
\llbracket g\circ f\rrbracket
  &=\llbracket g\rrbracket\circ\llbracket f\rrbracket,\\
\llbracket\langle f,g\rangle\rrbracket(x)
  &=(\llbracket f\rrbracket(x),\llbracket g\rrbracket(x)),\\
\llbracket\mathsf{switcher}_{I}\rrbracket
  &=\mathsf{switcher}_{S},
\end{aligned}
\]

and analogous equations for the other primitives.

Using semantic types as object indices makes this presentation particularly small. A representation with different storage types adds comparison maps or realization relations. **An event carrying a behavior handle must relate that handle to an entire semantic behavior, not merely to its current cached value.**

Define implementation equivalence by

\[
p\approx q
\quad:\!\iff\quad
\llbracket p\rrbracket=\llbracket q\rrbracket.
\]

Then the usual transport of laws is legitimate. Injectivity of the interpretation is unnecessary: two different graphs may mean the same thing. What would be unjustified is concluding that their graph representations are structurally equal.

This matches the podcast’s methodological point about making homomorphism-based correctness obligations available to a proof checker rather than leaving them as external reasoning. [Haskell Foundation](https://haskell.foundation/podcast/62/)

### 2.5 Additional constraints belong at the right layer

The sparse-event condition is not the only obligation missing from ordinary signatures. I would separate the following rather than crowd all of them into `Behavior`.

| Layer | Explicit requirement |
|---|---|
| **Event denotation** | Finite batches; finite relevant past; specified order for simultaneity. |
| **Online transformations** | Causality: equal input histories through \(t\) imply equal output histories through \(t\). |
| **Analytic primitives** | Appropriate mathematical hypotheses: for example, local integrability for integration, and a suitable finite-crossing condition for an event detector. |
| **Feedback** | Initialized, well-founded dependence—not unrestricted fixed points. |
| **Executable primitives** | A terminating evaluator and a correctness or approximation certificate. |
| **Source protocol** | Ordered, consistent information; trustworthy progress certificates; a stated liveness assumption. |

For ordinary behavior inputs and outputs, causality is straightforward in Lean:

```lean
def AgreeThrough {α : Type}
    (t : ℝ) (x y : Behavior α) : Prop :=
  ∀ s, s ≤ t → x s = y s

def Causal {α β : Type}
    (f : Behavior α → Behavior β) : Prop :=
  ∀ t x y, AgreeThrough t x y →
    AgreeThrough t (f x) (f y)
```

For compound and higher-order signal types, extend the observation relation recursively.

Some consequences are worth emphasizing.

**Time transformation remains mathematically unrestricted.** Its meaning is \(b(u(t))\). For an arbitrary unknown live input, \(u(t)\le t\) is a sufficient causality condition. A monotone \(u\) helps incremental execution; backward-looking access may still require retained history. Known pure time functions need not have the same restrictions.

**Integration is not an operation on arbitrary total functions with no hypotheses.** For real-valued behaviors, a clean contract is

\[
b\ \text{locally integrable}
\quad\Longrightarrow\quad
\mathsf{integral}_{t_0,c}(b)(t)
=
c+\int_{t_0}^{t}b(s)\,ds.
\]

**`predicate : Behavior Bool → Event Unit` is underspecified.** “Emit whenever true” need not have sparse support. “Emit at transitions” also needs an exact transition definition and an admissibility condition. A verified implementation must not pretend to detect arbitrary real-function crossings effectively.

**Feedback needs more than an informal appeal to strict causality.** Over dense time, dependencies can retreat through infinitely many instants in a bounded interval. A positive delay together with initialized history is one usable discipline; an explicit well-founded dependency argument is more general. Felix itself makes a relevant distinction: its raw trace operation takes a separate `WF` witness. [GitHub](https://raw.githubusercontent.com/conal/felix/master/src/Felix/Raw.agda)

### 2.6 Lean’s treatment of infinity is not an obstacle here

None of these semantic definitions requires a primitively coinductive datatype. A behavior is a function on an infinite domain. An event is another such function with a support property.

Likewise, an infinite execution can be represented by a function \(\mathbb N\to\mathsf{State}\) satisfying a step relation. Mathlib already represents ordinary infinite streams as `ℕ → α` and provides corecursive constructions over that representation. [Lean Community](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Stream/Defs.html)

Agda may offer a preferred working style for some developments, but this specification does not require switching languages because of infinite data.

## 3. A proof-oriented push-pull implementation

I would start with a **pure Lean transition system**, with a thin external driver. The substantial change from the historical implementation is:

> A suspended dependency is explicit machine state, not an implicitly suspended evaluation of an `unsafePerformIO` thunk.

### 3.1 Choose an executable fragment without changing the target meaning

The denotation should remain real-time. That does not require pretending that arbitrary real functions or exact comparisons of arbitrary represented reals are executable.

A useful initial implementation could use:

- rational event timestamps, embedded into \(\mathbb R\);
- a typed language of pure phase expressions;
- exact rational-polynomial phases as an initial numerical fragment;
- additional primitives only with evaluator correctness certificates.

For a polynomial phase \(p\), the key bridge is

\[
\operatorname{cast}(\mathsf{eval}_{\mathbb Q}(p,q))
=
\llbracket p\rrbracket_{\mathbb R}(\operatorname{cast}q).
\]

This is still continuous-time semantics. Sampling at representable instants does not redefine a behavior as a discrete-time sequence.

For approximate numerical primitives, replace equality with a specified error relation. Silently replacing \(\mathbb R\) by floating-point values would not establish the same homomorphism theorem.

### 3.2 Retain reactive normal form

Use a phase representation \(P A\) with an interpretation

\[
\mathsf{phaseMeaning}:P A\to(\mathbb R\to A).
\]

A mathematical reactive normal form is then:

```lean
structure RNF (Phase : Type → Type) (α : Type) where
  initial : Phase α
  changes : Event (Phase α)
```

Its meaning is exactly:

\[
\llbracket r\rrbracket
=
\mathsf{switcher}
\left(
  \mathsf{phaseMeaning}(r.\mathsf{initial}),
  \mathsf{mapE}\;\mathsf{phaseMeaning}\;(r.\mathsf{changes})
\right).
\]

This retains the separation between discrete phase changes and time-dependent evaluation that motivates the original normal form. The new work is the explicit realization and verification of that representation. [Conal](https://conal.net/papers/push-pull-frp/push-pull-frp.pdf)

For applicative combination, merge the phase boundaries and construct the pointwise combination of the current phases. Process simultaneous dependency changes as a complete batch before installing the resulting post-boundary phase.

Internal phase changes may be coalesced when they have the same behavior denotation. **User-visible event occurrences may not be discarded on that basis.**

Dynamic switching requires special care. Selecting a behavior at \(\tau\) does not mean restarting that behavior’s history at \(\tau\). The selected branch needs a certified residual state appropriate just after \(\tau\), including any of its own changes at \(\tau\). Obtaining that state may require maintaining it, retaining history, or supplying an initialization procedure. That choice must appear in the representation invariant and resource argument.

### 3.3 Replace blocked temporal information with explicit frontiers

Each source publishes timestamped batches and a **frontier** \(w\), meaning:

\[
\text{all occurrences with timestamp }s<w\text{ have been delivered}.
\]

A frontier is knowledge of absence as well as presence. It must advance even for a source that happens to be silent when another dependency needs that knowledge.

The relevant distinctions are:

\[
\begin{array}{ll}
\text{unknown future} &\ne \text{known absence},\\
\text{not yet delivered} &\ne \text{never occurs}.
\end{array}
\]

A small semantic model of this protocol is already in the Lean draft:

```lean
structure Prefix (α : Type) where
  frontier : ℝ
  data : Event α

def Prefix.Sound {α : Type}
    (p : Prefix α) (truth : Event α) : Prop :=
  ∀ t, t < p.frontier → p.data.at t = truth.at t
```

The actual runtime stores finite queues and bounds, not an `Event` function. `Prefix` specifies what those queues and bounds mean.

For merge, an occurrence at \(\tau\) can be committed as part of a **complete batch** once the relevant input frontiers are strictly greater than \(\tau\). A frontier equal to \(\tau\) does not rule out an additional simultaneous occurrence.

The strict switch convention gives a useful distinction: determining a switched behavior’s value at \(t\) requires its changes strictly before \(t\), whereas emitting the complete event batch at \(t\) requires closing that timestamp.

Frontiers need not cause global polling. Requests can ask only for the horizon currently needed; updates can be coalesced, and a source can register a deadline or notification. Nevertheless, progress information cannot be eliminated semantically:

> With an occurrence from A at \(10\), but no information about B before \(10\), a correct merger cannot know whether B still has an occurrence at \(9\).

That is an information limitation, not an implementation deficiency.

### 3.4 The scheduler: push changes, pull evaluations

Use a finite graph of typed nodes, explicit subscriptions, memoized phase/state information, and a work queue.

**Push.** An input batch or relevant frontier advance updates source knowledge and enables dependent nodes. A node is processed when the information needed for its next step is available. Event outputs follow semantic timestamp and batch order, never callback arrival order.

**Pull.** A sample request evaluates the current pure phase at the requested time. Constants can be reused across samples; time-dependent phases are evaluated only for actual demands. Sharing is keyed by node, phase/version, and sample time as appropriate.

**Suspend.** A blocked computation records which additional facts would enable it and yields to the scheduler. Checking readiness and registering the wait must be atomic with respect to incoming notifications, or accompanied by an equivalent no-lost-wakeup protocol.

**Cancel.** Removing a demand releases subscriptions or references. It does not throw an exception into a computation that another consumer may be evaluating. Shared immutable phase expressions remain valid; resumable work has explicitly owned continuation state.

This preserves “push is blocked pull” at the level of demand dependencies, without requiring a runtime thread for every blocked pure computation.

An initial acyclic graph makes the first proof much simpler. Feedback can subsequently be admitted through the initialized well-founded discipline described above.

### 3.5 Address the difficult nested-event case explicitly

The 2009 event API included a monadic flattening of event-valued events, with inner occurrences delayed as necessary to respect their outer occurrence time. Its documentation also specifies an event `pure` occurring at negative infinity. These are additional choices, not consequences of the 2015 sparse behavior-of-lists formulation. [Hackage](https://hackage-content.haskell.org/package/reactive-0.11.5/docs/FRP-Reactive-Internal-Reactive.html)

An explicit scheduler can implement a precisely specified `mergeAll` operation: maintain active inner sources and their frontiers, and retime an inner occurrence at \(\sigma\), introduced at \(\tau\), to

\[
\max(\tau,\sigma).
\]

Before an output horizon \(q\), only outer occurrences at or before \(q\) can contribute. Past-finiteness therefore supplies a finite set of relevant inner streams for each finite horizon. The proof must also account for their progress and the ordering of ties.

However, **do not automatically call this a lawful `Monad`.**

Here is an additional algebraic check, separate from the historical runtime diagnosis. Consider the natural candidate “retime with `max`, then stably merge chronologically,” preserving outer order for final ties:

```text
e    = [(0,a), (1,b)]
f(a) = [(3,x)]
f(b) = [(2,y)]
g(x) = [(4,X)]
g(y) = [(4,Y)]
```

Then:

```text
(e >>= f) >>= g       = [(4,Y), (4,X)]
e >>= (\a -> f a >>= g) = [(4,X), (4,Y)]
```

On the left, the intermediate chronological ordering puts `y` before `x`. On the right, the final tie preserves the original outer ordering. Every event is finite, and every continuation produces occurrences after its parent. Causality alone does not repair the discrepancy.

I checked this finite-model counterexample with the attached ordered_event_bind_counterexample.py[executable regression example](sandbox:/mnt/data/ordered_event_bind_counterexample.py). **It is not a reproduction of Reactive’s reported runtime bugs.** It demonstrates why an ordered-batch replacement must prove its proposed monad laws rather than inherit the class name.

Keeping `mergeAll` as an explicitly specified operation is legitimate. Changing simultaneous batches to multisets is another design, but changes the semantics and requires an explicit conflict rule for switching.

### 3.6 What must be proved

The central implementation invariant should quantify over possible completions of the input knowledge:

\[
\forall x\in\mathsf{Completions}(C.\mathsf{inputs}),\qquad
C.\mathsf{observations}
\sqsubseteq
\mathsf{observe}(\llbracket p\rrbracket(x)).
\]

In words: every observation already exposed by configuration \(C\) must be correct for **every** complete input consistent with what the machine has learned.

The main proof obligations are:

| Obligation | Required result |
|---|---|
| **Semantic closure** | Every event constructor preserves finite batches and finite relevant support; every restricted primitive preserves its admissibility conditions. |
| **Compilation correctness** | Normalization and optimization preserve the denotation of each admissible program. |
| **Transition soundness** | Every machine step preserves input-knowledge, node-state, queue-order, subscription, and phase-validity invariants. |
| **Observation correctness** | Returned samples equal—or satisfy the specified approximation relation to—the semantic behavior; completed output event prefixes have exactly the specified occurrences and order. |
| **Schedule independence** | Different legal processing orders cannot change observable denotation. In particular, they cannot choose different simultaneous-event orders. |
| **Productivity** | Under fair scheduling, source progress, finite work per bounded horizon, and terminating primitive evaluation, every enabled finite observation is eventually produced. |
| **Resource and cost properties** | Unreachable subscriptions can be reclaimed; retained history is justified; stated recomputation and memory bounds hold for the selected fragment. |

The productivity theorem is indispensable. A machine that waits forever can avoid producing an incorrect answer; soundness alone does not make it an FRP implementation.

The space theorem also needs honest hypotheses. A consumer allowed to request arbitrarily old samples, or a newly selected branch that needs arbitrary discarded history, prevents an unconditional bounded-memory result. Monotone consumer cursors and explicit residual-state contracts make useful bounds possible.

Likewise, I would replace universal “minimal computation” claims with provable structural properties: no phase evaluation without a demand, no waking unrelated dependencies, and bounded recomputation per stabilized batch or sample/version. Semantic equality of arbitrary phases is not an available general optimization oracle.

Finally, a mathematical transition-system proof does not by itself verify physical clocks, input adapters, generated machine code, or the external driver. Those form a stated trust boundary unless separately refined and verified. Latency needs its own environmental and scheduling bounds; it is not a consequence of denotational equality.

## Conclusion

The appropriate repair is not to abandon continuous-time denotation, nor simply to reimplement `unamb` in another language.

Keep the semantic core:

\[
\boxed{
BA=\mathbb R\to A,\qquad
EA=\text{past-finite, ordered-list-valued behaviors}
}
\]

and use Felix-style, machine-checkable preservation obligations for the operations. Then give the runtime its own explicit semantics for **knowledge, frontiers, suspension, ownership, and progress**.

That architecture removes dependence on the particular cancellation/restart machinery implicated in the historical failures. Its correctness would still require the compiler, transition, observation, and productivity proofs above—but those obligations would finally be visible, separated, and attached to the layer responsible for satisfying them.
````

Prompt 2:
````md
It is not obvious to me that your interpretation of "-- discretely non-empty" is correct. And I know of just the method to prove it to me: https://github.com/conal/talk-2015-more-elegant-frp and especially https://github.com/conal/talk-2015-essence-and-origins-of-frp (that immediately preceded it) contain the "less elegant" specification of FRP. As these are both specification of FRP, there should be a proof that both describe the same thing.
Let's formalize the "less elegant" specification in Lean and give those proofs.
Potential difficulties:
```haskell
μ :: Event a -> [(T, a)] -- non-decreasing times
```
Here we have a potentially infinite list as well as a constraint in a comment that should be expressed in code.
````

Response 2:
````md
Your objection is correct. **My earlier finite-past condition does not follow from “non-decreasing times,” and I should not have identified it with “discretely non-empty” without a correspondence theorem.**

There are two different results to establish:

\[
\boxed{
\text{sorted, possibly infinite lists}
\;\cong\;
\text{time-indexed batches with finite predecessors per occurrence}
}
\tag{1}
\]

and, after adding a stronger condition to **both** sides,

\[
\boxed{
\text{sorted lists with finite histories}
\;\cong\;
\text{finite-list-valued behaviors with finite past support}.
}
\tag{2}
\]

The first theorem answers the representation question without silently excluding infinite simultaneous batches or Zeno sequences. The second recovers my earlier representation, but as a **restriction justified by additional requirements on the operations**, not as a direct reading of the comment.

I have written a FRPEquivalence.lean[Lean development](sandbox:/mnt/data/frp_equivalence/FRPEquivalence.lean), with README.md[explanatory notes](sandbox:/mnt/data/frp_equivalence/README.md), also available frp_equivalence.zip[together as a ZIP](sandbox:/mnt/data/frp_equivalence.zip). **The Lean file is an untypechecked proof-script candidate, not a kernel-certified development:** no Lean toolchain was available, and attempts to obtain one failed. It contains proof bodies for the representation equivalence and several operation-preservation results, rather than assuming the equivalence or inserting `sorry`; elaboration fixes may still be necessary. Below I give the mathematical constructions and proofs independently of that limitation.

## 1. What the source actually specifies

The older presentation gives events a meaning in timestamped lists and explicitly requires non-decreasing timestamps. The newer presentation repeats that specification before eventually introducing the behavior-of-lists representation. Neither comment explicitly states my earlier finite-past condition. [raw.githubusercontent.com](https://raw.githubusercontent.com/conal/talk-2015-essence-and-origins-of-frp/master/essence-and-origins-of-frp.lhs)

There is also an important logical distinction:

```haskell
meaning :: Event a -> [(T,a)]
```

does not assert that **every** non-decreasing list is the meaning of an event. There might be further restrictions on the image of `meaning`. We should therefore start by formalizing the largest total mathematical carrier described by the explicit type and order constraint, and then name any additional restrictions.

The repository does explicitly advertise equivalence with the original denotation. That motivates proving correspondence, but it does not itself settle the omitted event-support conditions. [GitHub](https://github.com/conal/talk-2015-more-elegant-frp)

One more correction to my previous translation: **both occurrences of Haskell list notation matter**. The outer list in `[(T,a)]` can be infinite, but so can the list in `Behavior [a]`. Replacing the latter by Lean’s finite `List` is already a substantive restriction.

## 2. Formalizing the older carrier without losing infinity

### A possibly infinite list

We do not need a primitively coinductive datatype for this specification. A finite-or-infinite list is a family of values indexed by an initial segment of \(\mathbb N\).

```lean
import Mathlib

structure CoList (A : Type) where
  live : ℕ → Prop
  initial : ∀ {i j : ℕ}, i ≤ j → live j → live i
  value : {i : ℕ // live i} → A

abbrev CoList.Pos {A : Type} (s : CoList A) :=
  {i : ℕ // s.live i}
```

The possible position sets are exactly

\[
\varnothing,\quad
\{0\},\quad
\{0,1\},\quad\ldots,\quad
\mathbb N.
\]

The file includes `CoList.finite_or_infinite`, stating this characterization. In particular, this is not a bounded approximation to an infinite list.

Mathlib already provides a closely related type, `Stream'.Seq`, represented by a function \(\mathbb N\to\mathsf{Option}\,A\) whose `none` entries form a suffix, together with corecursion and extensionality principles. I use the explicit position-based presentation because counting predecessors is central to the proof. [Lean Community](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Seq/Defs.html)

**Scope:** this represents total finite or infinite list spines with total elements. It does not yet represent Haskell bottom, partial spines, or partially defined elements. That distinction becomes important when discussing `before` below.

### Non-decreasing timestamps as a field

Now the older event carrier is:

```lean
structure OldEvent (T A : Type) [LinearOrder T] where
  seq : CoList (T × A)
  ordered : Monotone (fun i : seq.Pos => (seq.value i).1)
```

Thus the comment becomes a proposition carried by every inhabitant.

For the FRP specification, instantiate \(T=\mathbb R\). The representation theorem itself needs only a linear order.

Behaviors remain:

```lean
abbrev Behavior (T A : Type) := T → A
```

No finiteness, non-Zeno condition, or fixed initial time has been hidden in `OldEvent`.

### Two inhabitants that my earlier representation excluded

An infinite simultaneous batch is allowed:

\[
e_0=[(0,0),(0,1),(0,2),\ldots].
\]

So is the strictly increasing sequence

\[
e_Z=
\left[
  \left(1-\frac1{n+2},n\right)
  \;\middle|\;
  n\in\mathbb N
\right].
\]

Every occurrence of \(e_Z\) has a finite list index, but infinitely many occurrences precede time \(1\).

Both satisfy the explicit ordering constraint. The Lean draft contains these examples and proof scripts that neither has finite history at every real time.

Consequently, a theorem equating this unrestricted `OldEvent` with my previous finite-past type would be **false**.

## 3. The exact condition on the newer representation

Start with batches that are themselves possibly infinite:

```lean
abbrev Batch (T A : Type) := T → CoList A
```

For a batch function \(B\), define its occurrence positions by

\[
O_B
=
\left\{
(t,k)
\;\middle|\;
k\text{ is a live position of }B(t)
\right\}.
\]

The value at \((t,k)\) is the \(k\)-th element of \(B(t)\). Order occurrences lexicographically:

\[
(t,k)<(u,j)
\quad\Longleftrightarrow\quad
t<u
\;\lor\;
(t=u\land k<j).
\]

This preserves both chronological order and the order of simultaneous occurrences. Multiplicity is preserved as well.

The corresponding Lean definitions are:

```lean
namespace Batch

abbrev Occ {T A : Type} [LinearOrder T] (b : Batch T A) :=
  {p : T ×ₗ ℕ // (b (ofLex p).1).live (ofLex p).2}

end Batch

def FinitePred (X : Type) [LinearOrder X] : Prop :=
  ∀ x : X, (Set.Iio x).Finite

def Batch.Admissible {T A : Type} [LinearOrder T]
    (b : Batch T A) : Prop :=
  FinitePred b.Occ
```

Here `×ₗ` equips the product with lexicographic order.

The crucial condition is:

> **Every actual occurrence has finitely many strict predecessors.**

Equivalently, at every time whose batch is nonempty, only finitely many occurrences have strictly earlier timestamps. The predecessors within the same batch are automatically finite because a batch position is a natural number.

This is weaker than requiring finite history at **every** time. In particular, it says nothing about history at an unoccupied limit time such as \(1\) in the Zeno example.

Define:

```lean
def NewEvent (T A : Type) [LinearOrder T] :=
  {b : Batch T A // b.Admissible}
```

Then the exact representation theorem is

```lean
def eventEquiv : OldEvent T A ≃ NewEvent T A
```

### Why ordinary topological discreteness is not enough

Consider batches containing one occurrence at each time

\[
\left\{1-\frac1{n+2}:n\in\mathbb N\right\}\cup\{2\}.
\]

Every point of this support is isolated in the subspace-topological sense. Nevertheless, the occurrence at \(2\) has infinitely many predecessors.

Its chronological order type is \(\omega+1\): infinitely many occurrences, followed by another occurrence. An ordinary finite-or-\(\omega\)-long list has no position “after all natural-number positions.”

Similarly, support at every integer is locally finite, but has no first occurrence and cannot be enumerated increasingly by an ordinary list.

Thus “discrete support” by itself does not establish the requested correspondence. We need a precise order-theoretic condition. **Finite predecessors is the necessary-and-sufficient condition for the raw carrier theorem; this does not, by itself, establish what Elliott intended by the informal phrase.**

## 4. Proof of the representation equivalence

Let

\[
G:\mathsf{OldEvent}\,T\,A\to\mathsf{NewEvent}\,T\,A
\]

group occurrences by time, and let

\[
F:\mathsf{NewEvent}\,T\,A\to\mathsf{OldEvent}\,T\,A
\]

flatten them chronologically.

The substance is proving that flattening exists and that neither construction changes ordering or multiplicity.

### 4.1 Grouping is well-defined

For an old event \(e\) and time \(t\), take the ordered subset

\[
I_{e,t}
=
\{n\in\operatorname{Pos}(e):\operatorname{time}_e(n)=t\}.
\]

Read its values in increasing original index order. This produces \(G(e)(t)\).

Each index in this subset has finitely many earlier indices, so the subset has a canonical finite-or-infinite list enumeration. A batch may be infinite; we do not force it into a finite `List`.

Moreover, grouping preserves the total order of occurrences. If two original occurrences have different timestamps, their order is determined by those timestamps. If their timestamps agree, their order is retained inside the batch.

An original occurrence at index \(n\) therefore has exactly \(n\) predecessors after grouping. Hence \(G(e)\) satisfies `Admissible`.

### 4.2 Flattening exists: enumerate by predecessor count

For an admissible \(B\), define

\[
r_B(p)
=
\left|\{q\in O_B:q<p\}\right|.
\]

This is a natural number because of admissibility.

**Strict increase.** If \(p<q\), then

\[
\{x:x<p\}\subsetneq\{x:x<q\},
\]

because \(p\) belongs to the second set but not the first. Both are finite, so

\[
r_B(p)<r_B(q).
\]

Thus rank is injective and order-preserving.

**No gaps.** Suppose \(r_B(q)>0\). The finite nonempty predecessor set of \(q\) has a greatest element \(p\). By maximality,

\[
\{x:x<q\}=\{x:x<p\}\cup\{p\},
\]

so

\[
r_B(q)=r_B(p)+1.
\]

Induction supplies an occurrence of every rank below \(r_B(q)\). Therefore the rank image is an initial segment of \(\mathbb N\).

Consequently,

\[
r_B:O_B\cong
\{n\in\mathbb N:\exists p,\ r_B(p)=n\}
\]

is an order isomorphism onto a valid co-list position set. Define \(F(B)\) at rank \(n\) using the timestamp and value of the unique occurrence of that rank.

Its timestamps are non-decreasing because lexicographic occurrence order respects timestamp order.

The draft develops this argument in `Numbering.rank_strictMono`, `Numbering.rank_initial`, and `Numbering.indexIso`.

### 4.3 First inverse law: flatten after grouping

Take occurrence \(n\) of \(e\). After grouping, the same occurrence still has exactly \(n\) predecessors. Flattening therefore puts it back at index \(n\), with unchanged timestamp and value.

Every live index is restored, and no other index is introduced. Hence

\[
F(G(e))=e.
\]

### 4.4 Second inverse law: group after flattening

Take occurrence \((t,k)\) of \(B\). Flattening preserves its timestamp, value, and order relative to every other occurrence.

Regrouping at \(t\) therefore recovers exactly the occurrences originally in \(B(t)\), in their original local-index order. In particular, \((t,k)\) returns to local index \(k\).

Thus

\[
G(F(B))(t)=B(t)
\]

for every \(t\), and consequently

\[
G(F(B))=B.
\]

These are literal extensional equalities of the list representations, not equality after forgetting duplicate values or simultaneous ordering.

In the Lean draft, `Realization` packages the timestamp- and value-preserving order isomorphism. The final inverse proofs are:

```lean
theorem toOld_toNew (e : OldEvent T A) :
    toOld (toNew e) = e := by
  exact Realization.old_unique
    (Realization.flatten e.group e.group_admissible)
    e.groupRealization

theorem toNew_toOld (b : NewEvent T A) :
    toNew (toOld b) = b := by
  apply Subtype.ext
  exact Realization.batch_unique
    (toOld b).groupRealization
    (Realization.flatten b.val b.property)

def eventEquiv : OldEvent T A ≃ NewEvent T A where
  toFun := toNew
  invFun := toOld
  left_inv := toOld_toNew
  right_inv := toNew_toOld
```

The auxiliary `Realization` results are proved earlier in the file; they are not assumed equivalence axioms.

## 5. Why carrier equivalence is not yet equivalence of the FRP operations

A bijection between the underlying types is necessary, but an equivalence of specifications must also preserve the operations.

This exposes a genuine problem with taking the old order comment as the **only** constraint.

### A counterexample for merge

Let \(e_Z\) be the Zeno sequence above, and let \(s\) contain one occurrence at time \(2\).

A standard chronological list merge repeatedly chooses the next occurrence of \(e_Z\), because every one has timestamp below \(1\). The occurrence at \(2\) never appears at any finite output index.

Thus, writing \(G\) for grouping,

\[
G(\mathsf{merge}(e_Z,s))(2)=[]
\]

whereas

\[
G(e_Z)(2)\mathbin{+\!\!+}G(s)(2)
=
[]\mathbin{+\!\!+}[a]
=
[a].
\]

But the newer derived event operation is pointwise list append. [GitHub](https://github.com/conal/talk-2015-more-elegant-frp/blob/lambdajam-2015/more-elegant-frp.lhs)

Therefore:

\[
G(\mathsf{merge}(e_1,e_2))
=
G(e_1)\mathbin{\oplus}G(e_2)
\]

**cannot hold unconditionally on all non-decreasing co-lists.**

This is not merely a defect in one merge algorithm. There is no ordinary sorted list containing all the Zeno occurrences followed by the occurrence at \(2\).

### The general necessity argument

Suppose a sorted output contains an occurrence at time \(t\), at output index \(N\), and contains all occurrences of \(e\) without loss or timestamp changes.

Every occurrence of \(e\) before \(t\) must occupy an output position below \(N\). Therefore there can be only finitely many such occurrences.

So closure under **lossless merge with an arbitrary singleton at time \(t\)** forces

\[
\forall t,\quad
\{n\in\operatorname{Pos}(e):
  \operatorname{time}_e(n)<t\}
\text{ finite}.
\tag{FH}
\]

The draft contains this argument as `OldEvent.finite_before_of_following_occurrence`. It does not assume any particular merge implementation.

This is where the stronger finite-history condition can be derived: **from an operational equation plus losslessness and closure, not from timestamp monotonicity alone.**

## 6. Restricting both sides: the finite-history equivalence

Define finite history separately:

```lean
def OldEvent.FiniteHistory
    {T A : Type} [LinearOrder T] (e : OldEvent T A) : Prop :=
  ∀ t : T, {i : e.Pos | e.time i < t}.Finite

def Batch.FiniteHistory
    {T A : Type} [LinearOrder T] (b : Batch T A) : Prop :=
  ∀ t : T, {p : b.Occ | p.time < t}.Finite
```

The grouping order isomorphism preserves timestamps. Restricting it to occurrences before \(t\) gives a bijection between the two histories. Therefore

\[
\mathsf{FiniteHistory}(e)
\quad\Longleftrightarrow\quad
\mathsf{FiniteHistory}(G(e)).
\]

The original equivalence consequently restricts to an equivalence of the finite-history subtypes.

For real time, finite history also implies admissibility and finite individual batches. To see the latter, fix \(t\) and choose \(u>t\): every occurrence in \(B(t)\) belongs to the finite history before \(u\).

The draft’s direct restricted theorem is:

```lean
def totalEventEquiv [NoMaxOrder T] :
    {e : OldEvent T A // e.FiniteHistory} ≃
      {b : Batch T A // b.FiniteHistory}
```

`NoMaxOrder` is satisfied by \(\mathbb R\).

Now convert each finite co-list batch to an ordinary Lean `List`. With finite batches, these two conditions are equivalent:

\[
\forall t,\quad
\text{finitely many occurrences before }t,
\]

and

\[
\forall t,\quad
\{s:s<t\land B(s)\ne[]\}\text{ finite}.
\]

One direction projects the finite occurrence set onto timestamps. The other expresses the occurrence history as a finite union of finite batches.

This gives precisely the corrected corollary:

\[
\boxed{
\begin{aligned}
&\{e:\mathsf{OldEvent}\,\mathbb R\,A
       \mid \mathsf{FiniteHistory}(e)\}\\
&\qquad\cong
\left\{
B:\mathbb R\to\mathsf{List}\,A
\;\middle|\;
\forall t,\ 
\{s:s<t\land B(s)\ne[]\}\text{ finite}
\right\}.
\end{aligned}
}
\]

**That establishes the relationship to my earlier representation.** The final conversion to native finite `List` is explained mathematically here; it is not mechanized in the attached file.

## 7. Preserving the operations

### Behaviors: the old equations are the standard pointwise operations

The earlier presentation specifies pointwise lifting, identity time, and composition for time transformation. [GitHub](https://raw.githubusercontent.com/conal/talk-2015-more-elegant-frp/lambdajam-2015/more-elegant-frp.lhs)

Using \(BA=T\to A\):

```lean
def pureB (a : A) : Behavior T A :=
  fun _ => a

def mapB (f : A → B) (x : Behavior T A) : Behavior T B :=
  fun t => f (x t)

def apB (f : Behavior T (A → B)) (x : Behavior T A) :
    Behavior T B :=
  fun t => f t (x t)
```

The old binary lifting formula becomes

\[
\mathsf{lift2}(f,x,y)
=
\mathsf{apB}(\mathsf{mapB}(f,x),y).
\]

Its proof is definitional equality:

```lean
theorem lift2_eq_ap
    (f : A → B → C)
    (x : Behavior T A)
    (y : Behavior T B) :
    (fun t => f (x t) (y t)) =
      apB (mapB f x) y := rfl
```

Likewise, time is `id`, and time transformation is function composition. No restriction of continuous semantic time is involved.

### Events: mapping and snapshot

Timestamp-preserving mapping changes only occurrence values. Grouping therefore commutes with mapping:

\[
G(\mathsf{mapE}(f,e))(t)
=
\mathsf{CoList.map}(f,G(e)(t)).
\]

Snapshot replaces an occurrence \((t,a)\) by \((t,(a,b(t)))\), so

\[
G(\mathsf{snapshot}(e,b))(t)
=
\mathsf{CoList.map}
  \bigl(\lambda a.(a,b(t))\bigr)
  (G(e)(t)).
\]

Both follow from preservation of the same occurrence order isomorphism, with altered labels. Their proof scripts are `OldEvent.group_map` and `OldEvent.group_snapshot`.

The empty event and singleton event correspond to the everywhere-empty batch function and a singleton batch at the specified timestamp, respectively.

### Merge on the finite-history fragment

Choose **stable left-first ordering** for simultaneous occurrences. On finite histories, merge the disjoint occurrence sets ordered by

\[
(\text{timestamp},\text{input side},\text{within-input index}).
\]

Every occurrence has finitely many predecessors: both inputs have finite relevant histories and finite simultaneous batches. The rank construction therefore enumerates the merged occurrences.

At a given timestamp, all left occurrences precede all right occurrences, giving

\[
G(\mathsf{merge}(e_1,e_2))(t)
=
G(e_1)(t)\mathbin{+\!\!+}G(e_2)(t).
\]

This proves the merge homomorphism mathematically on the restricted carrier. A stable-merge construction and its full Lean proof are **not included** in the current artifact.

The tie policy is explicit because ordered lists retain simultaneous ordering. It cannot be supplied by an unspecified scheduler.

### Switching: preserve the strictly-before boundary

The older source specifies switching using the last replacement strictly before the observation time, and explicitly distinguishes `<` from `≤`. [GitHub](https://raw.githubusercontent.com/conal/talk-2015-essence-and-origins-of-frp/master/essence-and-origins-of-frp.lhs)

For an initial behavior \(b_0\), define

\[
\mathsf{switcher}_{\mathrm{old}}(b_0,e)(t)
=
\begin{cases}
b_0(t),&\text{if no occurrence precedes }t,\\
b(t),&\text{if }b\text{ is carried by the last such occurrence}.
\end{cases}
\]

Define the batch-side operation identically, using lexicographic occurrence order.

Grouping restricts to an order isomorphism between the strictly-before histories. It therefore preserves emptiness and the greatest occurrence when one exists, along with that occurrence’s behavior value. Evaluating the same behavior at \(t\) gives

\[
\mathsf{switcher}_{\mathrm{old}}(b_0,e)
=
\mathsf{switcher}_{\mathrm{new}}(b_0,G(e)).
\]

The draft contains `Realization.before_eq`, an order-invariance theorem for selecting the last occurrence, and `Realization.switcher_eq`.

Why the finiteness hypothesis? An initial segment of natural-number positions is empty or has a greatest element **exactly when it is finite**. The draft states this as `OldEvent.finite_before_iff_empty_or_last`.

Thus finite history is also the exact condition needed to make this literal last-based selector total at every observation time. Adding special limit semantics for some infinite histories would be a different extension, not the stated `last` operation.

## 8. Two remaining boundaries of the result

### Mathematical lists versus literal lazy Haskell evaluation

The source writes `before` as a list comprehension filtering occurrences whose timestamps are below \(t\). [GitHub](https://raw.githubusercontent.com/conal/talk-2015-essence-and-origins-of-frp/master/essence-and-origins-of-frp.lhs)

Interpreted as a mathematical ordered subset, that is what we formalized. Interpreted literally as lazy Haskell `filter` on an infinite list, it has an additional problem: after the final matching occurrence, evaluation keeps searching the infinite suffix for another match. Thus a finite mathematical history need not become a fully terminated Haskell list, and applying `last` can diverge.

The theorem here is about **total mathematical denotations**, not equivalence of those lazy computations. A domain-theoretic treatment including partial spines would require another semantic layer and continuity proofs. It should not be smuggled into this theorem.

### The presentations are not complete formal specifications of every primitive

The event slides leave event-operation meanings as an exercise, and do not provide complete mathematical definitions for all primitives such as `predicate` and `integral`. [GitHub](https://raw.githubusercontent.com/conal/talk-2015-more-elegant-frp/lambdajam-2015/more-elegant-frp.lhs)

Accordingly, the correspondence above covers the event carriers, pointwise behavior operations, timestamp-preserving event operations, and strictly-before switching. It states the tie policy needed for merge. It does not invent an unspecified event-detector meaning and then claim to have proved that this was the original specification.

## Conclusion

The proof does **not** vindicate my earlier interpretation as stated. It yields a more precise correction:

> **Non-decreasing finite-or-infinite timestamped lists correspond exactly to time-indexed possibly infinite batches in which every actual occurrence has finitely many predecessors.**

Then:

> **Requiring total last-based switching, or closure under lossless merge with arbitrary singleton events, leads to the stronger finite-history fragment. On that fragment, the representation is equivalent to finite-list-valued behaviors with finite past support.**

So the finite-past condition can be justified by a correspondence and closure argument—but it must appear as an explicit additional condition. It cannot simply be substituted for `-- discretely non-empty` at the outset.
````

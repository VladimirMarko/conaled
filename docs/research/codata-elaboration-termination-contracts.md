# Codata, termination certificates and elaboration contracts

Research on 2026-10-25 at repository baseline
`83c1fcb87f10bc2e1c13aba2a85105adc738d994`. This note proposes contracts and
mathematical test cases. Extended for [#145](https://github.com/VladimirMarko/conaled/issues/145)
at baseline `29a62c424453a6763dc2e22ec38d897d21254a4d`. It does not add checked
theorems or implement a checker.

The owner approved further research and formalization of the finite-prefix
counterexample. Immediate laziness and arbitrary codata are not required.
The architectural requirement is to avoid assumptions that would prevent
supporting them later. The termination/productivity and elaboration contracts
below are approved bounded next steps, independent of a complete lazy runtime.

The project can represent infinite objects without extending Lean's kernel.
It still needs to specify which finite observations can be computed, which
source constructions preserve that property, and which interpretations retain
it. The existing relational-square machinery can express these contracts;
there is no existing general termination/productivity checker or declarative
elaboration specification in the inspected language modules.

## Existing local foundations

[Languages/Machines.lean](../../Applications/Languages/Machines.lean) already
uses a state coalgebra: `Machine.nullable` and `Machine.next` generate observations
of a language. `Machine.unfold` builds a depth-indexed trie by finite recursion.
`Machine.lookup_unfold` relates each sufficiently deep observation to
`Machine.run`; `Machine.run_correct` proves membership correctness for every
finite word. `Machine.intersection_correct` composes machine obligations.
This is a concrete example of infinite behavior presented through all finite
observations. The individual bounded trie is not an infinite materialized tree.

[FRP/Trace.lean](../../Applications/FRP/Trace.lean) models input streams as
`Source → Nat → Message`. Its `eventual_observation` theorem requires both fair
processing of available prefixes and source progress that eventually supplies
a closing prefix. Its safety square alone does not prove either hypothesis.
[FRP/Spec.lean](../../Applications/FRP/Spec.lean) uses total mathematical
behaviors `ℝ → α` and events with finite past support; its comments explicitly
separate those from online realizability.

[Relations.lean](../../SquareKit/Relations.lean) provides preservation,
composition and relation-witness spaces. The indexed membership construction in
[Optimization/Relations.lean](../../Applications/Optimization/Relations.lean)
shows how to retain the input problem while interpreting a successful output
as membership in a set of admissible results. These are reusable foundations
for the contracts below, alongside the
[optimization specification](compositional-optimization.md). None supplies
termination evidence merely because a semantic square commutes.

## What Lean and Agda provide

The pinned Mathlib defines `Stream' α := Nat → α`, with `map`, `zip`, `iterate`
and `corec`. A coalgebra step `S → A × S` therefore gives a stream through
finite iteration. This supplies mathematical infinite streams and executable
observations when the step and initial state are executable. Arbitrary Lean
functions may be noncomputable; the function type alone is not an extraction
or resource guarantee. The representation also does not promise sharing of
successive observations. [Pinned Mathlib stream source](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Stream/Defs.lean)

Lean's `coinductive` and `coinductive_fixpoint` support `Prop`-valued predicates,
such as bisimulation, rather than native coinductive data in `Type`.
`partial_fixpoint` constructs fixed points of monotone operations on suitable
orders. Its existence/equational results do not establish termination of a
runtime implementation. In particular, a tail-recursive definition into an
inhabited type may have underspecified values on diverging inputs. Avoid using
that total mathematical value to infer successful runtime evaluation.
[Lean recursive-definition reference](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/)

The versioned reference URL was unavailable during research. The installed
v4.35.0 source confirms that the coinductive fixpoint case rejects non-predicate
results and distinguishes the partial fixpoint mechanism.
[Pinned elaborator source](https://github.com/leanprover/lean4/blob/v4.35.0/src/Lean/Elab/PreDefinition/PartialFixpoint/Main.lean)

Agda 2.8 provides coinductive records and copatterns for streams under
`--guardedness`. Its documentation demonstrates stream operations and a
bisimulation proof. Constructor syntax on a coinductive record does not itself
count as a guard, which matters for superficially similar source translations.
[Agda coinduction](https://agda.readthedocs.io/en/v2.8.0/language/coinduction.html)

Sized types expose observation depth across function boundaries, permitting
compositions that a syntactic guard check misses. Agda's language-tree example
is closely related to our language machines. However, Agda 2.8 explicitly
excludes `--sized-types` from `--safe` because checks against inconsistent uses
are missing. The semantic idea is useful; accepting an imported sized
certificate requires our own justified rules and audit of the source mode.
[Sized types](https://agda.readthedocs.io/en/v2.8.0/language/sized-types.html),
[Safe Agda](https://agda.readthedocs.io/en/v2.8.0/language/safe-agda.html)

## Capability and observation obligations for #145

This extension inspects Lean 4.35.0 at
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Mathlib at the manifest revision
above, and Agda 2.8.0 at `3d04bacca842729f9c0869b9287256321b5f450f`.
The equations and scenarios below are mathematical design analysis, not new
Lean declarations or reports of an Agda build. Existing checked examples are
identified separately. The formal Cantor counterexample remains owned by the
expressive-test workstream; this task does not select or prepare #107/#108's
independent retest.

A coalgebra `c : S → F S` supplies one step. A final coalgebra additionally
supplies a unique behavior map satisfying `out ∘ unfold = F(unfold) ∘ c`.
The latter is an existence and uniqueness property, not a scheduling theorem.
This distinction follows the coalgebras, homomorphisms and final systems in
[Rutten, *Universal coalgebra: a theory of systems*, §§2–3 and 9](https://ir.cwi.nl/pub/48/).
The table gives candidate contracts for this project, with only the structure
needed for each route. It does not prescribe one representation for all routes.

| Capability | Equations and observations | Ambient structure and outstanding obligations |
|---|---|---|
| Total streams | `out : Stream A → A × Stream A`; head/tail and every finite prefix. In Set, `A^Nat` supports pointwise equality. | Products and a final `A × -` coalgebra, or an explicit natural-number-indexed representation. Executable heads/tails need terminating element computations; finality and runtime sharing are separate. |
| Possibly finite colists | `out : Colist A → 1 + A × Colist A`; each observation returns end or a head and remainder. | Coproducts, products and the chosen final coalgebra. End is positive information. A search that never finds a match has not returned end. |
| Delayed/partial output | `now a` or `later computation`; for a producer, a step can end, emit, or remain silent. | A delay construction or explicit transition system; convergence is finite reachability of an output. Choose whether equivalence retains delay counts, ignores finite delays, or also identifies divergence. Safety under silent steps does not establish convergence. |
| State coalgebras | `obs s`, `next s`, and finite iterates; a homomorphism `h` obeys `c' ∘ h = F h ∘ c`. | For a fixed finite observation, iteration and the operations it uses suffice. Finality is unnecessary for `Machine.lookup_unfold`. Transport the step equation and observation relation; compose maps without erasing their witnesses. |
| Guarded recursion | A later modality `▷` and a guarded fixed-point equation, schematically `fix f = f (next (fix f))`. | A model validating later and guarded fixed points, with substitution/naturality laws. An unrestricted eliminator `▷A → A` would defeat the guard. Relate logical ticks to emitted observations before claiming output productivity. |
| Sized codata | Observations at size `i` may expose a tail at smaller `j`; size-preserving operations support composition. | Valid size ordering, quantification, subtyping and rules for the limit size, with their soundness. Neither erasing a size annotation nor accepting Agda's size solver proves the translated productivity claim. |
| Domain fixed points | In a pointed ω-cpo with continuous `f`, `lfp f = sup_n f^n(⊥)` and `f(lfp f) = lfp f`. | Bottom, increasing-chain suprema and continuity for this construction. A fixed point can be bottom; operational adequacy and convergence require further theorems. A different complete-order construction may require only monotonicity. |

The delay distinction follows [Capretta, *General recursion via coinductive
types*](https://lmcs.episciences.org/2265): partial elements retain possibly
infinite computation, unlike a total optional result. The guarded model is
supported by [Birkedal et al., *First steps in synthetic guarded domain
theory*, §§2–4](https://lmcs.episciences.org/1041/pdf), whose later functor lives
in a presheaf model. These are different semantic constructions; the table
does not identify a domain bottom with a guarded tick. For the continuous
least-fixed-point route, see [Abramsky and Jung, *Domain Theory*, §2.1](https://www.cs.famaf.unc.edu.ar/~mpagano/cursos/dominios/libros/abramsky-jung-domain-theory.pdf).
The needed preservation maps depend on the selected construction: preserve
bottom and chain suprema to transport its iteration, or preserve later and its
fixed-point operation for the guarded route. Neither follows merely from
preserving products.

### Worked operations and failure cases

For these worked cases, let `s : Nat → A` be a stream with executable finite
observations. Prefix length `n` means indices strictly below `n`. Assume each
invoked element operation terminates; functions in host mathematics alone do
not imply that assumption for extracted code.

- **Map:** `map f s i = f (s i)`. Producing `n` elements demands `n` input
  elements. Pointwise equivalence transports when `f` respects the chosen
  element relation. The identity and composition laws follow pointwise; their
  validity says nothing about how often an implementation recomputes `s i`.
- **Zip:** `zip h s t i = h (s i) (t i)`. Prefix demand is `(n,n)` and
  progress is required from both inputs. A scheduler serving only one input
  can preserve value safety while preventing delivery. Synchronize their
  relations using the existing product construction, rather than assuming
  that one input's progress certifies the pair.
- **Scan:** choose the seed-inclusive convention `q 0 = z` and
  `q (i+1) = step (q i) (s i)`. The first `n` outputs demand
  `max(n-1,0)` inputs. A realization stores the accumulator and current input
  state; a relation to `q i` is its invariant. A seed-exclusive scan has
  different demand and must not inherit this contract unchanged.
- **Selective filter:** take `s i = 0` and predicate `x > 0`. Every tested
  input fails, so the usual sequential filter makes infinitely many silent
  steps and produces no first output. Replacing the result by a colist does
  not give that search a finite proof of end. A special implementation may
  recognize this particular constant producer and return end; a generic
  opaque input cannot justify end from any finite all-zero prefix, since a
  later position may be positive. An all-input stream-to-stream filter
  therefore cannot promise delivery under this specification.
- **Guarded feedback:** `q 0 = z`, `q (i+1) = f (q i)` emits the seed before
  demanding feedback. Every finite prefix follows by finite iteration if `f`
  terminates. By contrast, a transition `s ↦ s+1` that always chooses silence
  has an infinite transition trace but no output. Guarded construction of
  that trace establishes progress in *steps*, not progress in *emissions*.
  Unguarded feedback `q = q` neither selects a unique stream nor supplies a
  procedure for obtaining its head.

For filtering into an infinite stream, a useful sufficient premise is
`∀ k, ∃ j ≥ k, p (s j)`, with decidable `p` and executable source observations.
It gives arbitrarily late matches, not a uniform bound independent of input.
An executable realization can use a justified terminating search, or receive
increasing matching indices with search/completeness evidence. A classical
existence proof alone is not an extracted search algorithm. With only finitely
many matches, a delayed producer can emit those matches and then remain silent;
reporting end needs separate evidence that no more matches occur. An alternative
`Stream (Option A)` returns `none` at rejected positions and is productive per
input position, but does not implement compaction. These alternatives must
remain distinct in source fidelity and optimization contracts.

Fair scheduling suffices only when the environment eventually supplies every
needed finite input prefix and each local demanded computation terminates.
This is the same separation already proved by `Delivery.Fair` and the independent
`progress` hypothesis of `Trace.eventual_observation`. No fairness premise can
create a positive value in the constant-zero example. A bounded certificate
may provide a decreasing rank between emissions, while another realization
may supply an input-dependent demand relation. Do not require a uniform
numerical bound as the definition of productivity.

### Implementation restrictions and retained evidence

The pinned [Lean fixed-point elaborator](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Elab/PreDefinition/PartialFixpoint/Main.lean#L76)
checks predicate results for `coinductive_fixpoint`, constructs an order
instance, proves monotonicity, builds a fixed-point term, and registers equation
information. For `partial_fixpoint`, it seeks a `CCPO`; its fallback constructs
a flat order from an inhabitant. It also generates a recursive execution
implementation through `addAndCompilePartialRec`. The
[pinned compilation helper](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Elab/PreDefinition/Basic.lean#L280)
marks that implementation `DefinitionSafety.partial`. Thus the logical
fixed-point equation and running recursive code have distinct roles.

Lean's ordinary `partial` definitions instead present an opaque logical
interface and do not justify their recursive equations as termination proofs.
Structural and well-founded definitions elaborate into kernel-checkable
recursion; well-founded descent evidence belongs to that construction, whereas
tactic search and source annotations are not themselves trusted evidence.
See the [recursive-definition reference](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/).
The live reference is contextual documentation; the pinned source above fixes
which implementation this inspection concerns. No claim here audits Lean's
native compiler against its kernel meaning.

Lazy execution is not absent from Lean: its pinned
[`Thunk` implementation and contract](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Init/Core.lean#L110)
use runtime primitives for caching a forced result. In contrast, Mathlib's
`Stream'.corec` is `map` over `iterate`; the definition does not carry a shared
mutable cursor between calls. A thunk, a persistent stream of thunks, and a
stateful iterator can agree extensionally while retaining different amounts of
memory. Space bounds, reclamation, concurrency behavior and avoidance of
recomputation need an execution/cost contract. Prefix equality does not prove
them. No arbitrary recursive codata implementation follows from the presence
of `Thunk`.

Agda's [pinned coinduction examples](https://github.com/agda/agda/blob/3d04bacca842729f9c0869b9287256321b5f450f/doc/user-manual/language/coinduction.lagda.rst)
show copattern stream equations and bisimulation. Explicit coinductive record
constructors cannot be pattern-matched and do not count as productivity guards;
η-equality is not generally enabled for such records. The older built-in delay
presentation and coinductive records therefore cannot be translated by
blindly renaming constructors. In the actual
[termination checker](https://github.com/agda/agda/blob/3d04bacca842729f9c0869b9287256321b5f450f/src/full/Agda/Termination/TermCheck.hs#L226),
guardedness participates in call analysis; the constructor analysis tracks
whether arguments preserve guards. The
[sized examples](https://github.com/agda/agda/blob/3d04bacca842729f9c0869b9287256321b5f450f/doc/user-manual/language/sized-types.lagda.rst)
use size-preserving language operations to admit compositions the unsized
checker cannot infer. These are source inspections, not independently proved
soundness of Agda's checker.

Agda's stored [`funTerminates :: Maybe Bool`](https://github.com/agda/agda/blob/3d04bacca842729f9c0869b9287256321b5f450f/src/full/Agda/TypeChecking/Monad/Base.hs#L2707)
is a verdict field, not a portable proof term. The
[pragma branch](https://github.com/agda/agda/blob/3d04bacca842729f9c0869b9287256321b5f450f/src/full/Agda/Termination/TermCheck.hs#L176)
sets it to true when checking is skipped by `TERMINATING` or
`NoTerminationCheck`. `NON_TERMINATING` sets it false; the
[documented source mode](https://agda.readthedocs.io/en/v2.8.0/language/termination-checking.html#pragmas-and-options)
permits runtime execution but excludes its reduction during typechecking.
[Safe Agda](https://agda.readthedocs.io/en/v2.8.0/language/safe-agda.html)
rejects those overrides, sized types, and several other unchecked features.
Safe-mode acceptance still does not turn an external verdict into a Lean proof
of the exact imported proposition.

For [#115](https://github.com/VladimirMarko/conaled/issues/115), export internal
declarations together with the signature, source options, recursion groups,
coinductive record information, sizes, conversion rules and dependency manifest.
Preserve computational state and witnesses in data-bearing types. For
[#116](https://github.com/VladimirMarko/conaled/issues/116), a superficial
Agda-to-slean translation needs supported meanings for copattern observations,
size restrictions, bisimulation and the source's reduction equations. A target
that merely types the translated names has not preserved these judgments.

Either a verified producer can construct the target certificate, or an
untrusted producer can submit it to a verified validator. In both cases the
acceptance theorem must mention the exact source declaration, target artifact,
observation relation and source mode. Retain or reconstruct descent/guard
justifications that the target kernel can check; if the exported interface
contains only a verdict, reject unsupported cases or regenerate evidence.
Hashes identify bytes and dependencies, but do not establish that acceptance
means the intended proposition. The importer and its schema remain outside
#145; the [Agda frontend investigation](agda-core-and-slean-frontends.md)
records the broader boundary.

### Bounded follow-up and architectural constraints

Recommend [#146](https://github.com/VladimirMarko/conaled/issues/146) start with
explicit finite observations of a total state transition and a separate
silent-step relation with a decreasing rank between emissions. Keep operations,
observational equivalence and progress laws in separate interfaces. Prove
composition and use it for map followed by scan, paired producers, and the
silent-loop negative case. Use `Relational.compose` and `Relational.product` for value
preservation; add explicit progress transport rather than pretending their
current preservation field proves liveness. Keep accumulator/state witnesses
in the representation, not only a proposition that some implementation exists.

The already checked reuse pattern is concrete: `Machine.Correct` separates laws
from `Machine`, `regexMachine_correct` supplies a specialization,
`intersection_correct` combines two independent instances, and `snapshotSquare`
uses the shared exact-square interface for bounded observations. FRP's
`executionSquare` separately supplies relational safety while
`eventual_observation` adds progress. These existing specializations justify
reusing the interfaces; they do not yet check the proposed stream/scan/rank
contracts. This research change adds no formal declarations.

Avoid making all semantic functions executable, all computations terminating,
all recursive values eagerly materialized, all observation results immediately
available, or all equalities host equality. Also avoid requiring every change
of setting to preserve final coalgebras, all dependent witnesses to be erased,
or every frontend to use one universal AST. Each would exclude a route in the
table without proving it unnecessary. Specify preservation only for the
operations and observations a consumer uses, with maps, composition and their
coherence obligations retained.

The exact lazy heap representation, sharing policy, runtime scheduler, general
colist implementation, size calculus, later modality, and choice of frontend
syntax can remain undecided. They become obligations when a particular route
claims those capabilities. A finite-observation certificate neither commits
the project to eager-only semantics nor promises general lazy execution.
Host/target version separation remains an investigation; this note changes no
Lean, Mathlib or ConLeche pin and introduces no alternate kernel.

## Codata under a change of setting

Streams are necessarily infinite sequences. A colist may end after finitely
many outputs; a partial or delayed producer may instead fail to deliver a
next observation. Ending, delaying and diverging require distinct observations
when the intended semantics distinguishes them. Unrestricted filtering can
fail to deliver a first element even when its input is a total infinite stream.
Changing its target to a possibly finite colist alone does not make the end of
a fruitless infinite search decidable.

A geometric inverse image preserves finite limits and, as a left adjoint,
existing colimits. It need not preserve exponentials or countable products.
Therefore a transported coalgebra for `A × -` is not automatically a final
coalgebra. In settings where streams are represented by `A^N`, the comparison
`f*(A^N) → (f*A)^(f*N)` needs a preservation theorem, not just a name for its
source and target. Slice pullback functors enjoy stronger preservation than
arbitrary geometric inverse images, so success in our fixed-slice experiments
cannot discharge this general requirement.
[Van Oosten's topos notes](https://ncatlab.org/nlab/files/vanOosten-ToposTheory.pdf),
[Hemelaer and Rogers, Proposition 3](https://link.springer.com/article/10.1007/s10485-020-09626-6)

Here is a mathematical counterexample specific to streams, not a checked local
formalization. Let `X = {0,1}^N` with the product topology and take the constant
sheaf inverse image `Δ : Set → Sh(X)`. A section of `Δ({0,1}^N)` is a locally
constant map into the set of bit sequences with discrete topology. A section
of the countable product of `Δ{0,1}` is a family of locally constant bit-valued
maps. The coordinate projections on `X` form such a family. Their assembled
map is the identity on the underlying set of `X`, which is not locally constant:
no basic open neighborhood fixes every coordinate. Thus this family is not
in the image of the stream comparison on global sections. Finite products
are preserved, but the full stream object is not. Since `ΔN` is a coproduct
of copies of the terminal object, the product is also the exponential by `ΔN`.

This suggests an early test: prove transport for every finite prefix, then
exhibit the missing condition needed to reconstruct a full transported stream.
Do not silently promote prefix preservation to preservation of finality.
A backend may instead provide a comparison into its own stream object and
prove precisely the observational properties needed by consumers.

## Separate the properties being certified

| Property | Proposed meaning |
|---|---|
| Runtime termination | For a specified input and evaluation strategy, evaluation reaches a value in finitely many steps. |
| Totality on a domain | Every input satisfying a precondition terminates with a related result. |
| Productivity | Every permitted finite observation of a produced object is delivered after finite computation, with any required environmental progress stated. |
| Causality | Agreement on specified input prefixes implies agreement on output prefixes. This does not itself bound runtime or ensure progress. |
| Normalization for conversion | The selected reduction/conversion procedure has the required termination and correctness properties on its specified fragment. |
| Checker termination | The algorithm searching for certificates returns. This is independent of whether the checked program terminates. |

These are proposed distinctions for this project, not claims that all source
languages use those words identically. An infinite stream need never finish
producing. The relevant termination questions concern its finite observations.

For a selected operational semantics, define `Evaluates(p,x,v)` declaratively.
A certifying analysis returns evidence for
`∀ x, Pre x → ∃ v, Evaluates(p,x,v) ∧ Post x v`, or a certificate that a small
checker validates to establish that proposition. Well-founded descent is one
certificate format, not the definition of termination itself. To cover
nondeterministic execution, specify whether all permitted executions must
terminate; existence of one evaluation is weaker.

The analysis result should distinguish `certified evidence`, `unknown`, and
`refuted counterevidence` when supported. Exhausted fuel, failed synthesis or
an unsupported recursive pattern means unknown, not nontermination. A checker
can be total by bounding search without pretending to decide all totality
questions. Completeness claims must name a restricted syntax, certificate
language or supplied-annotation discipline.

For codata, use an observation specification `Obs(p,input,n)` for the first
`n` outputs, and prove finite delivery plus compatibility as `n` increases.
A state-based implementation additionally needs an invariant and an observation
simulation. Bisimulation can prove equality of infinite behaviors; a weak
simulation that permits unlimited silent steps does not alone prove delivery.
Include a decreasing stuttering measure, a finite-step bound, or a separate
progress argument when silent steps are permitted.

The compositional obligation for sequential programs is that the first
component's postcondition supplies the second component's termination domain.
For stream processors, a useful interface gives a finite input-demand function
`d(n)` and a finite computation bound for producing `n` outputs. Demand maps
compose by substitution: a downstream demand `d_g(n)` requires upstream input
`d_f(d_g(n))`. This is a proposed sufficient condition, not a requirement that
all productive processors admit a uniform input-independent bound. Adaptive
processors may need a demand relation depending on observed values.

An optimizer must preserve this operational observation contract when
productivity is required. Equality of abstract streams or equality of returned
values conditional on returning is insufficient. The same issue applies to
termination: an implementation can agree on every result it returns and still
diverge on an input where the original returns. This extends the project's
existing distinction between value preservation and resource preservation.

## A declarative specification of elaboration

A useful semantic output is the set of admissible elaborations of a surface
phrase in its declared environment and context. Propose a relation of the form

```text
Elaborates(Δ, Γ, surface, expectedType?, Δ', core, inferredType, requirements)
```

It must establish well-formed environment extension, scoping, target typing,
and the intended meaning of the source constructs. Typing alone does not prove
that a syntactically valid output represents the intended input. The relation
can retain implicit arguments, coercions and overloaded choices when those
choices affect meaning.

During elaboration, unresolved metavariables and universe variables belong to
an explicit constraint context. An intermediate result specifies the valid
solutions to its constraints; later stages refine this set while preserving
its interpretation. A final accepted declaration supplies a solution and closes
all required obligations. Unsolved constraints must not be quietly replaced
by axioms. Soundness, completeness for a chosen fragment, termination of search,
and diagnostics are separate contracts.

Relational composition expresses admissible intermediate translations without
requiring a unique result. To compose under binders and across dependent
declarations, prove weakening, substitution and environment-extension
compatibility. If two successful elaborations must mean the same thing, prove
coherence under explicit resolution policies. Otherwise retain intentional
ambiguity or reject it. Kernel acceptance alone establishes neither this
coherence nor source fidelity.

Bidirectional typing is a suitable starting discipline: checking against an
expected type and synthesizing a type divide the annotation burden. It does
not guarantee decidability or completeness for every dependent feature.
[Dunfield and Krishnaswami's survey](https://research.cs.queensu.ca/home/jana/papers/bidir-survey/)

Retain generated code and computational witnesses in data-bearing types.
The fact that admissibility is a proposition does not make the elaborated
program, a selected dependent pair witness or a stream state erasable. This is
the same distinction recorded by the project's relation-witness construction.

## Small tests that can change the design

These are proposed experiments, independent of existing application priorities.

1. **Total stream corecursion.** Encode a state step and compare the coalgebra
   interpretation, `Nat → A` observations and an explicit stateful realization.
   Prove compatibility for every finite observation. Add `map`, `zip` and a
   prefix `scan`, carrying termination assumptions for element operations.
2. **Selective output.** Filtering the constant-zero stream for positive
   elements cannot deliver its first output. A total stream-to-stream filter
   therefore needs a hypothesis of sufficiently many matches, a supplied
   executable search certificate, or a partial-output interpretation. Contrast
   it with `filterMap : Stream A → Stream (Option B)`, which emits an observation
   at every input position. Retain those different meanings in the frontend.
3. **Feedback and silent work.** Compare a guarded producer with a loop that
   repeatedly changes internal state but emits nothing. Require the certificate
   interface to reject the inference from state-transition safety to
   productivity. Test that fusion preserves finite delivery as well as values.
4. **Witness-bearing elaboration.** Elaborate a small dependent declaration
   that computes a vector together with its length, then a consumer indexed by
   that length. Check substitution, universe constraints and retained witness
   computation. Include an ambiguous overload and an unresolved implicit
   argument as negative cases. A proof-irrelevant existence theorem alone must
   not count as the executable output.

The first design decision is which observation and evaluation semantics the
next fragment promises. Then implement one certifying analysis and one small
elaborator against these relations. A shared specification can support several
checkers, source syntaxes and targets without demanding that their inference
algorithms agree. Transport to another mathematical setting must separately
preserve the required natural numbers, well-foundedness, coalgebra/fixed-point
structure and observations; the existence of these constructions in Lean's
host mathematics does not supply them in every internal setting.

## Checked bounded elaboration

The [bounded elaboration experiment](bounded-elaboration.md) implements the
#147 contract for typed natural expressions and length-indexed vector packages.
It separates source fidelity, constraint solutions, target typing and final
acceptance, with substitution/environment compatibility and two admissible
strategies. The note states its monomorphic universe boundary, caller effort,
checked dependent-data examples and unsupported inference features.

# Optimization transport, observations and recovery contracts

Research for [#196](https://github.com/VladimirMarko/conaled/issues/196),
2026-10-28. Inspection baseline:
[`6f4bead0d1ec9686b31a6d6f1e628926e61ec1d1`](https://github.com/VladimirMarko/conaled/tree/6f4bead0d1ec9686b31a6d6f1e628926e61ec1d1).
Repository links below refer to that baseline unless describing historical commits.
This is a scoped investigation, not completion of #196 or an architectural decision.
Named Lean declarations are existing source evidence; displayed derivations and
proposed experiments are **not newly checked Lean claims**. No runtime or physical
recovery experiment was performed.

Optimization already contributes to the interaction study: its indexed
`observationSquare` is reused by
[`Interaction.Evidence.observationSquare`](../../Applications/Interaction/Evidence.lean).
The next useful step is to distinguish permitted observations from guarantees
about every world consistent with an observation. Ordinary predicate substitution,
relational images and universal requirements provide that distinction. They do
not choose a recovery mechanism or establish environmental assumptions.

## What the optimization history established

The [original #110 research commit](https://github.com/VladimirMarko/conaled/commit/cfa7ccb5b21b6f9841b4f236c8aa6b6eb909b89c)
already defined pullback as precomposition, `C*J = J ∘ C`. Its
[research note](compositional-optimization.md#pullback-and-optimization-transport)
also pulled back target predicates and admissibility relations, separated
workload maps, and required cost agreement and candidate coverage for optimality.
It did not propose constructing a categorical pullback object to run optimization.

The [#112 implementation](https://github.com/VladimirMarko/conaled/commit/dc0e93636776750b7048ee00c6976989ece22f47)
made those distinctions explicit in
[`Basic`](../../Applications/Optimization/Basic.lean),
[`Transport`](../../Applications/Optimization/Transport.lean) and
[`Relations`](../../Applications/Optimization/Relations.lean):

- `pullback` and `pullbackWorkload` have identity and composition laws;
  their definitions remain unchanged at the inspection baseline.
- Least-cost minimizers, Pareto candidates, infimum values and attainment
  are separate. `select` uses classical choice only when attainment is supplied.
- `minimizer_image` needs monotone cost translation and cost agreement.
  Global `minimizer_transport` additionally needs admissibility and a source
  alternative no more expensive than each target alternative. Surjectivity is
  sufficient, but stronger than this dominating-lift requirement.
- `minimizer_reflect` uses an order embedding and source feasibility.
  `value_transport` uses `sInfHom` and exact coverage. Monotonicity alone
  does not supply either reflection or infimum preservation.
- `selectionSquare` relates an implemented candidate to the set of minimizers,
  retaining the problem index; `boundSquare` records feasibility and a bound.
  Neither forces a tie-breaker into the mathematical specification.

Later refinements extended the uses rather than replacing precomposition.
[#151](https://github.com/VladimirMarko/conaled/commit/94ce623) added thinning;
[#163](https://github.com/VladimirMarko/conaled/commit/8504c9c) factored positional
first/last minimum contracts. Current
[`argmin_map`](../../Applications/Optimization/SelectionMap.lean) proves exact
transport of the particular first-tie list selector through a map; this stronger
observation is separate from set membership.
[#164](https://github.com/VladimirMarko/conaled/commit/fecd73b63db45082976ccdd96edb17ec6dbbcc89)
added `observationSquare`, sending a permitted set to its ordinary image under
an observation function. It requires no objective or inverse.
[#113](https://github.com/VladimirMarko/conaled/commit/a24253f0dacb6721bdbfb25acca0fd1e62aabcf3)
subsequently supplied retained incremental state and resource contracts,
addressing proposals that the original research note had left open.

Thus the historical lesson for #196 is the separation of defining a transported
objective or requirement from proving a preservation theorem. Equality of program results
does not establish cost agreement; equality of recorded outcomes does not
establish durability, absence of duplicate effects or eventual completion.

## Which constructions are being compared

For a function `f : X → Y`, predicate pullback is `f*Q(x) = Q(f x)`.
It is substitution, just as objective pullback is substitution into a cost
function. In sets it is inverse image. It requires neither injectivity nor
an algorithm for evaluating `Q`.

A categorical pullback in types instead constructs
`{(x,y) | d₁ x = d₂ y}` from two maps into a common type.
[`Squares.synchronized`](../../SquareKit/Combinators.lean) uses precisely this
carrier through [`Comma.Exact.agreement`](../../SquareKit/CommaAgreement.lean).
Its composition and agreement theorems retain both representations and their
common decoded observation. The local agreement module does not itself state
a generic universal-property theorem; Mathlib's pinned
[`Types.pullbackLimitCone`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Limits/Types/Pullbacks.lean)
supplies the standard type-level construction. Agreement can combine witnesses,
but two agreeing corrupt observations still agree. Independence or truth
does not follow from the carrier.

A comma object retains a connector between interpreted objects, and a comma
morphism retains both operations and a commuting comparison. The existing
[`SquareKit.Comma`](../../SquareKit/Comma.lean) separates raw operations,
equivalence and laws. Its `HomEquiv` is an equivalence, so replacing it with
one-way refinement is not an existing lax-square API.
[`RelSquare`](../../SquareKit/Relations.lean) already handles preservation of
arbitrary relations, and `witnessSquare` presents this on total witness spaces.
These tools suffice for the examples here; a general lax or ordered comma
construction would need its own composition hypotheses and demonstrated reuse.
The glossary's homotopy pullback retains comparison isomorphisms and is yet
another construction; no such boundary data are needed in this investigation.

Elliott's [*Timely Computation*, §§9–12](https://conal.net/papers/timely-computation/paper.pdf)
uses comma composition and changes interpretations to separate signals, values
and timing. The local
[`Digital`](../../Applications/Timing/Digital.lean) contract retains stability
and a timing map. This supports the method of exposing distinct observations,
not an inference that timing analysis already models distributed recovery.
The [timing ADR](../adr/0008-timing.md) records the concrete restrictions.

## Existential observations and universal requirements

Here is a mathematical derivation with explicit orientation. For a relation
`r : X → Y → Prop`, define predicates

```text
E_r(P)(y) = ∃ x, P(x) ∧ r(x,y)
U_r(Q)(x) = ∀ y, r(x,y) → Q(y).
```

Then `E_r(P) ⊆ Q` iff `P ⊆ U_r(Q)`: both mean that every related pair
whose first component satisfies `P` has second component satisfying `Q`.
For `q : Y → Z → Prop` and the existing existential `Relation.Comp`:

```text
E_(Comp r q)(P) = E_q(E_r(P))
U_(Comp r q)(Q) = U_r(U_q(Q)).
```

For the second law, expand the left side as
`∀ z, (∃ y, r(x,y) ∧ q(y,z)) → Q(z)`; moving the witness into the
universal premise gives the right side. No finiteness, decidability,
termination, totality or choice is needed. For the graph `r(x,y) := f(x)=y`,
`U_r(Q)=f*Q` and `E_r(P)=f '' P`. These are prospective relation-level
lemmas, grounded in Mathlib's existing
[`Relation.Comp`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Logic/Relation.lean)
and [`Set.image_subset_iff`, `image_comp`, `preimage_comp`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Set/Image.lean).

This also explains the current compiler-facing contract.
[`Interaction.Refines r source target`](../../SquareKit/InteractionContracts.lean)
says `target ⊆ E_r(source)`. Therefore `source ⊆ U_r(Q)` implies
`target ⊆ Q`. Existing `Refines.property` proves this transfer through its
`respects` premise. This does **not** say that every source world related to
a target world is permitted. Abate et al.'s
[*Trace-Relating Compiler Correctness and Secure Compilation*](https://link.springer.com/chapter/10.1007/978-3-030-44914-8_1)
likewise treats different trace spaces and distinguishes forward property
translation from backward requirements. The formulas above are this note's
explicit derivation, not a claim to have ported that paper's development.

Environmental assumptions can restrict the behavior sets in this statement.
For target assumption `A_T`, prove refinement for the actual behaviors admitted
under `A_T`, and prove the source requirement `U_r(Q)` under the corresponding
source assumptions. A deterministic environment interpretation can pull a
predicate back by substitution; a many-valued interpretation needs the stated
universal requirement. Neither operation proves that the environment satisfies
the assumption, or that independently specified components permit compatible
environments when composed.

For observation-based knowledge the relation points the other way. With
`o : World → Obs`, admissible worlds `A`, and property `P`, define

```text
K_A(P)(v) = ∀ w, w ∈ A → o(w)=v → P(w).
```

This is `U_r(P)` for `r(v,w) := w∈A ∧ o(w)=v`. Permitted observations
are instead `o '' A`. An admissible observation must have a witness in that
image: an empty fiber makes `K_A(P)` vacuously true. On unrestricted predicates,
existential image, inverse image and universal image along a function form
the adjunctions `∃_o ⊣ o* ⊣ ∀_o`; restricting to `A` means using `o` on
the subtype of admissible worlds. The pinned Mathlib already implements the
universal image as [`Set.kernImage`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Set/Operations.lean)
and proves both adjunctions as
[`Set.image_preimage` and `Set.preimage_kernImage`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Set/Lattice/Image.lean).
Reuse these APIs in the function case; no new category hierarchy is required.

## Worked recovery and interference cases

Use the existing bounded evidence model, not a claim about an OS adapter.
[`Evidence.Attempt`](../../Applications/Interaction/Evidence.lean) permits
`initial` and `unknownEffect` from `initial`. Both observe `none`, but their
effect counts are zero and one. For
`A={initial,unknownEffect}`, `none∈observe '' A`, while
`K_A(fun w => w.effects=0)(none)` is false. Replacing the universal quantifier
with an existential one would approve absence using `initial` even when the
actual world is `unknownEffect`. `retry_duplicates` exhibits the second effect;
`no_effect_decision` proves the observation cannot classify both worlds.
This is a checked counterexample to inferring retry safety from silence.

A positive specialization uses recovery that observes existing evidence
without repeating the effect. `recover_published` and `recover_effects` prove
that `Recover` preserves publication and the effect count. If evidence is
published, the modeled `Acknowledge` step exists and sets acknowledgment.
Consequently `publication_then_recovery_then_ack` is safe through any finite
sequence of permitted recovery steps. In the formula above, `Safe P C Q`
is exactly `P ⊆ U_C(Q)`; the composition law organizes this proof.
Existence of that finishing step is not guaranteed scheduling:
`interrupted_run` permits endless loss of acknowledgment and
`interrupted_no_ack` disproves unconditional eventual acknowledgment.

The second specialization is captured compilation.
[`Snapshot.compile_sealed`](../../Applications/Interaction/Snapshot.lean)
composes `Seal inputs`, finitely many `Environment` steps and
`CompileCaptured`. The essential hypothesis is that the environment preserves
captured inputs. Its `captured_stable` theorem supplies the intermediate
assertion required by `safe_interference_seq`.
`missing_stability_counterexample` shows ordinary endpoint contracts fail when
arbitrary interference is inserted. `never_coexisted` separately shows that
captured bytes need not have existed simultaneously in the live world.
Predicate transport preserves precisely the chosen claim about captured data.

The current authority-inspired
[`Obligation`](../../Applications/Interaction/Obligation.lean) experiment retains
receipt, intent, attempts and effects separately. `Events.interpret_simulation`
in [`InteractionEvents`](../../SquareKit/InteractionEvents.lean) lifts primitive
simulations through scripts; callers avoid repeating sequence induction.
[`InteractionInterfaces`](../../Examples/InteractionInterfaces.lean) checks
receipt forgery, lost replies, delayed attempts and a successful initial script.
It also proves `script_is_not_authority`: unrestricted event syntax permits an
effect without acceptance or a lease. Pulling back a desired policy does not
make the handler enforce it. The scripts are finite lists without reply-dependent
branching or interruption inside a handler. Those behaviors must enter a richer
relation or language before a transport theorem can account for them.

The [source assessment](pre-conaled-authority-assessment.md) pins the older
authority at `1bb68d01deedbf7bd9ae06fdc176b3f04625e1a9`, including
[`Recovery.lean`](https://github.com/VladimirMarko/t3swarmforge/blob/1bb68d01deedbf7bd9ae06fdc176b3f04625e1a9/spikes/authority/lean/Recovery.lean).
Its lease/observation certificates concern selected local transitions. The
Conaled experiment's `delayed_attempt` demonstrates why a lease count alone
does not fence a downstream effect. A future safe-retry contract must establish
idempotence, enforced fencing or sufficiently strong reconciliation. Encoding
that obligation as a predicate does not discharge it.

## Resources and limits of reuse

For resources, ordinary pullback still transports a stated objective through
an interpretation. Current [`Resources.Measured`](../../Applications/Resources/Measured.lean)
additionally proves `reweight_bind` for additive homomorphisms and
`reweight_bound` for monotone maps; [`Workload`](../../Applications/Resources/Workload.lean)
lifts execution and reweighting through sequences. These reusable laws,
also exercised by the [cross-domain accounting work](adwh-potential-accounting.md),
distinguish value erasure from resource preservation.
[#113's `Stateful.Laws.comp`](../../Applications/Incremental/Stateful.lean)
retains boundary state and emitted changes. Its deterministic valid-state repair
does not model crash recovery just because both operations are called repair.

A proposed worst-case recovery cost is a supremum over permitted outcomes;
optimization's `value` is an infimum over controllable candidates. Switching
those quantifiers can invent a policy that chooses after learning the fault.
`∃ policy, ∀ environment` and `∀ environment, ∃ policy` are different contracts.
Probability requires distributions or kernels and correlation assumptions,
not a reinterpretation of nondeterministic existence. No probabilistic or
strategic recovery theorem follows here.

For progress, [`FRP.Trace.eventual_observation`](../../Applications/FRP/Trace.lean)
already exposes fair delivery and source progress. Reuse that discipline of
explicit assumptions; endpoint universal requirements alone say nothing about
termination. Likewise agreement between checkers does not remove shared bugs,
model errors or the trusted checking/execution boundary documented in
[`README`](../../README.md#proof-and-execution-boundary). Codata, interactive
strategies, correlated failures and distributed impossibility results remain
broader #196 investigations; this note has not established a common encoding.

## Bounded next checked experiment

Within #194's existing consumers, first test the small relation-level laws
above using Mathlib sets and `Relation.Comp`. Require checked graph
specializations matching `pullback` and `observationSquare`, then recover the
existing `Safe` and `Refines.property` formulations. Keep admissible-observation
inhabitation explicit. This stage depends only on current shared contracts.

Next apply the same laws to the evidence and captured-compilation cases.
Acceptance requires both successful witnesses and the lost-acknowledgment,
empty-fiber, delayed-attempt and missing-stability counterexamples. Compare
direct relations with event interpretation against the same independent
specifications. Record which primitive obligations are proved once and which
remain at each call site; moving the same proofs into a record is not an
improvement in caller effort. If these laws merely rename existing proofs,
keep them as examples rather than introducing a public abstraction.

A later bounded resource case can count recovery attempts and external effects
separately, including an interrupted attempt. Its acceptance criterion is an
explicit fault-budget assumption and a counterexample without that budget.
It depends on the first comparison and a chosen transition/cost model; it is
not authorization to select a universal recovery IR. Any formal implementation
must follow statement review, checked specializations, fresh build and exhaustive
axiom audit. The current milestone changes documentation only.

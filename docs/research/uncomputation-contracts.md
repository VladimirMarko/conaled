# Forgetting, uncomputation and reversible target contracts

Research for [#261](https://github.com/VladimirMarko/conaled/issues/261),
2026-10-30. Local inspection baseline: `85e92578a14c0d29f0befd1c2716593a5b5d3744`.

Uncomputation is useful to investigate before implementing a physical backend:
clean workspace and preservation of coherent input/output behavior are already
precise semantic obligations. The current retention service is a poor first
consumer. Its expiry contract deliberately identifies different histories;
uncomputation can remove redundant scratch while retaining information needed
to reverse the computation. These conclusions follow from the finite examples
below, not from an assumption about energy savings.

## Operations with different contracts

| Operation | Information and observations |
|---|---|
| Observation restriction | Change the observer or its admitted requests. The underlying state need not change. Equality after an observation map does not imply an invertible state change. |
| Logical erasure | A many-to-one state map, such as either bit becoming zero, loses distinctions in that state description. Information can remain elsewhere in a larger physical system. |
| Physical reclamation | Make storage available to a new owner after old readers and aliases lose access. Reclamation need not zero the storage, erase its physical information, or invert its last computation. |
| Reversible classical computation | An injective transition on admitted whole states has an inverse on its image; a finite total implementation on the same state space is a permutation. Include retained input, scratch and control state in the claim. |
| Recomputation | Re-evaluate a value from retained dependencies. It can replace storage with work, without reversing any transition. Ordinary overwrites remain ordinary overwrites. |
| Uncomputation | Apply an inverse to restore scratch while preserving the desired result. The dependencies, initialization condition and permitted intervening use determine whether this works. |
| Quantum measurement | An instrument produces a classical result and a conditional state. Ignoring its outcome generally changes coherent observations. |
| Quantum discard | Partial trace removes a subsystem from the description; it need not preserve the pure-state computation intended on the remaining subsystem. |
| Quantum reset | A channel replaces a subsystem with a specified state. It is not a unitary inverse on that subsystem. Resetting entangled scratch does not restore lost coherences in the retained subsystem. |

The quantum distinctions use density-operator semantics; the explicit partial
trace example below makes the failure observable. Silq's authors describe why
simply dropping temporary values can change the computation, and give a safe
uncomputation discipline using classically describable computations and preserved
dependencies. This is one sufficient discipline, not a claim that all safe
cleanup must use its type system. [Silq, introduction and §§2–4](https://files.sri.inf.ethz.ch/website/papers/pldi20-silq.pdf).

## Classical reversibility and the physical boundary

Bennett's construction retains the input, records enough history to reverse the
forward computation, copies the classical output onto blank storage, and runs
the computation backward. The history becomes blank; input and output remain.
This avoids confusing removal of redundant history with erasing arbitrary input.
Its temporary storage can be large. [Bennett, *Logical Reversibility of
Computation* (1973), pp. 525–529](https://worrydream.com/refs/Bennett_1973_-_Logical_Reversibility_of_Computation.pdf).

There is no evidence here that adding inverse instructions improves energy use
on a conventional processor. A CPU running a reversible algorithm is not thereby
a thermodynamically reversible device. But “pointless on conventional systems”
is too broad: ordinary systems can simulate and validate reversible algorithms,
and related checkpoint/recomputation schedules have practical conventional
consumers. Argonne's Checkpointing.jl implements such schedules for reverse-mode
AD. That is evidence for recomputation's usefulness, **not** evidence that
checkpointing reverses machine instructions or lowers dissipation.
[Project's own implementation and scope](https://github.com/Argonne-National-Laboratory/Checkpointing.jl).

For a precise physical statement, take Reeb and Wolf's finite-dimensional system
and reservoir, initially a product state, a reservoir initially Gibbs at inverse
temperature `β = 1/(k_B T) > 0`, and joint unitary evolution. With natural-log
entropy decrease `ΔS = S(ρ_S) − S(ρ'_S)` and heat delivered to the reservoir
`ΔQ = tr[H_R(ρ'_R − ρ_R)]`, their equality is

`β ΔQ = ΔS + I(S':R') + D(ρ'_R || ρ_R) ≥ ΔS`.

The familiar `k_B T ln 2` lower bound concerns reducing an unbiased bit's entropy
by `ln 2` under these hypotheses. It is not a charge per source-level assignment.
Initial correlations require different accounting; finite reservoirs strengthen
the bound, and exact pure reset has additional attainability restrictions.
[Reeb–Wolf, §2.1, Theorem 3, §§3.2–3.3 and 5](https://arxiv.org/pdf/1306.4352).

A lower bound is not an implementation attaining it. Bérut, Petrosyan and
Ciliberto measured erasure in a colloidal double-well memory and report approach
to the bound for long erasure cycles; their experiment does not establish the
energy of our programs or a quantum processor.
[Experiment and error discussion](https://arxiv.org/abs/1503.06537v1).
A prospective hardware claim must separately account for control, timing,
preparation, cooling, error correction and readout, specify which costs are
inside the measurement boundary, and supply device evidence. Neither logical
invertibility nor a gate-count proof supplies those premises. In particular,
this note makes no numerical prediction about finite-time dissipation or
fault-tolerant overhead.

## Finite oracle with a clean workspace contract

The examples are independently specified mathematical fixtures, with executable
finite evidence in [check.py](../../experiments/uncomputation/check.py). They are
not new Lean theorems or measured devices.

Inputs are bits `a,b,y`, with scratch `t` initially zero. The desired operation
is `(a,b,y) ↦ (a,b,y XOR (a AND b))`; the input is retained, and scratch must end
at zero. Run three gates on wire order `(a,b,t,y)`:

1. Toffoli with controls `a,b`, target `t`.
2. CNOT with control `t`, target `y`.
3. The same Toffoli again.

Each gate is a permutation, and all eight admitted input cases give
`(a,b,0,y XOR (a AND b))`. The checker also tests the full circuit followed by
its reverse on all sixteen four-bit states. A dirty initial `t=1` violates the
clean contract; changing `a` between compute and uncompute can leave `t=1`.
The inverse needs the original controls. “No longer referenced” is insufficient.

Interpreting these basis permutations linearly gives unitary gates. The exact
basis equality gives, by linearity, the same oracle for arbitrary complex
superpositions and inputs entangled with an untouched reference `R`. More
explicitly, the required channel equality on every `ρ_XYR` is

`C (ρ_XYR ⊗ |0><0|_T) C† = (V ⊗ I_R) ρ_XYR (V† ⊗ I_R) ⊗ |0><0|_T`,

with wires reordered as needed, `X=(a,b)` and `V` the specified oracle. This
states both coherent output preservation and scratch independence. It is a
mathematical argument about these permutations; the script checks finite basis
cases and selected exact real superpositions, not all complex density matrices.

CNOT copies *basis labels* into a zero target. On `|+>|0>` it produces a Bell
state, not `|+>|+>`. It cannot be treated as cloning an unknown quantum state.
The linear extension above is legitimate controlled computation, consistent
with the oracle construction in [Silq's own overview](https://silq.ethz.ch/overview).

Take `b=1,y=0` and `a` in an equal superposition. Before cleanup the state is
`(|0100> + |1111>)/√2`. Tracing out `t` removes the off-diagonal terms of the
retained `(a,b,y)` density matrix. After correct cleanup those terms remain:
the state is `(|0100> + |1101>)/√2`. Computational-basis output probabilities
agree, but interference distinguishes the two. The checker repeats the test
with an extra reference bit entangled with `a`. Reset or measurement of `t`
with its result ignored has the same damaging retained marginal in this case.

Phase behavior matters too: compute `t=a`, apply `Z` to `t`, then uncompute.
The result is `Z|ψ> ⊗ |0>`, not `|ψ> ⊗ |0>`. The checker uses signed exact
amplitudes to test this. Cleanup preserves the *specified use's* effect.

A clean pure marginal `|0><0|` actually does force product independence in
standard density semantics. The danger is checking only some observations, or
returning a borrowed *mixed* marginal: a Bell pair has maximally mixed marginal
but is not the product of two maximally mixed states. The checker distinguishes
those joint states. A dirty borrowed ancilla would require preserving its joint
state with its reference, a stronger contract than this zero-ancilla experiment.

## Work, depth and live workspace

Count Toffoli and CNOT each as one logical gate, with depth one per disjoint-wire
layer. This gate library deliberately leaves Toffoli decomposition and routing
unpriced. Inputs and caller-owned outputs are excluded from **scratch** counts,
but remain live and cannot be reclaimed. Gates act on distinct control/target
wires. Table entries describe explicit schedules, not optimality theorems.

Two independent AND oracles, with four inputs and two retained output bits, give:

| Schedule | Gate work | Depth | Peak scratch bits | Scratch still occupied at return |
|---|---:|---:|---:|---:|
| Compute both scratches, use both, retain garbage | 4 | 2 | 2 | 2 |
| Same parallel schedule, then uncompute both | 6 | 3 | 2 | 0 |
| Compute/use/uncompute first, reuse scratch for second | 6 | 6 | 1 | 0 |

Only the latter two satisfy the clean contract. Including inputs and outputs,
peak wire counts are eight and seven respectively. The script checks disjoint
layers, both clean schedules on all 64 input/output basis assignments, and their
work/depth counts. The retained-garbage route agrees on classical output values
but can fail the coherent contract just shown.

For *two separated uses of the same* `a AND b`, retaining one scratch requires
one Toffoli and two CNOTs, followed by one Toffoli if clean return is required:
four gates. Uncompute after each use and recompute before the next: six gates.
Both peak at one scratch bit, but the second releases it during the gap, where
another operation may need it. A conventional program can instead assign the
AND twice and discard each temporary; that is two AND evaluations and two
output uses, with ordinary overwrite/reclamation behavior. Those are not counts
in the reversible gate library. Re-evaluation from changed or missing inputs
would be wrong in either setting. This separates peak space, live intervals,
work, and available parallelism.

Resource-aware uncomputation is a compiler problem even without a thermodynamic
model: SQUARE studies when ancilla reuse justifies extra work under locality and
parallelism constraints. Its modeled evaluations motivate these axes; we do not
transfer its reported improvements to our library or claim a general optimum.
[SQUARE, §§II–IV](https://arxiv.org/pdf/2004.08539).

## Why the retention service is a different consumer

[#247's assessment](history-retention-contracts.md) and
[#251's implementation](../../Applications/Durability/Retention.lean) preserve
retained suffix reads, cumulative parity and bounded sequential retry behavior.
For `W=1`, `K≥3`, histories `[0,0,0]` and `[1,1,0]` both produce the snapshot
`position=3, pastParity=0, items=[0]`. Their discarded prefixes differ. The
checker calculates this collision independently of the Lean implementation.
No inverse of this snapshot abstraction can recover both histories. This is a
collision of the semantic snapshot map, not a claim that every byte in both
physical banks is already identical.

A reversible implementation could retain additional distinguishing information
in an input, log or environment; that changes its resource accounting. The
proof-side history in `Represents` is not runtime storage available to cleanup.
Once information has genuinely been lost, applying an inverse to the remaining
snapshot cannot reconstruct it. Likewise, preserving parity is not preserving
membership, old retries or arbitrary historical observations.

The existing service keeps its fixed incarnation, finite limit `K`, expiry
replies, no-wrap exhaustion, affine reader ownership and restart fencing. Safe
bank reuse requires the absence of admitted readers, recovery cursors and obsolete plans
referring to the bank; it does not require a unitary inverse or a zeroed bank. Atomic durable
publication after persistence still determines crash behavior. Uncomputing a
private, reproducible temporary could in principle fit *inside* that protocol,
but would not justify undoing acknowledged effects or relaxing a reader premise.
See [bank access](../../Applications/Durability/RetentionBanks.lean),
[ownership](../../Applications/Durability/RetentionOwnership.lean) and
[resource bounds](../../Applications/Durability/RetentionResources.lean).

The reusable question is: **what is preserved, what dependencies remain, and
under what contract may storage be reused?** It does not yield one shared
operation identifying expiry, affine release and quantum cleanup. Reopen a
retention-specific experiment only if a concrete target supplies reversible
private scratch, a preserved dependency source and a workload/resource model
showing a reason to use it. No retention retrofit follows from this note.

## Local reuse and missing semantics

This is a scoped inspection of the following entrypoints, not a claim to have
proved absence across Mathlib. The [logic-correspondence atlas](logic-correspondence-atlas.md)
M2 and Q5/Q6 already distinguish monoidal infrastructure from quantum semantics;
this note adds a cleanup consumer rather than repeating that survey.

| Existing component | Reuse and remaining obligation |
|---|---|
| [Category operations](../../SquareKit/Category.lean), [squares](../../Squares.lean) and Mathlib category/monoidal infrastructure referenced by atlas M2 | Reuse composition, equivalences and explicit preservation statements. Do not impose cartesian products on a tensor-only construction. |
| [Matrix category](../../SquareKit/MatrixCategory.lean) and [linear matrix backend](../../Applications/Linear/Matrix.lean) | Finite coefficients and matrix composition are useful. Current categorical products use **sums of coordinates**, not tensor products of quantum systems. ADR 0009's transpose is not automatically a complex adjoint. Need tensor, conjugate transpose, normalization/unitarity and the chosen state/channel semantics. |
| [Circuit syntax](../../Applications/Circuits/Syntax.lean) and timing interpretation | Existing syntax permits termination, projections and pairing; gates include NAND/NOR. That is cartesian Boolean circuitry, not a reversible gate language. Reuse the interpretation/preservation pattern, not an unrestricted quantum interpretation of these constructors. Signal timing does not prove quantum noise or energy bounds. |
| [Measured computations](../../Applications/Resources/Measured.lean) | Reuse separation of value and resource observations. Additive work composes directly; circuit depth needs scheduling/parallel composition, peak live workspace needs lifetime state. A writer count alone cannot identify them. |
| [Finite Metropolis–Hastings](../../Applications/Probability/FiniteMH.lean) | `detailed_balance` concerns probability flux under a distribution. A stochastic transition can satisfy it without a single-valued inverse. It is not the reversible-permutation or unitary contract. |
| Retention modules above | Reuse explicit admission, ownership and refinement boundaries as design discipline. Their ghost histories and affine driver assumptions do not implement coherent quantum ownership. |

No checked quantum backend is supplied by these inspected interfaces. Adding a
quantum gate to the cartesian frontend would expose an actual structural
mismatch: unrestricted contraction cannot mean unknown-state cloning. Hand this
consumer constraint to [#235](https://github.com/VladimirMarko/conaled/issues/235)
when implementing a tensor fragment; preserve existing ordinary cartesian
specializations. This is a mathematical requirement, not observed Lean
elaborator failure or an assessment of an author's capability.

## A bounded next experiment and its proof boundary

A justified followup is **one clean-ancilla combinator with two interpretations**,
not a generic quantum compiler. Implement finite reversible Boolean circuits
with identity, sequential composition, disjoint tensor, inverse, CNOT and
Toffoli. Use a declared zero-initialization/release boundary, not arbitrary
terminal maps. Interpret as finite permutations and as complex permutation
matrices on tensor-indexed basis states. Reuse Mathlib operations and local
squares wherever the hypotheses fit.

Acceptance should include the independently specified AND oracle and the two
schedules above, a general compute/use/uncompute correctness statement with
explicit preserved controls, inverse and clean-output premises, and extension
by an untouched reference system. Prove output correctness **and** scratch
factorization, inverse/composition/tensor preservation, and actual schedule
work/depth/live-space bounds. Include the dirty-control, phase and
trace-out counterexamples. A phase-sensitive example can use a diagonal `Z`
interpretation alongside permutations; state the extended gate vocabulary
rather than pretend `Z` is a Boolean permutation. Develop ordinary checked
specializations through EDD, statement review and the repository proof audit.
No automatic synthesis, borrowed dirty ancillas, approximate gates, variable-size
quantum data, storage service changes or energy claims belong in that experiment.

| Boundary | Required evidence; what can be done without hardware |
|---|---|
| High-level specification → clean combinator | Independent oracle/channel contract, admissible dependencies and ownership, compositional preservation. This is a mathematical proof task. |
| Combinator → circuit | Typing, inverse synthesis, tensor wire placement, initialization and clean release. Prove exact denotation and the selected resource events. |
| Circuit → finite matrix/channel | Gate matrices, adjoints, unitarity or explicit nonunitary channels, reference-system preservation. Exact finite semantics needs no device physics. |
| Logical gates → native gates and schedule | Decomposition, approximation error, routing and timing assumptions; refine resource events to a selected target. Current Toffoli unit counts stop before this boundary. |
| Schedule → noisy hardware | Calibration, dynamics/noise model, preparation/readout and error-correction assumptions; validate the claimed channel/error envelope against the device. |
| Hardware → heat/energy claim | System/reservoir boundary, thermal/correlation hypotheses, control and auxiliary costs, units, finite-time protocol and measured uncertainty. A semantic commuting square alone cannot discharge these. |

This note specifies that experiment; it does not begin it or select a permanent
language design. If a finite implementation reveals no reusable abstraction
beyond existing permutation and matrix interfaces, retain the examples and the
negative result. Revisit with a real coherent algorithm, a demonstrated author
burden or a target that needs scratch scheduling, rather than an arbitrary date.

## Reproduction and trust

Run `direnv exec . python3 experiments/uncomputation/check.py` from the repository
root. Python's standard library and exact rational arithmetic suffice. Successful
execution checks 16 inverse cases, eight clean-oracle cases, 64 paired scheduling
cases, 16 repeated-use comparisons, and explicit
phase/coherence/reference/dirty-workspace/marginal/retention
counterexamples. The independent specifications are Boolean AND/XOR, tensor
factorization of the expected vector, and the disclosed retention snapshot.
The script's evaluator, Python and these specifications are trusted; these
finite checks are not Lean kernel proofs, universal channel verification or
physical measurements. The main Lean build does not audit this isolated
experiment. This change adds no Lean declarations or tooling dependencies.

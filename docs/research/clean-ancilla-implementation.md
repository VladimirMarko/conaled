# Clean-ancilla semantics experiment

Implementation of [#264](https://github.com/VladimirMarko/conaled/issues/264),
following the [investigation](uncomputation-contracts.md). The scope is finite,
exact logical gates and zero scratch. No borrowed-dirty-ancilla, synthesis,
hardware, timing or energy contract is supplied.

## Choosing the semantic boundary

The discriminating cases were an AND oracle with arbitrary caller output,
cleanup with an untouched reference, dirty scratch, mutated dependencies,
phase kickback and loss of off-diagonal density entries under discard.
The first missing connection was from the independently specified XOR oracle
to a shared cleanup argument. The next was from a basis equality to arbitrary
complex amplitudes with a reference. `oracle_clean` and
`coherent_clean_reference` supply these connections.

| Candidate | What it supplies | What the cases require beyond it |
|---|---|---|
| Finite permutations | Reversible Boolean gates, composition, inverse and disjoint products of labels | Cannot express phase Z or initialize an extra wire as a permutation |
| Invertible linear maps | Linear extension and inverses | Invertible scaling by two changes norms; invertibility alone is insufficient |
| Unitary evolution | Coherent gates preserving the canonical complex inner product | Dimension-changing initialization and release require separate contracts |
| Isometric embeddings | Initialization into the zero-scratch subspace | Release is an inverse on that image, not arbitrary termination |
| Restricted-subspace equations | Exact specification of the permitted intervening use and inverse | Each interpretation must prove admissibility, not merely supply a linear map |
| Density operators and channels | Detect lost coherences under discard/measurement | A general channel library is unnecessary for the finite counterexamples |

The chosen shared statement is `cleanup_correct`: compute, use, undo composed
with initialization equals initialization composed with an independently supplied
output. Its assumptions are associativity, a left inverse on the initialized
subspace, and compatibility of use on the computed subspace. The latter is an
obligation, not a claim about arbitrary intervening operations. Identity laws
are available in the reused category interface but unused by this proof.
Tensor is needed to extend the construction to disjoint systems, not to prove
the three-composition equation itself.

This separates the shared argument from admissibility. The Boolean model admits
permutations; its coherent extension preserves `pairing`, the finite complex
inner product. `initZero` is an isometry. `IsClean` identifies its image; evaluating
scratch at zero is a release only on that image. This is not a global inverse or
a discard channel. Phase Z extends the gate vocabulary and has a separate
inner-product preservation theorem. Arbitrary linear maps are useful as an
ambient proof language, not an assertion of physical implementability.

The initial semantic checks (`coherent_unitary`, `initZero_isometry`, and
`coherent_clean_reference`) compiled before the oracle and schedule development.
They support the selection of permutations with a complex linear extension and
an explicit subspace boundary. Phase and trace-out cases require additional
finite operations but do not require changing the shared cleanup equation.

Silq provides a sufficient discipline based on classically describable
computation and preserved dependencies. This experiment checks a narrower
explicit contract; it does not implement Silq's type system or automatic
uncomputation. See the authors' [overview](https://silq.ethz.ch/overview) and
[paper, introduction and semantics](https://files.sri.inf.ethz.ch/website/papers/pldi20-silq.pdf).
The accepted investigation links Bennett and the resource-scheduling literature.
The authoritative API sources for this implementation are the pinned Mathlib
`Equiv`, `LinearMap`, `Matrix.ToLin` and `Matrix.Kronecker` modules.

## Coordinates and local reuse

`Core` reuses `SquareKit.CategoryOps` and its separate laws. The function
specialization reuses `SquareKit.FunctionCategory`. `Coordinates` uses the
same `LinearMap.toMatrix'`/`Matrix.toLin'` equivalence as `MatrixBackend` in
ADR 0009. It proves composition, identity, tensor/Kronecker and
inverse/conjugate-transpose correspondence for the admitted permutation maps.
The basis consists of delta functions on finite labels. It is orthonormal for
`pairing`; changing to an arbitrary nonorthonormal basis would require a Gram
matrix in the adjoint correspondence.

Product labels represent tensor systems. The coordinate sums used by existing
cartesian matrix clients represent direct sums, so their pairing/projection
interface cannot be reused as quantum tensor structure. Existing clients are
unchanged. There is no matrix-materialization cost or efficiency claim.

## Statement review and retained cases

The statements quantify over arbitrary complex vectors, including vectors that
do not factor across the retained system and its reference. Clean correctness
specifies output and scratch jointly; it is stronger than agreeing on basis
probabilities. The zero-scratch hypothesis is essential. `dirty_scratch` changes
the output and `mutated_control` leaves scratch occupied.

The phase case returns zero scratch with Z on the input, rather than claiming
identity on the input. `trace_loses_coherence` and `same_basis_observations`
distinguish equality of diagonal entries from equality of density operators.
Their unnormalized vectors avoid radicals; density entries scale quadratically.
`bell_marginal` uses normalized density entries to exhibit a mixed marginal
whose joint state is not a product. This does not contradict the standard
pure-marginal factorization property. Borrowed mixed scratch is outside the
release contract. `ignored_measurement` concerns measurement with the outcome
ignored, not a conditional postmeasurement pure state.

Schedule results use one logical gate per CNOT or Toffoli and one depth unit per
disjoint layer. Inputs and caller outputs remain owned; scratch may be released
only after its zero-state contract. Exhaustive finite propositions are Lean
kernel proofs, not `native_decide` evidence. No wall-clock or optimality result
follows. The earlier Python experiment remains independent exploratory evidence
with the trust boundary documented in the investigation.

## Handoff to #235

This consumer supplies a concrete mathematical mismatch for
[#235](https://github.com/VladimirMarko/conaled/issues/235), coordinated with
[#200](https://github.com/VladimirMarko/conaled/issues/200) and
[#8](https://github.com/VladimirMarko/conaled/issues/8): tensor composition and
clean-subspace release cannot inherit unrestricted cartesian contraction and
termination. CNOT correlates a superposition with scratch; it does not clone
that superposition. A frontend must preserve ownership of dependencies and
caller outputs, and expose compatibility of intervening use.

The bounded implementation needs no new universal category framework. Existing
category operations, equivalences and linear representations suffice, with a
small shared cleanup theorem. Lean's explicit product reassociation and wire
indices are encoding work, distinct from the mathematical ownership constraint.
The checked author specializations show how to supply a Boolean dependency and
obtain an oracle, and how to extend it by a reference. They are not an independent
human usability study. Automatic dependency inference, tensor surface syntax
and ownership diagnostics remain work for the architecture investigation.

`andCircuit_clean` connects the typed gate syntax to the shared oracle theorem
through a proved wire reordering. `Gate.involutive` establishes reversibility
from control/target disjointness. Each schedule has a permutation interpretation;
`parallel_coherent`, `serial_coherent`, `retain_coherent` and
`recompute_coherent` lift its Boolean contract to arbitrary amplitudes with a
finite reference. `clean_density_reference` separately proves the whole-operator
contract for the reusable oracle. `phase_cleanup` specializes the shared theorem
to the linear-map interpretation, demonstrating reuse beyond permutations.

`execute` checks allocation, gate support, disjoint layers and zero release at
every boundary. `plans_match` connects those events to the lists used for work
and depth. `workspace` derives peak and final scratch from the same event lists;
`gap_workspace` distinguishes retain from recompute during the gap. Both the
basis behavior and the ownership checks allow arbitrary caller output bits.

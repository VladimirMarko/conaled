# Finite quantum assertion soundness

Issue [#499](https://github.com/VladimirMarko/conaled/issues/499) delivers a native Lean specialization of CoqQ's measurement conditional and sequencing rules. The public client prepares a qubit, measures it, and uses the classical outcome to reset its state. Positivity, trace preservation, branch admissibility, and assertion soundness are proved from matrix operations. They are not fields assumed of a channel.

The entrypoint is [Examples/QuantumSemantics.lean](../../Examples/QuantumSemantics.lean), imported by `SquareApplications`. The library lives in [Applications/QuantumSemantics](../../Applications/QuantumSemantics/Core.lean).

## Source and scope

The mathematical source is [CoqQ: Foundational Verification of Quantum Programs, v1](https://arxiv.org/html/2207.11350v1), Definition 6.1, sections 6.1–6.3, the rules R.IF and R.SC, and appendix D. The paper's assertions may be arbitrary linear operators. This delivery deliberately restricts assertions to effects: Hermitian positive operators bounded above by the identity. It restricts programs to one full finite register, skip, unitary transformation, finite measurement with outcome-dependent continuations, and sequencing. It proves soundness for this slice, not the paper's full Theorem 6.1 or its completeness results.

The separately inspected implementation is [CoqQ commit b169ea462b13d20b05e03615ad1d56cc8d8f5784](https://github.com/coq-quantum/CoqQ/tree/b169ea462b13d20b05e03615ad1d56cc8d8f5784). Its [qhl.v](https://github.com/coq-quantum/CoqQ/blob/b169ea462b13d20b05e03615ad1d56cc8d8f5784/src/example/coqq_paper/qhl.v) gives `Ax_UT_G`, `R_IF_G`, and `R_SC_G`; [qwhile.v](https://github.com/coq-quantum/CoqQ/blob/b169ea462b13d20b05e03615ad1d56cc8d8f5784/src/example/coqq_paper/qwhile.v) supplies `fsem_ifE`, `fsem_seqE`, `no_while_qc`, and `global_hoare`. The displayed conditional in the paper uses computational-basis projectors; the pinned implementation admits finite complete measurements. The general Lean rule follows that formulation, and the public computational-basis client specializes the paper's displayed rule. Full-register semantics removes the need for cylindrical extension in this slice.

CoqQ is [MIT licensed](https://github.com/coq-quantum/CoqQ/blob/b169ea462b13d20b05e03615ad1d56cc8d8f5784/LICENSE), copyright CoqQ contributors. These are new matrix-native Lean definitions and proofs of the stated mathematical specialization; no Coq code is copied verbatim. No Coq build or verified translation between proof assistants is claimed. The separately pinned implementation is not asserted to be the original paper artifact. Source SHA-256 values are:

| File | SHA-256 |
| --- | --- |
| Retrieved v1 HTML | `4496c32a238abcbb13d59dfa64562a8199faff749a505f08d0b87fb1e475e325` |
| `qhl.v` | `77c2ee4646af2837e075e8928affed167515b356ed8dc0299cbe1c927f07fed4` |
| `qwhile.v` | `fa56b4504cd9aa88b96d0764f2d406ff9524f93662663cbb4fdf5bff75f0c204` |
| `LICENSE` | `28ce498adb3dddcde08730119c6445cb895d70f439767ef23f9ce62356a8e406` |

## State, program, and observation contracts

[Core.lean](../../Applications/QuantumSemantics/Core.lean) uses Mathlib complex matrices and `Matrix.PosSemidef`. `IsState ρ` requires positivity and `Re(tr ρ) ≤ 1`. Nonnegative real trace and zero imaginary trace follow from positivity. `IsEffect A` requires positivity of both `A` and `I − A`. `expectation_real` proves that taking the real part of `tr(Aρ)` loses no information for Hermitian assertions and states.

A `Gate` supplies both adjoint inverse equations. A `Measurement n k` supplies matrices `M i` and the equation `Σ i, (M i)† * M i = I`. Its outcome state is the unnormalized `M i * ρ * (M i)†`. `branch_state` proves positivity and the trace upper bound for each actual branch by using completeness and nonnegative branch traces. Zero-probability outcomes need no division or special convention. The generic definitions also permit an empty register; all substantive clients use `Fin 2` with explicitly normalized states, so soundness is exercised on a nonempty state space.

[Program.lean](../../Applications/QuantumSemantics/Program.lean) defines `denote` before any assertion judgment. Sequence is composition. Measurement denotes the sum of the continued branch states. `instrument` keeps the outcome index and its unnormalized continued state, while `instrument_probability` proves its trace equals the original outcome weight. `denote_positive`, `denote_trace`, and `denote_state` establish positivity, exact trace preservation, and admission preservation. Complex linearity is proved separately by `denote_add` and `denote_smul`.

These results establish the stated finite density semantics. An arbitrary tensor-ancilla extension theorem establishing complete positivity has not been proved here. Neither a general CPTP interface nor a local frame rule is claimed.

## Assertion rules

[Rules.lean](../../Applications/QuantumSemantics/Rules.lean) defines `Valid A c B` by the inequality `expectation A ρ ≤ expectation B (denote c ρ)` for every admitted state. `PartialValid` retains the source's additional trace-loss term `Re(tr ρ) − Re(tr(denote c ρ))`. The independent trace theorem proves `partial_iff_total` for every program in this terminating, trace-preserving syntax.

| Native theorem | Source rule and proof obligation |
| --- | --- |
| `unitary_sound` | Ax.UT: conjugate the assertion by the adjoint; cyclic trace proves the expectation equation. |
| `measurement_sound` | R.IF: apply each branch premise to its actual admitted unnormalized state, then sum the inequalities. Completeness proves the constructed precondition is an effect. |
| `sequence_sound` | R.SC: apply the second premise to the admitted output of the first command. |
| `pre_sound` | Derive a compositional precondition using these proved rules. |
| `pre_expectation` | Prove exact expectation equality for this finite precondition construction. No full-qwhile weakest-precondition completeness claim follows. |

There are no abort, initialization, while, parallel, or local-frame constructors. No assumptions about their behavior are hidden in the partial/total equivalence.

## Public clients and rejection cases

[Qubit.lean](../../Applications/QuantumSemantics/Qubit.lean) constructs the computational-basis projectors `p0` and `p1`, bit flip `x`, Hadamard matrix, plus state, maximally mixed state, and complete Z measurement. Projector positivity, state normalization, effect bounds, and both unitary equations are checked. Hadamard amplitudes use the exact real square root of one half.

The public `reset` measures Z, skips on outcome zero, and applies X on outcome one. `reset_sound` uses the skip, unitary, and measurement rules to establish `{I} reset {p0}`. Independently, `reset_denote` proves `denote reset ρ = tr(ρ) • p0` for every input matrix. `reset_normalized` specializes to normalized admitted states. Thus the postcondition has both a compositional proof and a direct channel calculation.

`prepareAndReset` applies Hadamard to `p0` before this control flow. `prepareAndReset_sound` uses R.SC; `prepareAndReset_partial` uses the proved partial/total equivalence. `prepareAndReset_output` gives final state `p0`. `feedback_half` gives each recorded outcome weight one half, and `feedback_branch` gives each continued unnormalized branch as one half of `p0`. The classical outcome is retained by `instrument`; it is not a copy of the input quantum state.

`admitted_observation_separator` exhibits admitted plus and mixed states with the same Z outcome distribution and different matrices. The admitted plus-projector effect distinguishes them: expectations are one and one half. This refutes the inference from equality of one chosen measurement distribution to full state equality. It does not prove a universal no-cloning theorem or identify all quantum observational equivalences.

`wrongFeedback_rejected` shows that omitting the X feedback invalidates the reset triple on the admitted `p1` input. `no_single_projector_measurement` rejects the incomplete one-outcome family containing only `p0`. These cases test control and measurement hypotheses rather than relying on a vacuous state predicate.

## Reuse and requirements for interpretation relations

The pinned Mathlib revision is `56a005855ea17e0b0958f73ec801ae140b0a1679`. Its matrix positivity, adjoint, trace, finite-sum, and complex-order lemmas provide the algebra. This work introduces no competing matrix order or inner-product library.

The existing [clean-ancilla core](../../Applications/Uncomputation/Core.lean), [coherent coordinates](../../Applications/Uncomputation/Coordinates.lean), and [Boolean oracle](../../Applications/Uncomputation/Oracle.lean) were inspected against #261/#264. Clean reversible computation alone supplies no density or measurement contract. [Permutations.lean](../../Applications/QuantumSemantics/Permutations.lean) actually reuses the coordinate unitary theorems to construct `permutationGate`; `permutation_composition` transports their composition law to density denotations. The public `bitFlip_coordinates` identifies that existing basis swap with the explicit qubit X gate. General circuit correctness and cleanup still retain their original clean-input/dependency hypotheses.

The quantum comparisons in [the MMT study](mmt-compiler-evidence.md) and [the evidence comparison](compiler-evidence-comparison.md) require observations to be named rather than equating all notions of preservation. This client supplies concrete requirements for #493:

- A realization relation must name its admitted states, operations, and observations. Equality of selected outcome probabilities is weaker than full density equality, as the checked separator demonstrates.
- Measurement witnesses include Kraus operators and completeness; assertion witnesses include positivity and upper bounds. Outcome labels, weights, and unnormalized states are relevant data. Summing outcomes deliberately forgets their labels.
- Composition requires preservation of the intermediate admission predicate and matching observations. The proved sequencing and coordinate-transport laws provide concrete examples; they do not choose a universal interface.
- Composite quantum registers require tensor semantics and appropriate positivity/ancilla theorems. Cartesian copying of unknown quantum states is not supplied by ordinary copying of Lean values or syntax. The selected full-register slice leaves the tensor extension proof open.

Lean's classical metatheory checks these mathematical relations. It does not assign every metatheoretic function to the quantum program language. The definitions contain exact complex numbers and noncomputable real amplitudes; no executable numerical simulator or hardware backend is delivered. Noise, calibration, finite precision, and physical applicability require their own models, empirical evidence, and realization premises. Such relations may compose when their contracts match; there is no mandatory hierarchy of evidence settings or unique final physical layer. This study neither adopts a general evidence framework nor unblocks #489.

## Validation

The focused command `direnv exec . lake build Examples.QuantumSemantics` checks all new library modules and the public positive and separating clients. Exact candidate acceptance additionally requires the repository's full build, exhaustive proof audit, and independent Standards and Spec reviews. Those acceptance records belong to the implementation handoff; the focused check alone is not represented as full acceptance.

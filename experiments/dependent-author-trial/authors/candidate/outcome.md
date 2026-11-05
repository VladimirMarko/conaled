# Candidate submission

Author status: complete submission, pending coordinator acceptance.
Final source: `attempts/Submission.lean`.
SHA256: `83b8e0996d27f7d215d177268d7d098adf6cbb0ec9592c156333475c4c4d5a51`.
Namespace: `DependentAuthorTrial.Candidate` throughout.
The final wrapper check passed and verified public inputs before and after.
Exact checked bytes and diagnostics are in `attempts/checks/Submission/`.

## Coverage

| Required item | Implementation and statement review |
|---|---|
| calibration | `calibration`, preserved first in checked `Attempt01.lean`, calls `Command.comparison`. Its `TypedEquality` contains both operand typings and the substituted/fresh source equation. |
| certificateCommand | `certificateCommand` retains arbitrary n, T, Q, p and supplied hx, hT, hp. Its branch is reflexivity of p substituted along rootTail. `branchTyping` converts the identity family by the symmetric `identitySub` equation. `rootTailTyping` instantiates the admitted rootTail rule. |
| certificate | `certificate` types `selected hx hT hp` at `identity Q p p`. `selectedRecipe` checks its exact J syntax. `selectedRootComparison` derives J computation at the retained root tail. |
| valueTwice, certificateTwice | Both apply source substitution twice, with arbitrary hσ and hτ. The certificate term remains the selected J expression. |
| valueTypeComparison, certificateTypeComparison | Source family equations from `Ty.subComp`, with family typing derived from hp and identity formation. |
| valueComparison, certificateComparison | Source selected-term equations from `Tm.subComp`. `valueComposite` and `certificateComposite` retain the composite operand typings. |
| certificateAligned | Converts `certificateTwice` along `certificateTypeComparison`, retaining its exact term. |
| firstWeakening, witnessVariable, secondWeakening | Derived from hp by identity formation, weakening and generic-variable rules. `secondFamily` is the identity family on the first generic witness. No substitution-typing hypotheses are added. |
| dependentWeakeningCertificate, dependentWeakeningComparison | Apply the generic certificate derivation and comparison to the constructed weakenings. `dependentWeakeningAligned` also applies the generic conversion. |
| valueValidity, certificateValidity | Interpret the twice-substituted source typings in arbitrary full M under validity of Ω. `originalValueValidity` and `originalCertificateValidity` cover the original selected expressions too. |
| certificateTypeValidity | Interprets the source family equation. `certificateComparisonValidity` also interprets the selected certificate equation. |
| extensionSelected | Embedded certificate validity and exact evaluation recovery, quantified over full M, Stable, ρ, and validity of original Ω. `extensionSelectedTwice` covers its twice-substituted expression. |
| extensionValue | Embedded original value validity and exact evaluation recovery. `extensionValueTwice` covers its twice-substituted expression. |
| extensionType | Interprets the embedded dependent family equation and recovers the exact composite family evaluation. |
| extendedCertificate, extendedValidity | `Sigma.retain` embeds the actual certificate derivation into Sigma.theory. `extendedAssumptions` derives validity of embedded Ω from original Ω. `extendedValidity` uses the admitted Sigma interpreter. `extendedCertificateTwice`, `extendedCertificateAligned`, `extendedTwiceValidity`, and `extensionAlignedValidity` retain repeated substitution and conversion through this embedding. |

## Checks and failures

- Attempt01 passed calibration before held-out authoring began.
- Attempt02 failed at elaboration of direct rule instantiation for rootTail.
  Attempt03 introduced a typed rule-instantiation helper and passed.
- Attempt04 failed because opening the parent namespace interfered with
  unqualified source variable declarations, and semantic theorem proofs needed
  explicit inclusion of section premises. Attempt05 qualified the semantic
  namespaces, included premises explicitly, and passed.
- Attempt06 passed with elaborated principal statements printed. It printed
  transitive axioms for every authored def, abbrev, and theorem. All reported
  dependencies were subsets of `propext`, `Classical.choice`, `Quot.sound`.
  No declaration reported `sorryAx` or an added axiom.
- Submission removes only diagnostic commands from Attempt06 and passed.
  The coordinator's exact-byte replay and exhaustive acceptance audit remain
  required. A successful Lean check alone is not claimed as acceptance.

There are no authored sorry/admit placeholders, new axioms, weakened task
assumptions, proof hints, coordinator repairs, or interface changes. Failed
sources and wrapper archives remain preserved.

## Author obligations and interface observations

The author supplied source derivations and one explicit source conversion for
the reflexive branch. The repeated-substitution alignment uses the public
family composition rule and conversion. No family indexed by semantic models,
semantic annotation alignment, or extra coherence law was supplied by the caller.
The semantic conclusions are derived by interpretation from the source judgments.
Stable is an explicit extension capability; its construction and coherence are
model-builder obligations already handled by the frozen library, not new author
proofs here. The proof uses its admitted Capability for the unchanged old terms.

The rootTail rule was public and admitted, but lacked the named authoring wrapper
needed for this construction. A local wrapper required one raw rule instantiation.
The source files exposed enough information to build it; a public named wrapper
or short documented recipe would reduce this discovery and elaboration work.
Opening the parent namespace also caused name resolution trouble in this Lean
encoding. Fully qualified semantic names resolved it. Neither failure supplies
evidence of mathematical impossibility.

The dependent weakening case is a checked application of the generic argument.
It retains a second family depending on the first identity witness. No native-only
model specialization is used to replace the general interpretation. The claims
make no UIP, equality reflection, higher-model adoption, or new Sigma-term claim.
Object-language identity, source judgmental equality, and host equality of semantic
evaluations remain distinct in the statements.

## Exposure, timing, and stopping reason

Only the frozen handoff and its public source closure were read. The initial
repository AGENTS instructions and skill catalog were disclosed to root as prior
conversation exposure. No other arm, private reference, original Git history,
coordinator records, or parent source was inspected. No assistance was requested.

Exact stopping reason: all requested declarations and associated checks have
been submitted; coordinator replay, statement review, and independent audit are
pending. There was no resource failure or external interruption. Wrapper
measurements are recorded in session-metadata.md; full author-session timing and
serving-model/usage telemetry unavailable to this author remain unknown.

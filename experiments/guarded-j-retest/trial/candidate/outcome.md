# Guarded candidate submission

Completed the calibration and held-out contract in `Submission.lean`, namespace `GuardedJRetest.Candidate`. The final wrapper returned exit 0 and verified frozen inputs before and after checking. Exact source, command, diagnostics, hashes and times are under `checks/Submission/`. Coordinator replay, statement review and exhaustive audit remain pending.

## Obligation map

| Obligation | Declarations and evidence |
|---|---|
| Calibration, selected inner J and full type | `calibration`, `inner`, `calibrationRecipe`, `calibrationBranch`; checked first in Attempt01 |
| Two-premise root-tail map | `rootMap`, uses `hx.rootTail hT` |
| Outer selected J, full source type, recipe | `outer`, `outerTyping`, `selectedRecipe` |
| Typed root computation | `rootLeft`, `rootRight`, `rootBeta`; branch conversion comes from `Command.reflexivity` and `Tm.reflexivitySub` |
| Arbitrary dependent substitution | `substitutedLeft`, `substitutedRight`, `substitutedBeta`; `selectedLeft`, `selectedRight`, `selectedFamily`, `comparison` retain the precise twice-substituted family |
| Constructed weakening | `dependentWeakening` derives Ty.weaken from the family of inner[r]; its domain extends the root-tail total by `(Id_Q(p,p))[r]` |
| Application at that weakening | `workedLeft`, `workedRight`, `workedBeta`, `workedComparison` |
| Arbitrary full-model semantic agreement and typing | `comparisonSound`, under satisfied Ω |
| Embedded source assumptions, typing, equation | `extensionAssumptions`, `extensionLeft`, `extensionRight`, `extensionBeta` |
| Stable Sigma reuse and selected data | `extensionSelected`: both embedded semantic typing judgments, equality of operands, exact selected left evaluation, exact family evaluation, exact old-model reduct |

`selectedRecipe` and `calibrationRecipe` are host equalities of the chosen source syntax. `rootBeta` and `substitutedBeta` are source judgmental equations. Object identity occurs in the motives. Semantic equality is obtained only by soundness of the source equation and accompanies typing judgments for both operands. No semantic comparison or alignment is a premise.

`substitutedBeta` uses source congruence, which itself does not require a valid σ. Both operand typing declarations and `comparison` require valid σ; the semantic theorems retain that requirement explicitly. The source family stays twice-substituted, so no further composition conversion is needed. The identity-family conversion needed for each branch is supplied by the frozen interface.

## Checks and failures

Attempt01 passed calibration. Attempt02 failed on congruence signature inference; Attempt03 passed with explicit theory and operation. Attempt04 failed after an overbroad namespace open; Attempt05 fixed that but exposed omitted theorem parameter hσ. Attempt06 fixed the parameter inclusion and passed. Attempt07 added the worked comparison and passed. Attempt08 checked the elaborated required types and printed the axiom dependencies of every authored declaration. Submission is exactly Attempt07 and passed separately. Every attempted revision remains intact.

All 29 authored declarations printed only `propext`, `Classical.choice`, and `Quot.sound` in their axiom closure. No admissions, new axioms, UIP, equality reflection, desired-output premises or new model laws were introduced. This local audit is additional evidence, not a replacement for coordinator exhaustive audit.

## Burdens and exposure

Source mathematics uses two selected J eliminations, J beta, dependent substitution, identity formation and reflexivity, and weakening. Root-tail raw-rule work was zero in this author file: the admitted two-premise interface supplies it. The conversion of reflexivity to the substituted identity family also needs no raw rule instantiation here. One source congruence derivation was authored for substitution of the root equation.

The model builder must supply the existing full PathTransport.Typed.Model and, for extension reuse, Sigma.Stable on its structural reduct. The author introduced no coherence obligation. The extension uses the capability underlying Stable; stability is retained as the requested boundary.

Host and interface work consisted of source-expression indices, a Fin.cases congruence proof, qualification of colliding namespace names, explicit theorem inclusion of hσ, syntax embedding through Atom.inl/Term.inl, and assembly of semantic conjunctions. The weakening retains p in its identity endpoints and is derived from inner[r], not assumed. Documentation did not supply a standalone root-computation comparison helper; its components were discoverable in Authoring and GuardedTheory. The missing handoff README was reported without reading outside the handoff.

Prior familiarity was limited to general repository instructions and this assignment. The task disclosed prior calibration solutions and public nested-J examples; no prior solution or separate nested-J example was inspected. Reading the public Command.reflexivity implementation and finishing calibration informed the held-out construction. This is fixed-order exposure, not an independent first-exposure result. No parent checkout, other arm, private reference, history or outside project path was inspected. No subagents or proof assistance were used. The coordinator received only the exposure/missing-README report during authoring.

Exact stopping reason: completed submission and local statement/axiom checks. No mathematical obstruction, resource failure or external interruption occurred. No authored obligation remains open; acceptance is for the coordinator's independent checks. This one-author result establishes neither causal productivity nor general human usability.

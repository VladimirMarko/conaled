# Homotopy canonicity and proof-producing extraction

Assessment for [#396](https://github.com/VladimirMarko/conaled/issues/396).
**Keep canonical-value recovery with an object-language witness as a separate
consumer contract. Defer a general HoTT extractor.** Bocquet supplies a
constructive mathematical existence result for a specified syntax; applying
it here requires a syntax correspondence and a realization of its metatheory.
Neither our denotations nor the existing machine canonicity bridge supplies
that correspondence.

## The theorem being considered

The inspected source is Rafaël Bocquet,
[*Strict Rezk completions of models of HoTT and homotopy canonicity*,
2311.05849v2, 8 October 2025](https://arxiv.org/pdf/2311.05849v2).
Section 4 specifies an omega-indexed cumulative universe hierarchy, with every
type classified, Π with function extensionality, Σ, intensional Id, unit, empty,
Booleans and W-types, and univalence. Theorem 6.1 (66 in the HTML rendering) gives, for closed Boolean `b`
in the **initial model**, an element of the external coproduct

```text
Tm(1, Id_B(b, true)) + Tm(1, Id_B(b, false)).
```

This is a selected branch with a closed syntactic identity witness. It does
not say that `b` reduces to that constructor. Section 6 obtains the witness by
sconing over a strict Rezk completion, then lifting back along its external
split weak equivalence. The original object syntax is unchanged. Arbitrary
HIT extensions, extra equations, and arbitrary models are outside this theorem.
The W-type assumption does not license replacing the stated Boolean theorem
with every desired data-type theorem without another argument.

The constructive proof works internally to Cartesian cubical presheaves, using
the interval/cofibration, fibrancy, universe and extension constructions in
sections 2–6. Diagonal cofibrations matter. The supplementary Agda work covers
part of the path/reflexive-loop model construction, not the whole extraction
claim. See the [completion assessment](strict-rezk-completion-assessment.md)
for the precise model prerequisites.

## What executable content would have to mean

A constructive coproduct witness carries more information than an unselected
classical disjunction. Nevertheless, this paper is not a Lean executable
implementation or a proved cost bound. A Lean transcription into
`∃ v, Nonempty (Witness b v)` in `Prop` would also not be an executable
producer. A proposed executable interface must retain the branch and witness
syntax in `Type`, supply an algorithm producing them, and prove its acceptance
and termination claims. Choosing a witness with `Classical.choice` may prove
existence but cannot discharge that executable contract.

For a new implementation, the initial generalized algebraic syntax, its
substitution and equality quotient, cubical presheaf constructions and size
levels would need explicit encodings. The proof's internal reasoning must be
interpreted in that constructed metatheory. It cannot be installed as new Lean
host axioms under the repository's proof audit. A complete translation from an
input calculus must preserve all admitted rules and return a witness **in the
input syntax**, or explicitly advertise a witness only in the translated
calculus. Forward semantic soundness alone does not provide this return route.
These are missing construction obligations, not evidence of impossibility.

## A consumer and a separating example

The proposed consumer is a proof-carrying constant specialization pass. Given a
closed Boolean source expression `b`, it would return a Boolean `v` and source
term `p : Id_B(b, literal v)`. A target compiler may emit `literal v`; the input
program remains unchanged, and its original evaluator need not acquire a new
reduction. The contract is schematic, not a current Lean API:

```text
recover(b : ClosedSourceBool) : (v : Bool) × SourceIdentityWitness(b, literal v)
interpretWitness(p) : Id_M(interpret b, interpret (literal v))
observe(interpret b) = v
```

The last line needs a model-specific observation map sending interpreted
Boolean constructors to their bits and respecting the interpreted identity.
It does not follow for an arbitrary observation merely from witness typing.
Compiling dependent consumers additionally requires transporting their results
along the selected witness. Erasing it is sound only for observations proved
insensitive to that choice. Compiler correctness and source evaluation
adequacy remain separate contracts.

A proposed discriminator is axiomatic-HoTT
`transport (ua notEquiv) true`: the ordinary Id eliminator has no reduction
rule for an opaque `ua` path, although a propositional transport law can connect
it to `false`. Establishing that **specific** witness requires the equivalence
and transport law; Theorem 6.1 by itself chooses a branch without identifying
which branch this example has. A compiler with the value-plus-witness contract
could emit `false` without claiming that the original evaluator reduces the
term. This is an external-calculus example, not a checked conaled program.

## Local evidence and the failed applicability test

Source inspection used conaled
`78540f8f30ed8cb1afa7dc799a96dac65fec1458`.

| Existing component | Reuse and limit |
|---|---|
| [Reference calculus](../../SquareKit/Internal/DependentJudgments/ReferenceCalculus.lean) and [soundness](../../SquareKit/Internal/DependentJudgments/ReferenceSoundness.lean) | `Derives` retains derivation data, and `sound` interprets it under validated declarations. No initial syntax for Bocquet's full HoTT, Boolean extractor or reverse source translation is supplied by these declarations. |
| [Derived path recipes](../../SquareKit/Internal/DependentJudgments/ReferencePath.lean) | Typed endpoints and object identity can remain explicit. A host equality between decoded expressions cannot replace an object identity witness. |
| [#410 canonicity](structural-canonicity-controls.md) | `embedded_returns` and optional `NoOmega` establish actual finite machine reduction and uniqueness in their ground/arrow fragment. Reuse that bridge for its clients; another value-existence wrapper would add no capability. |
| [Opaque control](../../SquareKit/WeakMachine/OpaqueControl.lean) | `kappa_meaning`, `kappa_no_step`, `demanded_stuck` and `ignored_returns` already distinguish semantic value, demanded stuck computation and unforced occurrence. They do not assert homotopy canonicity. |
| [Cubical construction](cubical-model-construction.md) | The universe-free interpretation cannot supply the full classified HoTT model required here. |

The applicability test fails at the source/model boundary: there is no
constructed correspondence from our reference calculus to the stated initial
HoTT syntax and back to its identity witnesses. Even building a Boolean-valued
denotation would leave that failure intact.

## Disposition

Under [#36](https://github.com/VladimirMarko/conaled/issues/36), retain the
value-plus-witness consumer specification above; do not schedule a wholesale
Bocquet port merely to reprove #410. Reconsider extraction when a concrete
univalent source importer or proof-carrying specialization client needs the
witness that the current reference derivations cannot produce. That follow-up
must choose its exact source, construct the syntax correspondence, retain
witness data, and compare emitted evaluation with unchanged source evaluation.
[#200](https://github.com/VladimirMarko/conaled/issues/200) owns the observation
and translation contract; #397 owns the completion applicability question.
No additional implementation ticket is justified before that consumer is
selected. Partial and lazy settings remain eligible: normalization is an
optional guarantee for admitted computations, not a requirement on all
specifications or all syntactic occurrences of an opaque term.

This is source research and a proposed contract. No new Lean theorem,
extraction algorithm, runtime measurement or source build is claimed.

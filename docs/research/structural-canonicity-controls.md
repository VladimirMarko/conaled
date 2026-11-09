# Structural admission and demand-sensitive canonicity controls

[#410](https://github.com/VladimirMarko/conaled/issues/410) implements the bounded
successor to [the canonicity assessment](executable-canonicity-obligations.md).
Closed ground terms admitted by `NoOmega` return a unique numeral under the
existing call-by-value machine. An unforced partial function can also return
without satisfying this admission policy. A separate typed opaque-constant
control shows why supplying a semantic meaning does not supply execution.

## Reused proof and public guarantee

[`Canonicity.lean`](../../SquareKit/WeakMachine/Canonicity.lean) defines
`NoOmega` structurally on the existing weak terms. Variables and literals are
admitted, application requires both operands admitted, a lambda requires its
body admitted, and omega is rejected. This is an optional sufficient interface.
The partial source syntax, evaluator, progress theorem and divergence proofs
remain available.

`embed_admitted`, `back`, `embed_back` and `admitted_iff_image` identify the
admitted terms with the image of the existing total syntax. The back-translation
chooses `false` for every literal presentation tag. Coverage is
`embed (back t h) = t`; it does not recover a discarded `true` tag. The examples
check both equal embeddings and unequal total presentations.

`NoOmega.rename`, `AdmittedSub.lift`, `NoOmega.subst`, `NoOmega.beta`,
`NoOmega.step` and `NoOmega.steps` establish closure under renaming, admitted
substitution including binders, and the selected machine's reductions.
`embed_rename` and `embed_subst` give the corresponding syntax bridges.

`embedded_returns` places the existing `Examples.WeakMachine.recovered`
argument in the public machine module. The old theorem retains its statement
and delegates to it. Its proof still composes `recovery_meaning` with
`return_denotation`, using the existing `TotalRel`/`TotalEnv` recovery; no second
logical relation or normalization argument is introduced. `admitted_returns`
applies this theorem to `back` and rewrites by coverage.

For every `t : Term [] ground` and `h : NoOmega t`, `canonicity` establishes:

- a numeral `n` and a finite source reduction `Steps t (lit n)`;
- every returned numeral equals `n`, by the existing `terminal_unique`;
- a bound such that every fuel at least that bound executes to `lit n`, by
  the existing `execute_sufficient`.

The bound exists in `Prop`. This API does not extract a computable fuel bound,
identify machine transitions with the total interpreter's beta count, or prove
strong normalization for every reduction strategy. Ground closedness and the
selected left-to-right weak call-by-value strategy are explicit hypotheses.

## Checked demand controls

[`WeakCanonicity.lean`](../../Examples/WeakCanonicity.lean) connects duplicated
function use to the public admission theorem. The expression
`(λf. f (f 7)) (λx. x)` returns 7 in three source steps; two steps time out.
A literal is already terminal with zero fuel. Timeout remains inconclusive.

The expression `(λf. 0) (λx. omega)` returns zero in one step but fails
`NoOmega`, since the predicate inspects the unforced body. In contrast, the
existing `(λx. 0) omega` has an infinite execution because call-by-value demands
its argument. These are weak lambda controls, not a lazy-pair or call-by-need
implementation. Structural occurrence and operational demand are different.

[`OpaqueControl.lean`](../../SquareKit/WeakMachine/OpaqueControl.lean) is a
separate opt-in test language with the same ground/arrow types and a ground
constant `kappa`. Its ordinary function interpretation assigns `kappa` zero;
`denote_rename`, `denote_subst` and `denote_beta` validate the binding equations.
Values are still only literals and lambdas. There is no operational rule for
`kappa`. The checked results distinguish these cases:

| Expression | Operational observation | Admission evidence |
| --- | --- | --- |
| Literal `n` | Already a value | `literal_admitted` |
| `kappa` | No step and not a value | `kappa_not_admitted` for every numeral |
| `(λx. 0) kappa` | Stuck despite denoting zero | `demanded_not_admitted` |
| `(λf. 0) (λx. kappa)` | Returns zero in one beta step | `ignored_admitted` |

`ExecutablePrimitive t n` requires both semantic agreement with `n` and an
actual finite reduction to `lit n`. It is a checked proof obligation for an
executable ground realization, not a decision procedure for termination or a
registry of all possible primitive types. Assigning a meaning to `kappa` cannot
construct this evidence. A future realization must supply operational rules and
prove the return obligation, or exclude the primitive from that executable
interface. The ignored-expression example prevents confusing this policy with
a ban on every syntactic occurrence of opaque data.

The control evaluator checks values separately from the absence of a step,
then reports terminal, stuck or timeout. In particular it cannot perform beta
reduction on an opaque argument merely because that argument has no next step.
Its `step_next` connects the independent reduction rules to the evaluator's
single step; the named return controls carry explicit finite derivations.
This bounded counterexample does not claim a complete adequacy or canonicity
framework for arbitrary future extensions. The original machine's `no_stuck`
is unchanged and is not asserted for this control language.

## Validation and remaining boundaries

The examples exercise the public coverage/return theorem, conservative rejection,
tag loss and admitted substitution. The executable controls are in
[`WeakCanonicityTest.lean`](../../scripts/WeakCanonicityTest.lean); the existing
[`WeakMachineTest.lean`](../../scripts/WeakMachineTest.lean) remains a compatibility
check. Integrated compilation and the exhaustive proof audit cover the new
modules through `SquareApplications`.

No whole-library totality policy, host axiom, cubical canonicity transfer, general
decidable equality claim, or lazy-pair implementation follows. Value-plus-identity
extraction under [#396](https://github.com/VladimirMarko/conaled/issues/396) and
open normalization under [#398](https://github.com/VladimirMarko/conaled/issues/398)
retain their distinct scopes. This result supplies a public optional interface
for an already supported total fragment and checks the demand boundary that its
structural admission deliberately overapproximates.

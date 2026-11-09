# Computation and equality across interpretation routes

Research for [#394](https://github.com/VladimirMarko/conaled/issues/394).
Inspected on 2026-11-09 at `78540f8f30ed8cb1afa7dc799a96dac65fec1458`.
This is a source audit and proposed contract discipline, not a new Lean proof
or a rerun of the integrated build.

Keep each route's declared equality and execution observation explicit. The
[algebra/program-specification assessment](algebra-and-program-specification.md)
established why this matters; this report adds a composition criterion and an
existing counterexample that rejects an invalid composition.

## Five different obligations

| Contract | Required evidence | What it does not establish |
| --- | --- | --- |
| Source conversion | A derivation `Γ ⊢ t ≡ u : A` in a named calculus | A step of a selected evaluator; conversion can include eta and symmetry |
| Identity | A term `p : Id A t u` with its interpretation | Judgmental conversion or an executable reduction |
| Semantic preservation | `decode (translate t) = denote t`, or a specified relation | Faithfulness, reflection, or termination |
| Evaluation preservation | Simulation of source steps/returns by target steps/returns | Open-term normalization or equal costs |
| Host equality | Lean `Eq`/`HEq` between represented objects | A new source conversion rule or a relevant higher path |

**Literature.** Licata's [2011 account](https://homotopytypetheory.org/2011/07/27/canonicity-for-2-dimensional-type-theory/)
explains why transport through an axiomatic univalence term is stuck under
traditional reflexivity-only reduction. Its proposed computational replacement
is a particular two-dimensional theory. It is not an evaluation theorem for
arbitrary HoTT or Lean. [CCHM, arXiv 1611.02108v1](https://arxiv.org/abs/1611.02108v1)
constructs univalence in a cubical calculus; transferring that result requires
that calculus's operations and rules. Neither citation turns an arbitrary
semantic equality into a reduction rule.

## Current declarations and their boundaries

| Local source | Audited declaration | Actual claim |
| --- | --- | --- |
| [Compiler](../../Compiler.lean) | `compile_sound` | Chosen target denotation equals source evaluation, assuming `Sound` for the supplied target operations |
| [ContextualModel](../../SquareKit/Internal/PathTransport/ContextualModel.lean) | `Model.j_beta`, `Model.j_sub` | Required heterogeneous equalities for contextual J under root and substitution, with the full telescope/motive/branch data |
| [ContextualOperations](../../SquareKit/Internal/DependentJudgments/ContextualOperations.lean) | `jBeta_valid`, `jSub_valid` | Generated equations are valid in that algebra by the model laws; these are semantic rule-validity proofs |
| [Cubical source semantics](../../SquareKit/Internal/Cubical/Judgments/Semantics.lean) | `subTy_comp`, `subTm_comp`, `variable_pair` | Presheaf substitution equalities, including host `HEq`; no evaluator is defined here |
| [Measured stack](../../Applications/Stack/Measured.lean) | `runMeasured_value`, `runMeasured_append`, `padding_changes_cost` | Instrumented execution erases to `run`, composes, and can change cost while preserving output |
| [Canonicity](../../SquareKit/WeakMachine/Canonicity.lean) | `canonicity` | Closed admitted ground terms return uniquely with sufficient fuel under the weak call-by-value machine |

The last two rows are completed #409/#410, not missing work. J validity and
cubical substitution give useful interpretation contracts without claiming
canonicity or open normalization. The admission predicate in #410 is sufficient,
not necessary for returning: it rejects an unforced divergent function body.

## Counterexample: proof of agreement without a reduction

**Checked local control.** In
[OpaqueControl](../../SquareKit/WeakMachine/OpaqueControl.lean), `kappa_meaning`
is a Lean equality proof that `denote kappa empty = 0`. Yet `kappa_no_step` and
`kappa_not_value` show that the specified evaluator cannot produce a numeral;
`kappa_not_admitted` rejects every `ExecutablePrimitive kappa n` certificate.
`demanded` is `(λx. 0) kappa`: its semantic meaning is zero but it is stuck
under the explicitly selected call-by-value rules. `ignored` places `kappa`
inside an unforced lambda and does return. This is about demand, not occurrence.

Here the proof is host propositional equality of denotations. The control has
no object-language identity constructor, so calling it an internal path proof
would overstate it. A separate **paper countermodel** gives that stronger
separation: extend a simply typed ground calculus by a constant `κ : Nat` and
an identity witness `q : Id Nat κ 0`, with no rule reducing κ. Interpret both
endpoints as zero and q as reflexivity in a set model. Identity introduction
by this declared constant is semantically consistent with that model, while
the selected evaluator remains stuck. This is an illustrative source theory,
not an axiom added to Lean, and no canonicity theorem is assumed for it.

## Composition test and affected callers

**Proposed contract.** For translations F : S → T and G : T → U, compose
conversion preservation only if F maps S conversions into the *same T
conversion judgment* that G preserves. Compose path preservation by mapping
witnesses and their endpoints, retaining substitution and transport. If F
returns only equality of denotations, G cannot consume it as T conversion
unless a separate reflection theorem supplies that implication.

For execution use a relation R between configurations, with matching initial
states, simulation of each source step by finitely many target steps, and a
terminal clause mapping each source value to an observable target value.
Existential relational composition then gives the combined relation. This
suffices for finite-return preservation. Infinite execution needs a separate
progress condition to exclude endless zero-step simulation; cost bounds need
bounds on the simulating paths. No such stronger clause follows from squares.

The countermodel rules out the tempting chain “S denotes zero; T's literal
zero returns; therefore S returns.” The absent edge is source-to-target
execution adequacy. A compiler emitting a literal for κ can preserve denotation
while repairing stuckness; that does not reflect source termination.

Affected callers are `compile_sound` clients requesting execution, contextual
J clients requesting source conversion, and cubical source clients requesting
normalization. Existing value-only clients retain their direct APIs. Existing
`ModelMap` [interpretation maps](../../SquareKit/Internal/PathTransport/InterpretationMaps.lean)
already handle dependent semantic comparisons; they should not be replaced
by a universal record of these unrelated guarantees.

## Adoption and bounded successor

Adopt the table as a review discipline under #235. Defer a standalone
composition abstraction until a real two-stage executable caller needs it.
The scoped successor specification is to prove a
finite-return composition lemma for two concrete weak-machine translations,
then apply it to the existing total embedding and a literal-preserving second
translation. Include the opaque control as a negative reflection test, and
check substitution/binder compatibility at both stages. Reuse #410's recovery
and return theorem; do not reprove canonicity or add an evaluator to the
cubical model merely to fill a table cell. Acceptance must preserve old direct
clients and separate source conversion, host equality and returns in named
statements. Open normalization belongs to #398; equality reflection to #401.

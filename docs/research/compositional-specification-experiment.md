# Compositional specification experiment

Issue [#339](https://github.com/VladimirMarko/conaled/issues/339) adds a bounded
proof-transport construction over the existing guarded rule language. Local
certificates that interpret primitive rules now transport complete derivations.
The experiment uses the existing primitive and strong dependent-pair providers;
it does not change the squares interface or claim a translation between
arbitrary object logics.

## What changed

[GuardedRuleInterpretation](../../SquareKit/GuardedRuleInterpretation.lean)
defines `RuleInterpretation T U`: every primitive rule of T has a selected
U-derivation from its listed premises. The interpretation may expand one rule
into several proof steps. `transport` substitutes those certificates and cuts
in the proofs of instantiated premises. It handles the complete existing
`Derivation` grammar, including equality congruence and predicate conversion.
`ofRuleMap` specializes the interface to literal rule inclusion.

`compose` transports the local certificates of the first interpretation through
the second. `reduct` turns a target model into a source model using soundness
of these certificates. The algebra, valuation, and operation values are
unchanged. `satisfaction`, `reduct_identity`, and `reduct_compose` establish the
corresponding satisfaction condition and exact model identity/composition.
They do not assert equality of the resulting derivation trees. The substitution
entry point retains the exact substituted assumptions and conclusion.

This construction is noncomputable. In the existing derivation interface,
hypothesis occurrences are certified by propositional list membership.
Instantiation can identify several premises, and transport uses classical
choice to select a supplying proof occurrence. The result is a Lean-checked
proof transformation, not an executable compiler. Making occurrence selection
executable would require suitable decidability or explicit premise indices;
that is not required for this experiment. Choice of such proof occurrences
does not change the object-language terms named in the judgment.

The existing `PrimitiveSigma.Reindexing.retain` now uses the generic transport
instead of its own induction over derivations. Its public statement and exact
source expressions are unchanged. Primitive pair syntax also gains the raw
constructor-substitution lemmas needed by the client, following the existing
strong pair syntax API.

## Specifications and the shared argument

[PrimitiveSigma.Specification](../../SquareKit/Internal/DependentJudgments/PrimitiveSigma/Specification.lean)
uses three contracts over the same operation/predicate signature:

1. The existing primitive pair theory, with dependent elimination and beta.
2. The existing stable primitive pair theory, adding substitution laws.
3. That stable theory plus the explicitly named elimination-eta rule.

The new third contract is specified by a source rule, independently of a model.
Its model validation is derived from the existing strong pair capability; the
model builder does not supply the final source-rule conclusion. The primitive
and stable contracts remain independently usable.

The shared argument applies dependent elimination beta under a well-typed
context substitution. Its motive can depend on the whole pair; its second
component can depend on the first. This is derived from beta and congruence,
not installed as a primitive axiom of the implementation theory.
`clientTheory` publishes this consequence as a small client requirement.
`clientView` supplies its implementation by the derived proof, demonstrating
rule expansion beyond literal inclusion. The complete client proof then
passes through the primitive, stable, and eta-strengthened contracts.

`no_reverse_view` rules out an interpretation from the eta-strengthened theory
back to the stable primitive theory that fixes this syntax. Such a view would
transport the eta argument to a derivation already excluded by the checked
constant-family separator. This is not a claim about translations that change
syntax, meanings, or the equality judgment.

The separator is a model with an extra Boolean coordinate and admitted
flag-observing sections. It is not evidence that an implementation must expose
an ignored representation flag. Changing which observations belong to the
specification changes the relevant contract. Its restricted admitted families
are documented in [primitive-dependent-sums](primitive-dependent-sums.md).

## Checked use and statement review

[CompositionalSpecifications](../../Examples/CompositionalSpecifications.lean)
uses the existing native dependent family and selected bounded-index branch.
The second component has type `Fin (n + 1)`. A context substitution selects
index n in a fiber bounded by n + 2. The translated source proof yields the
exact interpreted section. At context value 3 it retains index 3, and the
example rejects replacement with index 0. Decoding the transported source
result and substituting again along doubling returns index 6 in `Fin 8`.
Thus the selected witness test depends on the source proof transported through
the new generic interface, not just on an unrelated native calculation.

The existing `Examples.PrimitiveDependentSums` remains imported. It exercises
strong-to-primitive recovery of the chosen unpacking operation, arbitrary
nonconstant dependent families, noncommuting substitutions, and the separating
model's internal eta witness. These are retained applications of the existing
capabilities, not newly claimed results of this transport layer.

Statement review found the following boundaries:

- `cut` replaces assumptions by proofs with the identical conclusion. It does
  not erase object terms or introduce a semantic assertion as an axiom.
- Rule certificates quantify over every source axiom and its finite parameter
  context. `transport` handles arbitrary outer assumptions and substitutions.
  Certificates are local rule proofs, not the final client theorem as a field.
- Equality atoms still use the existing guarded theory's host-equality
  semantics. Object identity operations remain separate. This experiment does
  not supply a generic equivalence-valued replacement for that judgment.
- The typed substitution premise records the intended dependent client domain.
  The equality-congruence proof itself also works on raw operands; that is a
  property of the ambient engine, not a proof of an ordinary typed-calculus
  reflection theorem.
- Model reduction keeps the entire selected algebra. Identity and composition
  laws concern models and judgment preservation. No law identifying the raw
  transported proof trees has been established.
- Strong-model existence is exercised by the native family provider. Failure
  of a reverse view uses the existing semantic countermodel, not failed proof
  search. The negative statement is restricted to a view fixing the signature.

The initial missing connection was generic substitution of rule derivations:
existing inclusions used separate inductions. The concrete client also exposed
missing primitive-constructor source-substitution equations, already present
for the strong sibling. Both were addressed without changing the independently
specified expected selected-index computation.

## Decisions, cost and residual work

Adopt the local rule-certificate interface for same-signature theory maps and
reuse it for existing inclusion proofs when needed. Keep primitive and strong
pair specifications separate and connected by their checked adapters. Keep
proof-relevant language semantics unchanged: the experiment neither replaces
`Lang = A* → Type` by recognition nor changes its witness-preservation contract.

Investigate a change-of-logic interface and a useful combined satisfaction and
computation square under [#340](https://github.com/VladimirMarko/conaled/issues/340),
within #290/#235. Here the sentence translation is identity and the semantic
reduct retains the algebra, so the satisfaction square is exact but limited.
It does not establish a general institution interface, change of object logic,
or a new combined square interface. Do not infer those capabilities from the
composition of rule interpretations.

Defer a universal calculus, global equality abstraction, and executable proof
translator until a consumer supplies their requirements. Retain the possibility
of replacing the underlying representation if a competing framework removes
more author obligations while preserving the required distinctions.

Implementation work includes the generic induction/cut construction, source
substitution lemmas, specification maps, and validation of the stronger rule.
Model construction reuses the existing native and separator providers. Repeated
client work consists of one source proof, selecting a composed interpretation,
and discharging its typed assumptions. No controlled comparison of agent
productivity was performed; these observations separate costs but do not
measure an advantage. Agent productivity remains sufficient for the MVP.

Focused validation: `direnv exec . lake build Examples.CompositionalSpecifications`
passed, including retained primitive-pair examples. The parent implementation
loop owns isolated-candidate full build, exhaustive proof audit, independent
Standards/Spec review, and the final accepted commit record.

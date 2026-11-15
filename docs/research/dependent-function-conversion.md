# Optional conversion for open dependent functions

Issue #423 adds an optional decision procedure for the existing generated
`DepEq` and `FuncEq` relations. It does not change their rules or the source
grammar. Engine correctness and an author productivity result are different
obligations: the independent author trial remains unstarted and mandatory for
completion of the full issue.

## Contract and algorithm choice

The inputs are existing context-indexed `Dep` and `Func` terms. Base expressions
remain literal variables, zero and unary negation. Function domains are base
objects; function bodies return dependent terms. Arbitrary higher-order function
domains, arbitrary Pi types, cubical rules, semantic reflection and hole solving
are not admitted. Variable identity includes its full context path.

A dependent normal form is a dependent variable, point, or a free function
variable applied to a base expression. The variable and application constructors are the neutral cases; no separate
general neutral-language framework is needed here. A function normal form is its eta-long
body under one fresh base binder. Thus the neutral head and its argument remain
visible, including free function variables. The source embedding inserts the
lambda explicitly. No semantic equation such as double-negation cancellation is
added to base expressions.

Two algorithms were considered before implementation:

| Obligation | Structural eta-long normalization | Typed normalization by evaluation |
| --- | --- | --- |
| Open terms | Keep context-indexed variable heads directly | Reflect variables into a semantic neutral environment |
| Beta | Plug a base expression into a normal body | Apply semantic functions and reify |
| Termination | Recurse only on source subterms; base plugging does not insert function terms | Establish evaluator/reifier termination for the semantic domain |
| Substitution | Prove normal substitution commutes with source substitution | Prove environment substitution and reification naturality |
| Scope | Fits the existing base-domain grammar | Adds a semantic layer without admitting another source construct |

The structural implementation was selected for this bounded grammar. This is a
design comparison, not a benchmark or a claim to have implemented both routes.
If the grammar later admits higher-order domains, this argument must be
revisited. No general normalization framework is adopted.

## Checked claims and owners

The source grammar, typing, equality and interpretation remain owned by the
existing `DependentFunctions`, `DependentFunctionTyping`,
`DependentFunctionEquality` and SheafSem modules.

- [NormalForms](../../SquareKit/Internal/DependentFunctionNormalForms.lean)
  defines canonical data, embeddings, variable-preserving maps and base plugging.
- [NormalFormLaws](../../SquareKit/Internal/DependentFunctionNormalFormLaws.lean)
  proves map identity/composition, embedding compatibility and binder/plug laws.
- [Normalization](../../SquareKit/Internal/DependentFunctionNormalization.lean)
  defines total mutual structural normalization. `normal_sound` constructs the
  existing equality derivation from each source term to its canonical embedding;
  `normal_type` preserves the inferred index. `normal_map` commutes with the
  existing variable-preserving action, which itself may substitute base syntax.
- [NormalizationSubstitution](../../SquareKit/Internal/DependentFunctionNormalizationSubstitution.lean)
  defines substitution on normals and proves `normal_sub`. This theorem holds
  even for raw source substitutions; callers who need preserved typing still
  supply the existing `Sub.Typed` evidence. It does not claim an untyped source
  equality rule.
- [Conversion](../../SquareKit/Internal/DependentFunctionConversion.lean)
  proves equality of normals for **every** constructor of the existing mutual
  relation: reflexivity, symmetry, transitivity, application/lambda, beta/eta,
  and typed substitution. `convertible_iff` proves both directions. The executable
  `decideEq` returns either an existing derivation or its negation.

These are separate obligations: termination follows from Lean's accepted total
recursive definitions; soundness constructs derivations; completeness is an
induction on the full existing relation. No uniqueness, reflection or conversion
premise is assumed. General substitution re-normalizes free-head replacements
that create beta redexes. Binder plugging, weakening and eta cancellation are
proved algebraically rather than justified only by closed examples.

`Dep.check` and `Func.check` are optional author services. The caller supplies
both scoped terms and a common explicit expected index. They check the left
index, then the right index, then conversion. Diagnostics distinguish those
three failures. On success a `PLift` packages the existing equality proof in a
computational result; it is not a new equality relation or trusted certificate.
`check_success` characterizes success exactly by both expected-index equalities
and the existing source relation. The low-level decider remains available when inferred-index checking is not the
requested interface. Native helper derivations remain ordinary public callers.

## Consumers and limitations

The [development examples](../../Examples/DependentFunctionConversion.lean)
retain a generated beta expression with a function parameter, a genuine bound
result index and a nonconstant open argument. They apply two nonidentity typed
substitutions, retain direct beta/eta helper proofs and connect the optional
converter to a typed dependent output. The nested-function case eta-expands twice,
introduces a beta redex under the binder, and then substitutes twice. A repair
changes a constant assignment to a second free base variable in an enlarged
context: the old index is rejected, the new family index is supplied, and the
typed substituted equation is recovered. Bound index zero remains bound while
free indices shift through weakening. Negative controls change the surviving
index and change a free function while keeping its type identical. These are
development fixtures, not sealed author-trial tasks.

The [interpretation examples](../../Examples/DependentFunctionConversionSemantics.lean)
consume the produced derivation through existing SheafSem and ordinary dependent
function application. The changed-head control has a separate finite-model
observation: the two legal free functions return different Boolean fibers.
No converse from semantic equality to generated source equality is asserted.

The [runtime driver](../../scripts/DependentFunctionConversionTest.lean) observes
twelve public service outcomes and exact diagnostics, including the genuine
free-dependency repair and rejection of its obsolete constant annotation. Kernel
proofs and runtime observations serve different roles. Native computations are
not used as trusted proof certificates.

## Acceptance and author trial

Focused compilation of all seven new library/example modules has passed,
including the interpretation and separating-model fixtures. The runtime driver
passed all twelve public-service fixtures. Detailed commands and retained
attempts are in the coordinator handoff.
The finite separating model uses a local 800,000-heartbeat allowance for one
observation lemma; the retained successful development check took 105 seconds
for that module. This is engine/control setup cost, not author-trial timing.
Exact candidate build/audit and independent review remain coordinator gates.
The retained development logs include unsuccessful elaboration attempts; those
failures establish neither mathematical impossibility nor performance limits.

The research assumptions remain those distinguished in the
[open-term assessment](open-term-normalization.md) and
[typed authoring assessment](typed-nbe-and-authoring.md). No cubical normalization
theorem is imported as a proof of this implementation. The existing
[reviewed prospective protocol](dependent-conversion-authoring-protocol.md)
continues to govern the later comparison.

The later trial requires frozen tasks, a held-out binder/repair task, the same
model/configuration and explicit resource budgets, independent fresh authors
for direct-helper and service routes, assistance/repair/check logs and a
comparable cost ledger. No authors have been exposed to these tasks, and this
implementation author cannot count as an independent trial author. The protocol
and tasks must be reviewed and frozen before execution. Engine correctness alone
supports no productivity claim. Issues #401, #260, #214, #107 and #108 retain
their existing scope; this work does not activate or replace them.

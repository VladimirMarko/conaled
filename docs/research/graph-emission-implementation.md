# Verified emission of the bounded graph core

[#132](https://github.com/VladimirMarko/conaled/issues/132) extends the tested
[#125](https://github.com/VladimirMarko/conaled/issues/125) emitter with a pure
producer and separate typing and denotation proofs. The producer covers every
`GraphTarget.Code` constructor, including simultaneous substitution and both
existential eliminators. It does not extract executable code from source proofs
in `Prop`.

## Pure construction and exact conversion

[`CoreSyntax`](../../SquareKit/Internal/CoreSyntax.lean) represents bound
variables, sorts, named constants with universe arguments, application,
lambda, and dependent function types. `Expr.ofLean_toLean` proves that its
partial decoder recovers every converted expression. `Expr.toLean_injective`
and `inLean_toLean` transfer independently stated relations to actual
`Lean.Expr`; conversion cannot erase a wrong index, constant, or universe.
The module proves renaming and simultaneous substitution composition, including
their interaction with weakening and binders.

[`GraphEmissionPure`](../../SquareKit/Internal/GraphEmissionPure.lean) constructs
all primitive arguments explicitly. There is no inference through `mkAppM`.
`formula_subst`, `formula_instantiate`, `formula_rename`, and `formula_weaken`
connect source substitutions and binder changes to emitted syntax.

The declaration telescope starts with `A B C : Type v`, `f : A → B`, and
`g : B → C`. The target context is newest first; its tail is abstracted first.
The proof hypothesis is last. For the graph declarations the resulting order
is `A B C f g z x h`. Every carrier has universe `Level.succ (Level.param v)`;
Eq, Exists, and their helpers receive that explicit universe. `congrArg`
receives it for both domain and codomain. Any new binder shifts the model,
object assignment, and existing proof expressions together.

## Typing, meaning, and composition

[`CoreTyping`](../../SquareKit/Internal/CoreTyping.lean) defines the admitted
core typing judgment independently of target code. It has explicit de Bruijn
lookup, sort, dependent function, application, lambda, and weakening rules.
Its primitive rules specify the complete raw applications for Eq, And,
Exists, reflexivity, symmetry, transitivity, congruence, conjunction operations,
and existential introduction/elimination. They are the standard native Lean
primitive schemas. This is a declarative fragment judgment, not a model of
Lean's checker algorithm or a universal checker-acceptance theorem.

[`GraphEmissionTyping`](../../SquareKit/Internal/GraphEmissionTyping.lean)
requires `ModelTyped` and `AssignmentTyped` for open terms. The model supplies
actual carrier and arrow typing derivations in a raw context; every assigned
object expression must have its carrier type. `code_typed` proves preservation
for arbitrary supported code. `context_typed` abstracts an arbitrary typed
continuation. `parameterModel_typed`, `closeParameters_typed`, and
`emitCore_typed` discharge all those compatibility premises for a complete
artifact, yielding `HasType [] body type`. `emit_typed` transfers this result to
the exact Lean expressions.

`TermDenotes` and `FormulaDenotes` interpret primitive syntax relative to an
explicit interpretation and assignment. The existential rule interprets its
new bound variable and shifts outer expressions. They are open relational
interpretations; an arbitrary aliased assignment is not claimed to define a
functional evaluator. `formula_toLean_denotes` establishes that the actual
emitted proposition syntax denotes `Formula.eval`. Complete declarations use
the explicitly constructed parameter and binder assignments.

[`GraphEmissionProof`](../../SquareKit/Internal/GraphEmissionProof.lean)
separately defines primitive proof derivations indexed by the raw proposition
and its meaning, proves their soundness, and proves `code_denotes` for every
constructor. It uses no equality of host proofs to establish syntax meaning.
[`GraphEmissionContract`](../../SquareKit/Internal/GraphEmissionContract.lean)
proves telescope abstraction and `emit_denotes`. Its producer-independent
`ArtifactDenotes` relation decodes both the type and body. Typing is the separate
`ArtifactTyped` contract; neither is replaced by the other.

[`GraphEmissionSquares`](../../SquareKit/Internal/GraphEmissionSquares.lean)
uses the existing `Relational.RelSquare` and composition operation. It composes
source formula preservation, an explicitly supplied executable code certificate,
and the pure producer. `source_emission` gives typing and denotation for the
composite. Alternate producers can supply the same artifact relations without
returning the pure producer's exact bytes. General validation of such producers
belongs to #133.

## Primitive environment and installation

The environment contract is the pinned Lean 4.35.0 declarations recorded in
[`GraphPrimitiveEnvironment`](../../SquareKit/Internal/GraphPrimitiveEnvironment.lean).
These are complete `ConstantInfo` records: names, universe parameters, exact
types and bodies, safety fields, constructor and inductive metadata, and
recursor rules. `checkExactEnvironment` compares those records structurally
before installation. Lean's expression comparison ignores binder names, which
have no binding significance. The older hash manifest remains a regression
diagnostic; it is not used to justify the semantic connection.

The direct primitive operations are Eq, And, Exists, Eq.refl, Eq.symm,
Eq.trans, congrArg, And.intro, And.left, And.right, Exists.intro, and
Exists.elim. Their inspected dependency closure also includes Eq.rec,
Exists.rec, rfl, Exists.casesOn, and the pinned private Exists elimination
matcher. The exact records make that closure inspectable. The closure audit
rejects unknown, unsafe, axiomatic, or unapproved dependencies.

`GraphEmission.emit` wraps the proved pure function.
`GraphEmissionPure.declaration` constructs the complete theorem payload with
one universe parameter, `v`. `installProduced` passes that very declaration
to installation and compares the installed `ConstantInfo` with the producer's
record. `constantInfo_type` and `constantInfo_value` identify its fields with
the proved expressions. The body is installed unchanged; `expandHelpers` is
retained only for the older experimental interface and regression tests.
`emitInferred` preserves that separate unverified producer.

`#emit_graph` still compares the two types with independently elaborated graph
statements. The synchronous `Environment.addDeclCore` check reports rejection
before `addDecl` mutates the environment. Installed graph declarations have
empty transitive axiom sets in the retained execution checks.

The Lean elaborator, compiled execution of the pure functions, environment
inspection, declaration installation, serialization, and the host kernel are
trusted execution boundaries. The formal results concern the represented
syntax, its specified primitive environment, the bounded typing judgment, and
native interpretation. They do not prove that an arbitrary serialized binary,
checker implementation, or runtime executes that model. There is no native
axiom shortcut, new global axiom, full Lean self-model, or reflection from
arbitrary core declarations.

## Checked applications and corruption cases

[`Examples.GraphEmission`](../../Examples/GraphEmission.lean) retains the
installed forward/backward clients, the numeric witness 3 and output 6,
distinct Nat/Option/product carriers, and Type 1 specialization. New cases
exercise `elimWith` while retaining an outer equality, simultaneous
substitution by reversed function applications, and substitution beneath an
existential binder. They use the universal typing and denotation results and
the composed source/emission square.

An independently written raw existential predicate fixes the positions of
witness, endpoints, both functions, and all carriers. Its arithmetic
specialization uses the actual syntax-denotation theorem. The conversion
injectivity example distinguishes universe arguments. Runtime failure cases
cover open and closed binder corruption, universe corruption, reversed
conclusions that remain well-typed propositions, helper-body corruption,
inductive metadata corruption, unsupported syntax, dependency drift, and
name collisions. These checks supplement the universal proofs.

The existing #107/#108 repair and independent-author boundary is unchanged.

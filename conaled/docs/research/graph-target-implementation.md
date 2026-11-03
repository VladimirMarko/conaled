# Typed graph target and native denotation

[#124](https://github.com/VladimirMarko/conaled/issues/124) implements the
restricted representation and native interpretation proposed in
[the target contract](lean-core-target-contract.md). It does not emit
`Lean.Expr`, inspect installed constants, or interpret full Lean.

## Representation and judgments

[`GraphTarget`](../../SquareKit/Internal/GraphTarget.lean) defines a fixed
three-sort target. `Term Γ s` is its data typing judgment; `Formula Γ` admits
carrier equality, conjunction and existential binding. `Code p q : Type` is
an inspectable proof-code judgment for a lambda from p to q. Its constructors
are typed schemas for the core image, with no semantic-validity constructor.
`Declaration` packages a context, premise, conclusion and typed body.

The target reuses source `Var`, the ordered context assignment `Env`, and the
three-sort model interface `Interpretation Graph.Arrow`. Separate target
terms and formulas exclude relation symbols, including the source's impossible
empty-relation constructor. Separate proof code retains constructor data:
source `Derives` lives in `Prop` and cannot in general be eliminated into code
in `Type`. The new target does not change that source API.

The interpretation uses native carrier functions, equality, `And` and `Exists`.
`term_subst`, `formula_subst`, `formula_shift` and `formula_instantiate` prove
capture-avoiding substitution and its context action. Lifting fixes the new
variable at index zero and shifts each old substitution image. Variable names
are absent, so alpha-renaming does not change the representation. A context
renaming is the variable-valued special case of substitution.

`sound` validates every admitted proof schema, including substitution and
existential elimination with a retained hypothesis. `declaration_sound`
universally closes the result over the model and ordered context. No carrier
inhabitants or choice operation are required. The native interpretation
discharges the semantic primitive schemas directly; it has no premise asserting
that an arbitrary installed environment implements them.

## Specified core image and emission boundary

A future emitter must realize the following mapping, maintaining a map from
our data-variable indices to core indices. Core proof binders also shift data
indices. The list order places the newest data binder first; the graph body
has `[middle,input,output]`, interpreted by `y,x,z`.

| Target constructor | Specified core image |
| --- | --- |
| `Term.var`, `Term.app` | Bound variable, application of telescope f or g |
| `Formula.eq` | `Eq` applied to its carrier and two data terms |
| `Formula.conj` | `And` applied to two propositions |
| `Formula.ex` | `Exists` applied to its carrier and a lambda over that carrier |
| `Code.ident`, `Code.cut` | Identity lambda, lambda applying the second proof to the first proof's result |
| `left`, `right`, `pair` | Lambda using conjunction elimination or introduction |
| `refl`, `symm`, `trans`, `congr` | Lambda using reflexivity or equality-eliminator helper bodies |
| `intro` | Lambda introducing the evaluated witness term and instantiated premise proof |
| `subst` | Simultaneous substitution of data terms before generating the body |
| `elim`, `elimWith` | Lambda eliminating Exists into the conclusion proposition, with the witness binder and optional retained premise |

The declaration telescope is `A B C : Type v`, `f : A → B`, `g : B → C`,
the data variables specified by `context`, then the premise proof. The external
universe parameter v is fixed per instantiation. Carriers are `Sort (v+1)`;
carrier-parameter binder types live in `Sort (v+2)`. Formulas and the closed
sequent are in `Sort 0`, using the proposition-valued `imax` case. K contains
no object-language universe quantifier, type-valued term or arbitrary Prop
parameter. `Declaration.denote` packages the telescope semantically via the
model interface; it is not a model of Lean's universe formation rules.

The intended primitive environment contains Eq and reflexivity/equality
elimination, And and its introduction/elimination, and Exists and its
introduction/elimination. Other equality helpers and conjunction projections
must expand to checked bodies over that environment. The installed names,
universe instantiations, recursor metadata and transitive dependency closure
are obligations of [#125](https://github.com/VladimirMarko/conaled/issues/125).
An environment extension must assign fresh theorem names to generated types
and bodies and check them; `Declaration` itself has no installed names or
mutable environment. No environment-extension correctness theorem is claimed.

The supported semantic conversions are substitution (including renaming),
implication beta (`cut_beta`), conjunction iota (`left_iota`, `right_iota`),
and existential introduction/elimination (`intro_beta`, `elim_iota`). These
state the native equations for the admitted helper schemas. `proof_irrel`
validates any comparison of two K proofs with the same premise and conclusion
at the native proof observation. It does not equate their code. Helper delta
expansion to installed constants, and actual kernel beta/iota conversion of
emitted expressions, remain emission obligations. K has no data lambdas,
lets, arbitrary delta reduction or data eta rule. The denotation theorems do
not certify unrestricted core conversion.

## Source comparison and checked cases

[`GraphTargetComparison`](../../SquareKit/Internal/GraphTargetComparison.lean)
translates terms and formulas computationally. It proves syntactic commutation
with substitution, lifting, shifting and instantiation; the semantic context
comparison is `substitution_comparison`. `term_comparison` states equality of
data values; `formula_comparison` states equivalence of propositions.

`translate_derivation` proves that every source derivation has target code,
by the corresponding rule cases. Its result is `Nonempty Code` in Prop.
It deliberately provides no choice-based function extracting a program from
a source proof. `forward` and `backward` are explicit target programs available
to an emitter, and their declarations are explicit as well. The two comparison
theorems connect their denotations to `Graph.forward`/`Graph.backward` through
source soundness. `proof_comparison` is pointwise equality of proofs of the
same native proposition after applying the formula equivalences. It uses
proof irrelevance; it does not preserve proof-relevant witnesses or identities.

[`Examples.GraphTarget`](../../Examples/GraphTarget.lean) checks distinct
carriers, coincident Nat carriers, the existential binder order, both proof
directions, the non-vacuous witness 3 for output 6, and rejection of output 5
from swapped function order. Empty input is permitted, while a first arrow
from Unit into Empty is proved impossible. Declaration closure is specialized
at two host universe levels. The cases consume the target soundness results;
the native graph theorem is not used as a substitute for target soundness.

Statement review checked the context order and lifting under Exists, equality
versus equivalence, absence of inhabitance and choice premises, and the scope
of proof irrelevance. The arithmetic expectation was fixed as increment 2,
then double, before connecting it to `graph_equivalence`. The initial missing
obligation was this target connection; the native arithmetic fact and existing
source proof were already available. The distinct-carrier case detects sort
mixups; the coincident-carrier negative case detects a wrong well-typed result.

No source client, #107/#108 theorem selection, relative model, reflection rule,
or model-existence assumption changes. The next concrete contract is emission
from these explicit declaration codes with structural expected-type checks,
installed primitive identification and an artifact axiom audit.

The bounded emitter is now implemented in
[graph core emission](graph-emission-implementation.md). It consumes these
explicit declaration codes, checks independent expected propositions, expands
installed helpers and enforces the measured primitive dependency boundary.
The proved target semantics and the tested emission connection remain distinct.

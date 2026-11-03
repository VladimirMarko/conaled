# Staged arithmetic configuration

[Issue #214](https://github.com/VladimirMarko/conaled/issues/214) selects a
bounded staging route: evaluate an integer configuration expression, insert its
literal into an existing first-order body, then compile the residual syntax to
the existing typed stack machine. The consumer is `Arithmetic.shared`, the
let-sharing polynomial `(a*b)*(a*b)+a`, with configured `a` and runtime `b`.
The checked example computes configuration `1+2`, emits residual code containing
literal 3, and executes that code at input 4 to obtain 147.

## Selection against the local alternatives

[FirstOrder](../../FirstOrder.lean) already supplies typed products, let, primitive
operations and a target-parametric compiler. [Arithmetic](../../SquareKit/Arithmetic.lean)
supplies integer literals, addition, multiplication and negation, plus the
shared polynomial. [StackMachine](../../Applications/Stack/Machine.lean) already
produces typed instruction sequences and proves their execution correct for
arbitrary stack tails. The missing route was replacing a separately available
configuration computation with residual literal syntax while preserving that
compiler contract.

The higher-order compiler gained capture-avoiding substitution in #203, but
its `Ty`, `Var` and `Term` are distinct from the first-order source. The graph
emitter's substitution and correctness theorems likewise concern a different
source grammar and host-core artifact contract. This experiment adds the
first-order operations it actually needs; it does not convert arithmetic into
graph judgments or claim acceptance by the graph emitter.

Normalization by evaluation would instead require an explicit normal/neutral
syntax, evaluation and reification, and a normalization/equality theorem for
its chosen fragment. The repository's path-transport normalizers solve bounded
path problems, not normalization of arbitrary arithmetic terms. No concrete
consumer requiring a new arithmetic or higher-order equality decision procedure
was established here. The configured stack consumer benefits from staging
without that additional claim, so NbE is deferred. No speculative implementation
issue is needed until such a consumer and equality contract are specified.

## Phase discipline and residual correctness

[Arithmetic.Staging](../../SquareKit/ArithmeticStaging.lean) uses the following
interface, with existing source terms on both sides:

```
Program Δ Γ a
  configuration : Term Arithmetic.Prim Δ base
  body          : Term Arithmetic.Prim (base :: Γ) a

specialize : Program Δ Γ a → Val Int (context Δ) → Term Arithmetic.Prim Γ a
```

`Δ` contains static inputs; `Γ` contains runtime inputs. The body's newest
variable is the configured integer. Phase one receives only the static
valuation, evaluates `configuration`, quotes the resulting integer, and
substitutes it for that variable. It returns syntax, not a function closure
containing a runtime environment. Static and runtime contexts may have the same
shape, but no runtime valuation or variable is automatically available to the
static expression. This is an explicit two-phase boundary, not inference of
binding times for arbitrary source programs.

The phase index means compilation availability. It is neither the processing
clock of the temporal FRP experiments nor a physical deadline. The residual
language is exactly the first-order language: unit, products, variables, let
and arithmetic primitives. There is no new universal AST, quotation type,
modal kernel rule, recursive source construct, effect or scheduler.

[FirstOrderSubstitution](../../SquareKit/FirstOrderSubstitution.lean) provides
intrinsically typed renaming and substitution, including lifting beneath the
let binder. `eval_subst` proves interpretation compatibility for any primitive
meaning and agreeing environments; `eval_single` specializes it to replacing
the newest variable. These are semantic substitution theorems, not a
normalization or syntactic-equality decision procedure.

`specialize_correct` states, for every static and runtime valuation,

```
eval residual runtime = eval body (runtime, eval configuration static).
```

`static_substitution` proves exact residual syntax equality when a substitution
in the static expression agrees with its supplied valuation.
`runtime_substitution` proves interpretation compatibility for substituting
runtime inputs into the residual term. Both use the general substitution
contract; neither assumes a closed runtime body. Intrinsic indices establish
that the result has context `Γ` and result type `a`.

The negative `no_static_variable` states that `Var [] base` is empty. A runtime
variable therefore cannot be used as a variable in a closed static expression.
`no_runtime_dependency` also proves that no such closed arithmetic expression
can equal every possible runtime integer. Explicitly passing a value as a
static input changes the phase contract; it is not an implicit cross-stage
reference.

## Composition with the existing backend

`compile_correct` composes specialization with any existing target equipped
with `Sound Int K Arithmetic.meaning`. Its conclusion observes the compiled
residual under that target's denotation and equates it to the original staged
meaning. The required primitive and structural laws remain the target author's
obligations.

[Stack.Staging](../../Applications/Stack/Staging.lean) supplies `stack_correct`
by composing `StackMachine.compile_correct` with `specialize_correct`.
It preserves the entire arbitrary stack tail, and produces an inspectable
`StackMachine.Program`. The backend already uses the first-order naturality
contract; no backend soundness induction is repeated. This is instruction
compilation and execution, not native Lean core declaration emission or a
proof of kernel acceptance for a new artifact format.

[Checked examples](../../Examples/ArithmeticStaging.lean) obtain the staged
body by substituting a pair of inputs into the existing `Arithmetic.shared`.
`body_value` reuses its existing polynomial theorem. `residual_value` connects
that independent account to the generic specialization theorem. The ordinary
client is the direct Lean polynomial function and needs no syntax interface.

The positive cases include static configurations 3, -2 and 0, an actual stack
execution yielding `(147, ())`, static substitution, and runtime substitution
through the retained let binder. A separate open-variable substitution case
keeps runtime value 4 free beneath a let-bound 99; the intentionally captured
version returns 99. The executable example prints the result and
instruction listing. Checked listing properties count one residual `ADD` and
more than one in the version that inlines the unevaluated static configuration.
This establishes the removal of those static additions from this artifact;
it is not a runtime speedup, allocation or optimal-code theorem. Product
projections and other residual structure are deliberately left intact.

## Sources, obligations and remaining scope

[Davies, A Temporal-Logic Approach to Binding-Time Analysis, introduction](https://www.cs.cmu.edu/Groups/fox/people/fp/courses/15816-s10/papers/Davies96.pdf)
relates availability at successive stages to constructive temporal types and
shows how binding-time discipline constrains specialization. It motivates the
separation of static and dynamic input here. This bounded configuration
specializer does not implement Davies's full lambda-circle calculus or its
time-ordered normalization theorem.

[Sterling, First Steps in Synthetic Tait Computability, chapter 5](https://www.csd.cs.cmu.edu/sites/default/files/phd-thesis/CMU-CS-21-142.pdf)
treats normalization through semantic constructions and reification; the
following recursion-theoretic discussion distinguishes normalization structure
from effective computation. Those stronger obligations explain why preservation
of one integer interpretation is not advertised as NbE or decidable equality.
A future NbE route must select its source equality and consumer before proving
normal-form completeness and execution.

A client supplies a configuration term, a body and a static valuation. The
configuration-to-residual interface is one record; no per-client semantic
preservation proof is required. The polynomial example has one pair-substitution
adapter with two variable indices and one source-value lemma that reuses
`Arithmetic.eval_shared`. The shared infrastructure supplies typed substitution,
quotation correctness, specialization correctness, two phase-specific
substitution comparisons, and the compiler/stack comparisons. These are
bookkeeping and proof obligations, not an automatic frontend for arbitrary
ordinary Lean programs.

[#109](https://github.com/VladimirMarko/conaled/issues/109) retains source
recursion, fixed-point interpretation and incrementalization obligations.
Both compiler transformation and source evaluation here recurse only on finite
syntax; unrestricted fixed points are absent.
[#128](https://github.com/VladimirMarko/conaled/issues/128) retains the independent
graph-to-core emission and relative-checker contracts. Host/target version
compatibility is unchanged. The temporal workstream retains its own reactive
progress and causality contracts; staged configuration proves none of them.

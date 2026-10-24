# Emitting the graph declarations in Lean core

[#125](https://github.com/VladimirMarko/conaled/issues/125) implements the
bounded emission experiment after [the typed target](graph-target-implementation.md).
[`GraphEmission`](../../SquareKit/Internal/GraphEmission.lean) consumes the
explicit `forwardDeclaration` and `backwardDeclaration` data. It traverses
`Term`, `Formula` and every `Code` constructor to build actual `Lean.Expr`
types and proof bodies. It does not extract code from source proofs in Prop.

## Declaration and environment checks

The telescope is `A B C : Type v`, `f : A → B`, `g : B → C`, `z : C`,
`x : A`, then the premise. Reversing the target context list when creating
local declarations puts its newest variable `x` at index zero. Lean's local
variable abstraction manages data and proof binders together. Substitution
changes the data assignment; existential branches extend it with the witness.
Every constant carries an explicit universe instance in the completed Expr.
Metavariables, free locals and loose bound variables are rejected before
installation.

`#emit_graph ForwardName BackwardName` independently elaborates these expected
propositions from host syntax, without consulting target formulas or emission:

```lean
∀ (A B C : Type v) (f : A → B) (g : B → C) (z : C) (x : A),
  (∃ y, y = f x ∧ z = g y) → z = g (f x)
∀ (A B C : Type v) (f : A → B) (g : B → C) (z : C) (x : A),
  z = g (f x) → ∃ y, y = f x ∧ z = g y
```

Structural Expr equality compares their binder structure, constant names,
universe instances and endpoints with emitted types. Binder names are ignored;
there is no conversion-based relaxation of the proposition comparison.
Fresh names are required. A synchronous `Environment.addDeclCore` check uses
kernel checking enabled, followed by ordinary `addDecl` installation. This
makes a kernel rejection observable before mutating the environment, including
when ordinary declaration checking runs asynchronously.

Lean **4.35.0** is enforced. `environmentManifest` records the primitive and
helper level parameters, structural hashes of their types and bodies, and
inductive, constructor and recursor metadata. The hashes detect accidental
environment drift; they are neither cryptographic authentication nor a proved
environment correspondence. The pinned toolchain and its installed environment
remain trusted inputs. The human-readable [manifest](graph-emission-manifest.txt)
records exact types, helper bodies and recursor rules with `pp.all`. Reproduce it
by importing `GraphEmission` and running `#graph_manifest`.

Helpers (`Eq.symm`, `Eq.trans`, `congrArg`, `rfl`, conjunction projections,
`Exists.elim`, `Exists.casesOn` and the pinned private elimination matcher)
expand to their checked installed bodies before installation. Expansion is
bounded and fails on exhaustion. There is no arbitrary-constant constructor
in the target code. The final primitive boundary is:

| Primitive | Role |
| --- | --- |
| `Eq`, `Eq.refl`, `Eq.rec` | Carrier equality, reflexivity and equality elimination |
| `And`, `And.intro` | Conjunction and introduction; projection expressions eliminate it |
| `Exists`, `Exists.intro`, `Exists.rec` | Proposition-valued existential and its introduction/elimination |

Expanding `And.left` and `And.right` retains `Expr.proj And 0` and
`Expr.proj And 1`. The [target contract](lean-core-target-contract.md#fragment-k-and-its-environment)
now includes those two forms and their reductions on `And.intro`. They implement
K's conjunction elimination schemas, whose native meanings are proved by
`GraphTarget.sound`. No arbitrary structure projection is supported. The native
`left_iota` and `right_iota` results compare K proofs; they do not establish a
semantic theorem about emitted Expr projections or kernel conversion.

The emitter builds expressions from typed K code and pinned helper bodies. The
final checks do not include a separate Expr-constructor recognizer; dependency
and kernel checks alone are not a proof of fragment membership. The supported
interface emits the two graph declarations, without importing arbitrary Expr.

The audit follows types, available bodies, inductive constructor references,
constructor parents and recursor rule expressions. It rejects unknown names,
unsafe constants, axioms and every dependency outside the boundary. The helper
environment is audited separately before expansion. The measured forward
closure contains all eight primitives above. The backward closure contains
all except `Eq.rec` and `Exists.rec`. Both installed declarations have **empty
transitive axiom sets**, measured with Lean's `collectAxioms`. The fragment
rejects even `Classical.choice` and `propext`, which the broader repository
allows. No claim about the axiom set of the metaprogram itself follows from
that artifact result.

## Checked uses and limits

[`Examples.GraphEmission`](../../Examples/GraphEmission.lean) calls the actual
installed declarations in both directions. Incrementing 2 gives witness 3;
doubling it gives output 6. A separate specialization uses Nat, Option Nat and
Nat × Bool to detect sort confusion. Another instantiates carriers in Type 1.
Universal proof comparisons connect the emitted forward proof to
`GraphTarget.graph_equivalence` and the backward proof to `Graph.inSet`.
These equalities use proof irrelevance after checking identical native
propositions; they do not preserve computational witness data.

The retained failure checks require the designated diagnostic. They cover an
open binder, a closed corrupted binder, a wrong universe instance, an opposite
direction body, duplicate names, unknown constants, disallowed foundational
axioms, changed environment signatures and a missing transitive constructor.
The changed-conclusion test specializes the actual emitted type to coincident
Nat carriers, matches it to the intended host proposition, checks that reversed
composition is still a well-typed proposition, and requires structural rejection.

The first executable obligation was an absent emission interface for the
concrete forward/backward clients. Subsequent kernel checks exposed the
existential introduction argument convention and the need for synchronous
failure reporting; both were corrected without changing the mathematical
expectations. Statement review checked quantifier order, witness binding,
function order, universe specialization and the proof-irrelevant scope of the
comparison examples. They introduce no inhabitance or choice hypotheses.

The target's `sound`, `translate_derivation` and comparison theorems remain
formal proofs about the restricted syntax and native semantics. Actual Expr
emission, expected-type construction, helper expansion, environment checks and
dependency traversal are executable code with retained tests. There is no
formal theorem identifying a model of Lean expressions with `Formula.eval`,
no full Lean self-model and no reflection from arbitrary core declarations.
Kernel acceptance establishes that the installed body proves its installed
type; the independent structural check and checked clients supply the bounded
connection to the intended graph proposition. Arbitrary core import, runtime
IR and environment-extension semantics remain outside this experiment.

The earlier #107/#108 proof selection and ordinary native clients are unchanged.

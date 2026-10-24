# Relative set-model feasibility for the graph signature

Assessment for [#126](https://github.com/VladimirMarko/conaled/issues/126), at
local baseline `ad1c9b35d20cdc2add0086e98eef2ef1d3afaabe`.

The pinned ConLeche model theorem builds and its selected transitive axiom
inventory meets the repository's whitelist. A conditional formula adapter is
checked in isolation. Adoption remains pending: the experiment does not
construct an accepted graph environment or derive the meanings of `And` and
`Exists` from its installed declarations. Those two primitive interpretation
laws are explicit premises of the adapter. They are not consequences claimed
for an arbitrary `ConLeche.Model`.

The [native graph target](graph-target-implementation.md) and
[Lean expression emitter](graph-emission-implementation.md) remain independent.
Neither imports this experiment. The fresh-theorem and ordinary-client contracts
of #107/#108 are unchanged.

## Pinned builds and selected inventories

The experiment uses two separate temporary checkouts, with no port or dependency
change to conaled:

| Source | Revision | Toolchain and observed Lean commit |
|---|---|---|
| [ConLeche](https://github.com/leanprover/con-leche/tree/8e166ca53cd1f864b63c13cc1d326d38316d00ea) | `8e166ca53cd1f864b63c13cc1d326d38316d00ea` | Lean 4.35.0, `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` |
| [Lean4Lean](https://github.com/digama0/lean4lean/tree/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3) | `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` | Lean 4.33.0-rc2, `d8b18978322de05a8f3dba51ef03cf5461676c17` |

ConLeche's package has no external Lake dependencies. Lean4Lean's checked-in
manifest pins Batteries to `76e1c118b0700b4ceafe99532e887d6431625e1a`.
The incompatible toolchains are kept separate; this is not a demonstration
that both libraries can be imported into one Lean environment.

From the repository's Nix shell, the selected commands were run in their
respective checkouts:

```sh
lake build ConLeche.MainTheorem
lake env lean /path/to/conaled/experiments/relative-graph/ConLecheAudit.lean
lake env lean /path/to/conaled/experiments/relative-graph/GraphAdapter.lean

lake build Lean4Lean.Theory.Typing.Basic Lean4Lean.Theory.Typing.Lemmas \
  Lean4Lean.Theory.Typing.UniqueTyping
lake env lean /path/to/conaled/experiments/relative-graph/Lean4LeanAudit.lean
```

The ConLeche build completed 536 jobs; the Lean4Lean build completed 49 jobs.
These are Lake's reported counts for the observed fresh selected builds, not
counts of audited declarations. The selected axiom inventories are:

| Declaration | Exact transitive axiom set |
|---|---|
| `ConLeche.model_exists` | `propext`, `Classical.choice`, `Quot.sound` |
| `ConLeche.Denotes_functional` | `propext`, `Classical.choice`, `Quot.sound` |
| `ConLeche.Model.mem`, `ConLeche.Model.eq_equality` | each: `propext`, `Classical.choice`, `Quot.sound` |
| `ConLeche.SetModel.app_lamV`, `ConLeche.SetModel.app_mem_piV` | each: `propext`, `Classical.choice`, `Quot.sound` |
| `ConLeche.SetTheory.of_mem_truthVal`, `ConLeche.SetTheory.eq_of_mem_eqv` | each: `propext`, `Classical.choice`, `Quot.sound` |
| `Lean4Lean.VExpr.liftN_zero`, `Lean4Lean.VEnv.IsDefEq` | each: `propext` |
| `Lean4Lean.VEnv.HasType.instN` | `propext`, `Quot.sound` |
| `Lean4Lean.VEnv.IsDefEq.uniq` | `propext`, **`sorryAx`**, `Quot.sound` |

The last result rules out using that type-uniqueness theorem under our proof
standard. The build also reports admissions in `Theory.Inductive`,
`Typing.InductiveLemmas`, `Typing.Injectivity` and `Typing.UniqueTyping`.
In particular, [the injectivity lemmas](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/Lean4Lean/Theory/Typing/Injectivity.lean)
are admitted. This does not taint the separately audited substitution theorem,
nor does it establish that the whole declarative tier is acceptable.
The implementation verification tier was not built or audited here; its
source-level axiom concerns remain as recorded in the
[design contract](lean-core-target-contract.md#lean4lean-syntax-and-checker-contracts-with-admitted-gaps).

The [reproduction script](../../experiments/relative-graph/reproduce.sh) clones
the exact revisions into a new temporary directory and repeats these commands.
Run it from conaled with
`direnv exec . bash experiments/relative-graph/reproduce.sh`.
It preserves build and audit output in the printed directory. A zero script
exit means the commands completed; Lean4Lean's diagnostic `sorryAx` result is
intentional and is not an adoption approval.

## Expressions, telescope and declarations

The shortest selected semantic path is directly through ConLeche's
[`Expr`](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/Kernel/Expr.lean#L315),
[`Declaration` and `Env`](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/Kernel/Env.lean#L391),
and [`Denotes`](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/Denotes.lean#L123).
This avoids a translation through Lean4Lean's `VExpr` and its separate
`VEnv.IsDefEq` judgment. `VExpr` has only bound variables, sorts, constants,
applications, lambdas and dependent functions; ConLeche's `Expr` also has
projections, lets, literals and typed free variables. `Denotes` has no free
variable clause. Neither datatype is the installed `Lean.Expr`.

Use a natural-valued universe assignment `φ`; at the graph's carrier level
`u = succ (param v)`, the carrier sets must belong to `univ (Level.eval φ u)`.
This is a fixed interpretation of the object universe parameters, not an
embedding of every native Lean universe into one set.

The declaration telescope is `A B C f g x z`, with types
`A B C : Sort (succ v)`, `f : A → B`, `g : B → C`, `x : A`, `z : C`.
Under that telescope the de Bruijn assignment is:

| Index | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| Value | z | x | g | f | C | B | A |

Under `λ y:B`, the list becomes `y,z,x,g,f,C,B,A`.
`Eq.{u} B y (f x)` and `Eq.{u} C z (g y)` are three applications of
the `Eq` constant; their conjunction is two applications of `And`.
`Exists.{u} B (λ y:B. ...)` applies the existential constant to the carrier
and that predicate. The result is `Eq.{u} C z (g (f x))`.
All binders and applications are explicit in the checked artifact.

A closed proof would be submitted as
`Declaration.thmDecl ⟨name, [v], telescope (P → Q)⟩ body`
and similarly for `Q → P`. The accepted environment stores only its
`ConstantInfo.thmInfo` statement. `Env` contains a list of constants and
projection tables. The graph's primitive environment needs the pinned Eq
basis, `And`'s inductive block and projection table, an `Exists` inductive
block, and any referenced helper declarations. ConLeche
[pins `And`](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/Kernel/Basis/And.lean)
but installs it through the general inductive mechanism; `Exists` is not a
handwritten basis model. The conditional artifact operates on open formulas
under the specified telescope. It does not submit these closed theorem records
or translate the #125 proof bodies.

## Model assumptions and formula preservation

The exact public theorem is:

```text
model_exists (V : Type w) [SetTheory V]
  (pins : List NatOpPinSet) (ds : Array Declaration) (env : Env)
  (accepted : Cached.checkDecls .verified pins ds = .ok env) :
  Nonempty (Model V env)
```

[`SetTheory V`](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/SetTheory/Core.lean)
supplies membership, extensionality, pairing, union, power set, regularity,
replacement for arbitrary host functions `V → V`, and a natural-indexed chain
of Grothendieck universes. No instance is constructed here. Auditing the
theorem's axioms does not remove these explicit hypotheses.

[`Model`](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/Denotes.lean#L248)
supplies `cval`, `mem`, `false_empty` and `eq_equality`. `mem` places each
stored constant in a denotation of its declared type. Once a graph theorem's
type is proved to denote the expected implication truth value, membership
would establish that implication, using `Denotes_functional` to identify the
denotation and `of_mem_truthVal` to recover the proposition. That is a route
to preservation of the graph formulas, rather than merely rejection of False.
It still needs the formula comparison and accepted declaration membership.

The checked [adapter](../../experiments/relative-graph/GraphAdapter.lean) chooses
native carriers `Member A := {a : V // a ∈ˢ A}`, and likewise for B and C.
The native arrows are `a ↦ ⟨app F a.val, hf a.val a.property⟩` and its G
counterpart. It assumes closure of these set applications, endpoint membership,
and universe membership for B and C. These are enough for the open formulas;
they do not prove that F and G inhabit the full telescope's function types,
or that A inhabits its declared universe. Closed declaration typing would
need those additional membership obligations.

`Primitives` records lookups and universe arities for Eq, And and Exists.
Its two additional semantic premises are:

```text
And(truthVal p, truthVal q) = truthVal (p ∧ q)
Exists(A, lamV A (a ↦ truthVal (P a))) =
  truthVal (∃ a, a ∈ˢ A ∧ P a), provided A belongs to the chosen universe.
```

Here the left-hand names mean application of the corresponding `m.cval`
values at the exact universe substitutions, not native Lean connectives.
The Eq comparison is derived from `Model.eq_equality`, with the carrier and
both element membership premises discharged. No graph truth is assumed in
`Primitives`; its laws describe the two primitive logical operations uniformly.

`graph_denotes` constructs denotations for both raw formulas. `graph_comparison`
uses `Denotes_functional` to identify any supplied denotations P and Q and
proves:

```text
pt ∈ˢ P ↔ ∃ y : Member B, y = f(x) ∧ z = g(y)
pt ∈ˢ Q ↔ z = g(f(x)).
```

`graph_truth` consumes that comparison, eliminates the middle witness forward
and chooses `f(x)` backward. It is a checked application to the graph
composition identity, not an independently reproved native formula detached
from the adapter. There is no equality of proof-relevant witnesses, no recovery
of source derivability from validity and no formal link to the local
`Graph.inSet` declaration. Both formulas have the same explicit mathematical
meaning as the graph source after choosing these member carriers.

Statement review checked the binder shift under Exists, the orientation
`y = f(x)` followed by `z = g(y)`, the domains of F/G, and the distinction
between truth-value membership and subtype equality. No carrier is assumed
inhabited. An empty A or C simply has no endpoint; an empty B has no witness,
and the assumed F closure excludes an input in A in that case. No concrete
instance of `SetTheory V`, `Model` or the primitive package is supplied, so
these checked uses do not establish satisfiability of the full hypothesis
package. This is the stated limit of the feasibility example.

## Blocking contract and smallest follow-up

There is no checked function in this experiment from an accepted declaration
array to `Primitives m u φ`. The public `Model` fields alone do not *directly*
provide the two logical-operation equations. This is an interface gap in the
selected adapter, not a proof that the pinned infrastructure cannot establish
them. Source inspection suggests a small next step:

1. Construct one explicit Eq/And/Exists declaration array, with the exact
   formation, constructor and eliminator signatures, and prove or reproducibly
   check its verified acceptance. Record the resulting constant and projection
   tables, without importing all of Init or the native emitter's environment.
2. Derive the two `Primitives` laws for its model from `Model.mem` and those
   signatures. Formation places results in `univ 0`; constructor and eliminator
   membership supply the two truth implications. Candidate tools are
   `app_mem_piV`, `piV_eq_zero`, `app_lamV` and truth-value membership lemmas.
   For Exists, use a proposition motive expressing the semantic witness
   predicate. This proof route is source-inspected, not checked here.
3. Instantiate the conditional comparison with that package, then add the two
   closed graph theorem records and apply `Model.mem` to their types. Audit
   the new selected closure and show the endpoint/binder correspondence.

That follow-up discharges a named obligation without a new kernel axiom or
an unconditional model-existence claim. It does not require a general importer,
full-host reflection, a Lean4Lean port, or replacement of the native route.

## Checked evidence and remaining trust

The selected upstream builds, the inventories in
[evidence.txt](../../experiments/relative-graph/evidence.txt), and the isolated
adapter are checked evidence. The alternative Lean4Lean structural admissions
are observed audit failures for the named declaration. The construction of a
minimal accepted graph environment and the derivation of its And/Exists laws
are remaining work, supported only by the cited source inspection.

The isolated adapter is outside the main project's module graph and exhaustive
`ProofAudit`; its own declarations have a separate inventory. The main
project inputs did not change, so its full build was not rerun for this
experiment. Upstream runtime/compiler trust-surface tests, executable checker
behavior, exporter correctness, installed-Lean expression correspondence and
filesystem/toolchain integrity are not certified by `#print axioms`.
The model theorem concerns its pure verified checker equation. It does not
identify that checker with the installed C++ kernel or erase the explicit
set-theory and primitive-law assumptions.

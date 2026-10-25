# Proving the emission connection and using verified kernels

Research checked on 2026-10-25, following the owner's response to #114 and
#124–#127. The bounded emission connection is a proof obligation we can pursue
now. No incompleteness theorem prevents it. Keeping the emitter tested was a
sequencing choice, not a requirement for frontend flexibility. A stable
preservation relation can accommodate several implementations and surfaces.

This note extracts the relevant claims from the supplied ChatGPT report,
`lean-4.35-kernel-validity-report-updated.md`, and checks them against pinned
primary sources. The report's private binary experiments were not reproduced
here. Its reported exploit outcomes are not used as evidence for a new local
validation claim. The source comparisons and proposals below do not constitute
new Lean proofs or a new upstream build.

The gap analysis below records the baseline before #132. Its pure producer,
bounded core typing, syntax-denotation proofs, exact environment records and
installation path are now described in the
[emission implementation record](graph-emission-implementation.md). The
relative-model, validator and execution connections remain separate tasks.

## The exact local gap

The [typed graph target](../../SquareKit/Internal/GraphTarget.lean) already has
inspectable `Code`, native `Formula.eval`, substitution lemmas and `sound`.
The [source comparison](../../SquareKit/Internal/GraphTargetComparison.lean)
connects source derivations and target code. These are mathematical theorems
about the represented language.

[GraphEmission](../../SquareKit/Internal/GraphEmission.lean) constructs actual
`Lean.Expr` using `MetaM`, local variables, application inference and helper
expansion. It checks expected types, the environment's recorded signatures,
dependency closure and kernel acceptance. Its checks establish useful observed
facts about the two emitted declarations, but no theorem quantifies over every
`Code` and the expressions this procedure returns. The environment hashes are
regression checks, not proofs of the signatures or their denotations.

There are several distinct obligations:

| Connection | What remains to prove |
|---|---|
| Target formulas to core types | Translation respects variables, binders, universes, substitution and the chosen primitive signatures; interpretation of the actual translated type agrees with `Formula.eval`. |
| Target code to core bodies | Every constructor emits a derivation of the translated conclusion from the translated premise. Include both existential eliminators and simultaneous substitution. |
| Executable emission to the proved translation | Either prove successful `MetaM` execution returns that translation, replace its semantic construction with a pure proved function, or validate each returned artifact with a proved checker. |
| Core declarations to the installed environment | Match exact declarations, helper bodies, constructor/recursor metadata and projection tables; retain declaration names, ordering and universe parameters. |
| Mathematical checker to executable acceptance | State separately which parser, driver, compiler and runtime correspondence has been proved or is trusted. |

The second row is not discharged by proving two host proofs equal through
proof irrelevance. That equality follows after their propositions have already
been identified. It does not establish the construction of those propositions
or the interpretation of arbitrary emitted syntax. The existing
[emission record](graph-emission-implementation.md) states this limitation.

## A bounded proof route that preserves implementation freedom

The recommended next implementation is a pure construction of the admitted
core expressions, together with a checked relation to their mathematical
meaning. It can return `Lean.Expr` directly; a second universal intermediate
language is unnecessary. If a small representation makes binder proofs
easier, its conversion to `Lean.Expr` must also be covered.

The pure function should construct explicit applications, universe arguments
and de Bruijn binders. It should avoid asking `mkAppM` to infer the semantic
structure being verified. Prove weakening, substitution and telescope
abstraction once, then prove emission preservation by induction on `Code`.
Primitive signatures and elimination rules belong to the stated environment
contract. Prefer explicit primitive constructions to reading and expanding a
private installed matcher whose body is checked only by a hash.

There are two useful delivery guarantees:

1. **Verified producer:** a theorem covers the pure emitter on every admitted
   code value. The installation command uses that producer, with an explicit
   artifact-identification boundary.
2. **Verified translation validation:** an arbitrary producer supplies an
   artifact and a certificate. A proved validator checks its relation to the
   source code and intended declaration. Each successful use supplies an actual
   kernel-checked proof of the validator equation or relation.

They can coexist. The second permits `MetaM` conveniences and later optimization
without proving all of Lean's elaborator implementation. A Boolean gate executed
by `#eval`, or another test that merely reports success, does not supply that
last proof. The certificate checker and its successful result must themselves
be justified in the accepted logic. The [pinned native evaluation
implementation](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Meta/Native.lean)
adds an axiom for a native result, so `native_decide` would change this project's
axiom contract rather than close the gap under the existing one.

The owner subsequently approved building both approaches. They must share
composable preservation contracts, with operations, semantic equivalence and
laws separated according to the repository's Felix-compatible architecture.
The verified producer must not become the only permitted generation strategy.

A proposed contract, with the interpretation and typing relations still to be
implemented, is:

```text
typed code d : Code p q
  → CoreHasType environment context (emitCode d) (emitImplication p q)

compatible model, assignment and universe valuation
  → DenotesFormula (emitFormula p) ↔ Formula.eval model assignment p

validated artifact a for d
  → a is the declared core translation of d
```

The first theorem concerns a specified core judgment, not universal acceptance
by every kernel implementation. If a chosen checker uses fuel or rejects a
supported mathematical conversion, acceptance requires its own theorem or a
certificate for the successful check. Soundness and acceptance completeness
should remain separate interfaces.

## How #126–#127 shorten the semantic work

The isolated [relative graph experiment](relative-graph-model.md) already
proves primitive meanings for `And` and `Exists` from exact declaration records
and `Model.mem`. Its Eq meaning comes from ConLeche's model interface. It
proves formula denotation comparisons and derives the two closed graph
implications from stored theorem memberships. These provide concrete semantic
lemmas for an emission proof, rather than only a consistency corollary.

Two unclosed connections are visible in the source:

- [AcceptedGraph.model_exists](../../experiments/relative-graph/AcceptedGraph.lean)
  still takes `Cached.checkDecls .verified [] declarations = .ok environment`
  as a premise. [GraphChecks](../../experiments/relative-graph/GraphChecks.lean)
  executes that check, but does not produce a Lean proof of this equation.
- [GraphDeclarations](../../experiments/relative-graph/GraphDeclarations.lean)
  hand-constructs ConLeche expressions. It does not translate the expressions
  returned by the native emitter. Its telescope orders the endpoints `x,z`;
  the native emitter orders them `z,x`. Its forward proof directly substitutes
  with `Eq.rec`, while the native emitter expands helper proofs. These are
  mathematically compatible artifacts, not structurally identical artifacts.

Consequently, simply importing #127's theorem would leave the very connection
the owner is asking to prove unproved. The next experiment should use one
canonical generated declaration family, or prove the binder permutation and
body relation between the existing families. Generalize the formula comparison
over the admitted `Formula` constructors and the code correspondence over
`Code`; do not add another independently handwritten graph proof.

For the acceptance equation, first measure whether ordinary kernel reduction
and staged lemmas can prove this small example. If it is too expensive, expose
and certify a smaller execution trace or use an explicit derivation with a
proved checking rule. Report the measured obstruction; no such cost experiment
was run in this research. An executed check should not silently become an
assumption that downstream users can no longer see.

ConLeche's [public
model](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/Denotes.lean)
provides constant membership, False's emptiness and Eq's meaning. It does not
expose all definition-body and recursor laws as fields. For program computation
preservation, obtain the relevant stronger internal invariant or derive the
required equations through accepted theorem membership. For this proposition
fragment, #127 demonstrates that constructor and eliminator signatures already
yield useful additional meanings. This does not establish preservation of
proof-relevant computational witnesses or higher identity.

The [model-existence
theorem](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/MainTheorem.lean)
remains conditional on `[SetTheory V]` and verified-mode checker acceptance.
The [set-theory
interface](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/SetTheory/Core.lean)
includes a natural-indexed chain of Grothendieck universes. Closing the artifact
bridge does not require proving unrestricted Lean self-soundness, and does not
discharge that stronger model premise. The native restricted interpretation is
still useful independently of this relative route.

## Which upstream kernels actually connect

The supplied report and our experiment concern different pins:

| Component | Report's Lean 4.35 bundle | Existing local experiment |
|---|---|---|
| Lean | `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` | Same version and observed commit |
| ConLeche | `67f04630d88718e81aa4d07ab64501f68f105398` | `8e166ca53cd1f864b63c13cc1d326d38316d00ea` |
| Lean4Lean | `Kha/lean4lean`, `456abe5015fc8f54ea595561fc39523d7733c93f` | `digama0/lean4lean`, `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` |
| ConRon | `dd8d8218892c871276b1e569d3decbb368bba1b6` | Not built or imported |

The ConLeche and ConRon release pins are in Lean's [release build
configuration](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/CMakeLists.txt).
The local pins and independent build/audit evidence are recorded in
[relative-graph-model](relative-graph-model.md#pinned-builds-and-selected-inventories).
ConRon's [proof manifest](https://github.com/leanprover/con-ron/blob/dd8d8218892c871276b1e569d3decbb368bba1b6/proof/lake-manifest.json)
pins the release ConLeche revision. Matching theorem names does not identify the
two versions' expression annotations, checker functions or interpretation
relations. Use a common pin or prove the required translation/refinement before
composing those proofs.

The [#134 alignment record](../../experiments/relative-graph/pin-alignment.md)
verifies that the existing experiment pin `8e166ca` is a strict descendant of
the release pin `67f0463`, so it remains the selected newer revision. ConRon
still needs a coordinated port: its arena interfaces require binder metadata
removed by that revision. No aligned execution-refinement composition is claimed.
Separately investigate distinguishing the host toolchain from the modeled
target version: a library should be able to describe a Lean version without
being compiled by that version. Versioned target judgments, environments and
adapters need explicit compatibility contracts. The operational preference
remains the latest compatible Lean; conceptual separation does not itself
require maintaining multiple build toolchains.

The report's useful claim about ConRon is confirmed by its [maintainer
README](https://github.com/leanprover/con-ron/blob/dd8d8218892c871276b1e569d3decbb368bba1b6/README.md):
an Aeneas-generated Lean model of Rust refines a Lean arena implementation,
which refines ConLeche's pure checker. This preserves successful modeled
checking. It is not a proof of binary execution or universal equivalence with
the C++ kernel. The README explicitly excludes the driver and identifies the
Rust translation as a trust boundary.

Its [capstone theorem](https://github.com/leanprover/con-ron/blob/dd8d8218892c871276b1e569d3decbb368bba1b6/proof/ConRon/Capstone.lean)
makes initialization, reads, parsing, preparation, pin interning, verified
installation, arena freezing and coverage of every pending worker check
explicit premises. The conclusion gives a represented environment and a
ConLeche model. Its embedded-pin specialization additionally records a native
axiom dependency. These are concrete contracts we could consume after matching
the inputs and pins; they do not prove our source-to-core correspondence.

Lean4Lean offers a declarative typing vocabulary and implementation-refinement
work, but it is not currently a completed whole-kernel route under our audit
policy. At the report's [bundled revision](https://github.com/Kha/lean4lean/blob/456abe5015fc8f54ea595561fc39523d7733c93f/Lean4Lean/Verify/Environment.lean),
the inductive case of `addDecl.WF` is admitted. Our separate pinned experiment
found `sorryAx` in the selected type-uniqueness theorem's dependency closure.
Individually audited lemmas may still be reused. Neither observation invalidates
the independently audited ConLeche route.

## An independently designed kernel

Writing a kernel is compatible with the project direction. Its smallest useful
form could be a certificate checker for the growing language fragment, with
explicit typing/conversion evidence and a translation to Lean core. It need not
start by reproducing every acceptance heuristic of Lean's production checker.
The choice to support arbitrary Lean imports would create a much larger
compatibility obligation and should be explicit.

The incoming *Algorithm Design with Haskell* formalization could help derive
the checker from a specification and refine its data structures or algorithms.
The owner reports that it also tackles checking `cqueens 16 = 14772512` through
substantial optimization and Lean kernel work. That supplies a more direct lead
for certified evaluation or kernel implementation. The incoming artifacts have
not been inspected here, so neither that result's trust boundary nor its
performance has been reproduced. Inspect its exact proof and checking strategy,
then assess how to expose reusable operations and refinement laws without
discarding useful existing proofs. One possible connection is:

```text
formal judgment and semantic soundness
  ← certificate-checking specification
  ← terminating or fuelled reference algorithm
  ← optimized representations and implementation
```

Each arrow needs its own theorem. Algorithm derivation does not select the
right typing rules, prove their semantic soundness, establish faithful decoding,
or verify the eventual compiler/runtime automatically. ConRon's arena-to-pure
refinement supplies an existing example of the separation between algorithmic
representation choices and the semantic theorem. A custom checker can make the
interface smaller and its obligations clearer, but is not a prerequisite for
proving the current bounded emitter.

## Proposed next tasks

1. **Prove the bounded emission relation.** Specify the exact primitive
   environment; implement both a pure emitter and proved certificate validator;
   cover all current `Code` constructors, substitution, scopes and universes.
   Connect the theorem to the actual installed artifact. Retain negative
   corruption tests as supplementary evidence.
2. **Join native emission to the relative interpretation.** Generate ConLeche
   declarations from that same artifact family; prove syntactic/environment
   correspondence and formula denotation. Close the concrete acceptance equation
   with kernel-checked evidence, or expose the measured obstacle and the smaller
   certificate needed. Preserve the explicit set-theory premise.
3. **Assess upstream execution reuse separately.** Align ConLeche/ConRon pins,
   audit the exact selected theorem, and specify the relation from our artifact
   to its parsed input. This strengthens execution confidence without delaying
   the source-to-core preservation theorem.
4. **Evaluate a custom checker through one shared algorithm.** After stating
   the fragment judgment, derive one binder/substitution/conversion or checking
   component and compare its contract with upstream infrastructure. Decide on
   broader kernel ownership from that evidence, rather than making it an
   implicit consequence of closing the graph emitter gap.

The first two tasks directly answer the owner's objection. Their semantic
contracts can remain stable while author-facing syntax and implementation
strategies evolve.

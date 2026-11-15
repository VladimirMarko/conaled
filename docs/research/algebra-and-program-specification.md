# Algebraic interpretation and program specification in conaled

Issue [#407](https://github.com/VladimirMarko/conaled/issues/407).
Research inspection: 2026-11-09, local revision
`c34d622cb276ecc2db5ed82e3632c800b4c04567`.

Keep compositional denotation and add execution obligations where a client asks
about execution. The compiler foundations already separate operations from
semantic laws, and the stack backend already connects an independently defined
instruction interpreter to source meaning. A new universal type-theory interface
would not improve that contract merely by renaming it. The missing experiment
is whether an additional observer can be attached compositionally without
weakening existing clients or repeating their compiler proofs.

This report distinguishes **literature** results, **local results** inspected in
integrated source, and **proposals** below. Local results refer to existing Lean
declarations, not a new build performed for this report. No Lean files, host
axioms, proof-audit exceptions, or architectural decisions change here. The
archived [discussion](../history/harper-hott-computational-interpretation.md) is
background; the historical account below was checked against the live primary
thread. #308 and #263 are integrated evidence. Unaccepted #307 fresh-build work
and #309/#408 drafts supply no result used here.

## What Harper and Sterling were distinguishing

In the [complete discussion][discussion], Sterling's March 18 answer gives two
reasons for changing architecture: admitting ordinary mathematical models, and
automating well-formedness with typed normalization and elaboration. He retains
computational interpretation and proof refinement. His follow-up compares the
same invariance lemmas and reports less manual equality work in redtt despite
losing general equality reflection. This is historical author experience, not
a measured conaled productivity result.

On March 19 Sterling distinguishes an unconditional Boolean branch reduction
from the circle eliminator's beta rule: the latter needs typing premises in the
cubical PER interpretation. Harper's reply that day places computation-based
truth and behavioral specification alongside algebraic uses of type theory;
he does not prove their incompatibility. The questioner subsequently asks whether
the tensions are fundamental; Sterling's March 20 reply endorses studying
computational spaces without settling that question. The thread therefore does
not establish that every realizability model excludes geometric mathematics,
that every untyped rule fails cubically, or that programming requires abandoning
typed syntax. Its examples concern admissible principles, equality and automation,
not a pure/effectful classification. [Primary thread][discussion]

## Mathematical commitments that a compiler can expose

**Literature.** The [RedPRL paper][redprl], §2, starts with untyped expressions
and small-step dynamics, then defines types by symmetric, transitive relations
on canonical values. Membership of a program requires evaluation to a related
value; reflexivity holds on the PER's domain, not every raw program. Open
judgments quantify over equal closing substitutions. Theorem 1 gives Boolean
canonicity for semantic membership. Its Boolean Shannon expansion illustrates
extensional equality obtained from those judgments. §3 then supplies proof
refinement for establishing them; semantic truth and automatic decidability are
separate. Exact equality and higher-dimensional paths coexist in the reported
system. These claims concern its described computational type theory, not Lean's
definitional equality or arbitrary runtime programs. [§§2–4][redprl]

**Literature.** [Angiuli, Harper and Wilson, version 2][chtt], §§2–4, build a
dimension-indexed operational meaning explanation with coherence under dimension
substitution and Kan conditions. Theorem 38 (p. 36) gives canonicity for closed,
zero-dimensional Boolean terms in its simple higher-dimensional theory. Its
scope includes function/product types, the circle and the Boolean-negation line
`not` (a particular univalence example); it is not a theorem about arbitrary dependent Lean types or
compiled machine code. Coherence matters because evaluating and then changing
dimensions need not be interchangeable without the required compatibility.
A plain PER over values would omit these obligations. [Introduction and
meaning explanation][chtt]

**Design interpretation.** An algebraic account specifies operations, equations
and admissible interpretations. A computational specification additionally
classifies programs relative to chosen dynamics and observations. These are
questions to ask of a contract, not mutually exclusive data structures: one can
build an algebra whose carriers are behavioral specifications, or prove a
realization theorem for a separately chosen denotation. Their connection must
preserve the equations and observations actually requested.

| Question | Algebraic requirement | Additional program requirement |
|---|---|---|
| Which models are admissible? | An interpretation supplies the fragment's operations and validates its laws. | A realization connects those operations to the selected execution; progress or termination is required only where claimed. |
| What does equality forget? | Equality is the declared semantic equivalence, possibly a quotient or relation. | Every permitted observer respects it; a cost observer may require a finer equivalence. |
| What may be substituted? | Substitution respects the interpretation and its equality. | Related environments must preserve behavioral membership; evaluation order and value restrictions matter. |
| What can automation decide? | A specified conversion or normalization procedure may discharge a fragment of equality. | A proof-producing method must establish the requested execution property; semantic membership alone supplies no general decision procedure. |

The table is a proposed reading discipline, not an equivalence theorem between
PRL and categorical semantics. In particular, the local relational compiler's
arbitrary base relation need not be a PER; calling it a realizability model
would require further hypotheses and a dynamics interpretation.

For the categorical side, the pinned [Felix comma construction][felix-type]
uses two arrows and a commuting comparison over supplied interpretation
homomorphisms. Its [projection homomorphisms][felix-hom] preserve category
structure. The code supports compositional comparison without asserting that
every morphism executes, every interpretation reflects equality, or every
semantic equivalence preserves resource observations. The local
[Felix implementation record](felix-parity-implementation.md) documents the
broader port, but only inspected local declarations below support this audit.

## What the current compiler routes establish

| Inspected source and declarations | Established contract | Boundary |
|---|---|---|
| [Compiler.lean](../../Compiler.lean), `Target`, `Sound`, `compile_sound` | Every intrinsically typed product/function/sum/let/primitive source term compiles through the supplied operations; its chosen Set-valued target denotation equals `eval` under local operation squares. | `Sound` is an assumption package, not a faithful Set interpretation for every category. No small-step semantics, termination or contextual reflection follows from this theorem alone. |
| [FirstOrder.lean](../../FirstOrder.lean), `Target`, `Sound`, `compile_sound` | The analogous result for ground/unit/products and primitives, requiring cartesian operations without closure. | An executable backend must still implement its primitives and satisfy its additional execution contract. |
| [FirstOrderNaturality](../../SquareKit/FirstOrderNaturality.lean), `cartesian_naturality`, and [STLCNaturality](../../SquareKit/STLCNaturality.lean), `naturality`, `naturality_comp` | Structure-preserving maps transport compilation; composed maps reuse the argument. | Forward preservation is not reflection. It does not imply raw-code equality or full abstraction. |
| [Stack machine](../../Applications/Stack/Machine.lean), `runInstr`, `run`, `Certified.correct`, `compile_correct` | Independent typed instruction interpretation produces the source value and preserves every tail, for all inputs and supplied primitive meanings. `run_append` supports sequential composition. | Finite first-order bytecode with total host-function primitives; no closures, external native execution, wall-clock bound or general divergent machine. |
| [STLCRelations](../../SquareKit/STLCRelations.lean), `Encoding.arrow`, `Primitives.correct`, `compile_preserves` | Higher-order implementations preserve relations on every related argument, with matching sum tags and captured environments. | No decoder from arbitrary runtime functions, no definability of every host function, no contextual-equivalence reflection. |
| [Graph emission](../../SquareKit/Internal/GraphEmissionContract.lean), `ArtifactDenotes.sound`, `emit_denotes`; [typing](../../SquareKit/Internal/GraphEmissionTyping.lean), `emit_typed`; [composition](../../SquareKit/Internal/GraphEmissionSquares.lean), `source_emission` | A bounded graph proof declaration emits exact core expressions with separate typing and meaning derivations; composition retains the source contract. | Neither extracting an executable witness from arbitrary `Prop` proofs nor verifying Lean's compiler/runtime. Fragment typing is not a universal checker-acceptance theorem. |
| [WeakMachine adequacy](../../SquareKit/WeakMachine/Adequacy.lean), `fundamental`, `return_denotation`, `divergence_denotation`, `context_returns`, `context_divergence` | Related closing substitutions connect syntactic call-by-value execution to the independent partial denotation. At closed ground type, returns and divergence agree; supported contexts preserve these observations under open denotational equality. | The fragment has literals, functions, application and explicit omega. Divergence proof uses a finite path to an active self-loop, not arbitrary recursion. No full-abstraction theorem. |
| [Memoization cache](../../Applications/Memoization/Cache.lean), `Storage.call`, `call_correct`, `repeat_hit`; [Fibonacci](../../Applications/Memoization/Fibonacci.lean), `correct`, `repeated` | Actual cache execution retains correct stored results; a repeated successful call bypasses the body. Costs distinguish hits, body evaluations, read visits and written path nodes. | Representation equivalence alone gives neither retained reuse nor these counters. Concrete storage traversal supplies them; they are not Lean allocation or elapsed-time measurements. |

The graph route also has translation validation and checked native callers;
its [implementation account](graph-emission-implementation.md) describes exact
primitive-environment checks and installation. This is evidence about the
bounded emitted artifacts, not a replacement for the independent execution
bridge a new compiler target would require.

Use terminology with its equation attached. Here **adequacy at ground type**
means agreement between named execution outcomes and denotation.
**Simulation** would relate machine configurations and match steps, possibly
with a separately controlled stuttering policy. **Full abstraction** would be
an equivalence between denotational equality and contextual equivalence for a
specified source/target context language and observer. The listed naturality,
relation-preservation and context theorems do not establish that biconditional.
The #308 runner's timeout is also not a divergence observation; finite fuel can
expire before an ordinary terminating redex finishes. See its
[scope and examples](weak-operational-machine.md).

## One compiler client, independently specified three ways

Use the existing `MatrixCompiler.linearCombination ℕ` client, not a second
source language invented to favor either account.
[MatrixStack](../../Examples/MatrixStack.lean) already supplies its checked
specialization and the quantified comparison for arbitrary source terms.

* **Denotation:** `F(x,y) = 2*x + 3*y`, from the source `eval` and primitive
  arithmetic meaning. Matrices interpret this as finite coordinate sums.
* **Execution:** `StackMachine.run` recursively executes the generated typed
  instruction sequence using `runInstr`; it is defined without calling `eval`.
* **Observations:** observe the returned number and the unchanged arbitrary
  stack tail. For a proposed finer experiment, also observe instruction count.
  The latter must be specified from instruction execution, independently of `F`.

The algebraic account uses `compile_sound` and matrix interpretation to prove
that the compiled denotation is `F`. The program-specification account uses
`Certified.correct` to connect the generated sequence to that denotation.
`compile_correct` composes these proofs. Existing
`linear_example_with_tail` gives `(2*x + 3*y, (z, ()))`, and
`agree_preserving_tail` equates stack output with decoded matrix output for
every typed source term and arbitrary tail. This is a combined contract already
available to ordinary Lean callers, not a proposed PER implementation.

**Negative control, proposed.** For any generated program with output type `a`,
append `dup; swap; swap; fst`. These instructions preserve the result and tail:
the duplicated pair is swapped twice and projected back. Under the experimental
unit-per-instruction observation, they add four steps. Denotational equality
therefore cannot establish an exact instruction budget or an optimization claim.
The report does not claim this new control is already formalized. An even weaker
specification observing only the top value would permit arbitrary tail changes
in an unconstrained implementation; the actual `Certified.correct` contract
explicitly rules those out.

There is also an existing checked negative result at higher order:
[WeakHigherOrder](../../SquareKit/WeakHigherOrder.lean), `redex_equal`,
`strong_distinguishes`, `no_strong_adapter`, identifies a literal and its identity
redex denotationally while distinguishing counted behavior. Its
`unrestricted_beta_fails` shows why erasing an unused omega argument under
call-by-value changes termination. This is a failed applicability condition for
unrestricted beta, not evidence that the existing total CCC compiler is wrong.
The partial fragment requires its own value-sensitive contract.

## Optional interfaces and theorem sketches

**Proposed mathematical signatures; not Lean declarations.** Keep `Target`,
`Sound`, naturality and relational squares. For a selected backend with syntax
`Code a b`, state independent `denote : Code a b → D a → D b`, configurations,
`Exec c input output`, and relations `InputRel input x`, `OutputRel output y`.
The following two obligations deliberately differ:

```
execution_sound:
  InputRel i x → Exec c i o → OutputRel o (denote c x)
execution_total:
  InputRel i x → ∃ o, Exec c i o
compiled_execution:
  InputRel i x → ∃ o, Exec (compile t) i o ∧ OutputRel o (eval t x)
```

The third follows from the first two and `compile_sound`; it must not be
inferred from the first alone, since an execution relation with no runs satisfies
soundness vacuously. For partial code replace `execution_total` by an explicitly
chosen adequacy contract, such as the #308 return/divergence equivalences. Do
not force every analysis backend or partial language to prove totality.

For the stack specialization, take `Exec c i o` to mean `run c i = o`, retain
inputs and tails in `InputRel`, and require the same tail in `OutputRel`.
This recovers `compile_correct` directly; defining this relation around `run`
is adequate for that interpreter but does not claim an independent small-step
machine proof. A future transition machine must prove its own relation to `run`.
For matrix compilation retain the existing finite-sum interpretation. For
`ArithmeticPipeline.stack_after_update` and `stack_enclosed`, expose the same
stack value/tail contract so the current exact and relational compositions
remain usable. For `STLCRelations`, use related inputs at arrows rather than
postulating a function decoder. For graph emission retain `ArtifactTyped` and
`ArtifactDenotes`; an execution adapter is inapplicable until an executable
artifact and observer are specified.

Sequential composition needs an intermediate-state compatibility theorem:
executing `c` then `d` realizes `d ∘ c`, and the output relation of `c` supplies
the input relation of `d`. `run_append` plus `Certified.comp.correct` already
provides this for stacks. A resource extension can use
[Measured](../../Applications/Resources/Measured.lean) composition over an
additive cost monoid, but must prove that the counters arise from the selected
execution. Preserve the value theorem by projecting away costs. An observer
transport `obs₂ = h ∘ obs₁` permits forgetting information; reconstructing
`obs₁` from `obs₂` needs another theorem and may be impossible, as
`no_strong_adapter` demonstrates.

For actual memoization, `Storage.call_correct` and `repeat_hit` are better
starting points than a representation isomorphism. A compositional cache client
must thread the valid retained state and count the actual body/read/write
operations. Reusing #263 avoids proposing memoization as an unimplemented
consequence of extensional equality.

## Discriminating experiment and adoption decision

Propose a bounded follow-up under #235, coordinated with #8/#200/#36 and the
completed #209 methodology study. Coordinate computational-meaning and
equality/cost investigations #394/#399/#400/#406 through their actual contracts;
none is assumed to have supplied an accepted theorem here.

Freeze the existing matrix/stack linear client and arithmetic stack composition
as baseline clients. Implement a counted instruction executor with a projection
theorem to `run`, an append theorem, and the four-instruction control above.
Compare direct proofs using `Certified.correct` against the optional execution
adapter on exactly those claims. Add one application of #308's existing
related-input theorem to ensure the proposal does not force totality or decode
arbitrary higher-order values. This is a test of compatibility across fragments,
not a request to unify their syntax or implement cubical realizability.

Acceptance requires all of the following:

1. Recover the old quantified value/tail theorems without changing ordinary Lean
   call sites; no loss of interval enclosure or matrix/stack agreement.
2. Establish counted execution composition and the padding control for arbitrary
   inputs, with a named unit-cost policy. Exact output equality must coexist
   with unequal counts; reject an adapter claiming cost equality from value
   equality alone.
3. Demonstrate a client-level resource bound derived through the adapter, and
   compare it with the direct proof of the same bound. If the adapter merely
   packages the conclusion as a field or duplicates syntax induction for each
   client, do not adopt it as shared infrastructure.
4. Record setup declarations, repeated client obligations, proof repairs and
   available agent time/token data separately. No productivity advantage is
   established by the present source inspection. A more complicated adapter
   with no repeated proof saved is a valid negative outcome.
5. Run statement review, checked specializations, relevant runtime tests for the
   counted executor and the README build/proof audit when implementing. This
   documentation-only investigation performs none of those formal changes.

No ADR revision is warranted by the inspected evidence. ADRs
[0002](../adr/0002-relations-and-synchronization.md) and
[0006](../adr/0006-stack-machine.md) already retain the relation and arbitrary-tail
obligations. The [language direction](../language-direction.md) prefers
independent compositional denotation and explicitly assigns operational semantics
an implementation, adequacy and resource role. The proposed experiment follows
that division while allowing a computational model to challenge the selected
laws. Felix's compositional comparison remains shared; observation, termination,
state retention and cost stay explicit contracts. A future migration needs a
repeated author failure or a theorem that current interfaces cannot express,
not Harper's historical distinction by itself.

## Source receipts and inspection limits

Primary sources were retrieved on 2026-11-09. Their URLs, versions and paper
checksums are recorded below.
The discussion is mutable; its dated comments and anchor identify the historical
claims. Paper versions and Felix revision fix the technical scope. No copied
historical transcript serves as proof evidence.

* [Discussion #186][discussion], all displayed comments and replies, including
  Harper's March 19 reply `discussioncomment-501404`.
* [Computational Higher Type Theory I][chtt], arXiv `1604.08873v2`, 14 June 2016.
* [The RedPRL Proof Assistant][redprl], author-hosted LFMTP 2018 paper, especially
  Figure 1, §2 Theorem 1, §3 and §4.
* Felix commit `6f36d28097db7ea5f5df3263db3e8be08f74e490`,
  [`Construct/Comma/Type.agda`][felix-type] and
  [`Construct/Comma/Homomorphism.agda`][felix-hom].

Downloaded paper SHA-256 receipts are
`70d4438a2ba8c53077e4af27556f28d2337c97a3b7ef034a4efa623d9979d68d`
(CHTT I v2) and
`9826bfd60294ae2024c07a14669afb3c521f90fe6db73d74120282d0abe673b8`
(RedPRL). These identify retrieved bytes, not independent verification of claims.

This report does not reproduce the cited papers' metatheory, establish a PER
model of conaled, measure author productivity, prove full abstraction, or audit
external native execution. These are omitted claims with concrete missing
obligations above, not prerequisites for retaining the existing compiler APIs.

[discussion]: https://github.com/RedPRL/cooltt/discussions/186#discussioncomment-501404
[chtt]: https://arxiv.org/pdf/1604.08873v2
[redprl]: https://www.cs.cmu.edu/~rwh/papers/redprl/lfmtp18.pdf
[felix-type]: https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda
[felix-hom]: https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Homomorphism.agda

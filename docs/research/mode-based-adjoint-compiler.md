# Two-mode adjoint compilation

Issue [#352](https://github.com/VladimirMarko/conaled/issues/352) implements a
bounded multiplicative fragment with unrestricted mode U above linear mode L.
A resource-sensitive model supports an actual shift adjunction, and local
primitive certificates imply whole-program resource and selected-payload
preservation. A two-pass client expands unrestricted arithmetic before using
its result in a linear update. It returns the selected value `12`, retaining
one unit of linear resource.

## Source discipline and chosen fragment

Pruiksma, Chargin, Pfenning and Reed's [Adjoint Logic, §§2–3](https://www.cs.cmu.edu/~fp/papers/adjoint18b.pdf)
requires a preorder of modes, monotone weakening/contraction permissions, and
independence: a conclusion can depend only on hypotheses at higher modes.
Its explicit and implicit structural presentations distinguish tensor's split
context from additive conjunction's shared context. The shifts form an
adjunction. Their Example 2 identifies invalid promotion of a linear
hypothesis to U as a route to unsound contraction.

Jang, Roshal, Pfenning and Pientka's [Adjoint Natural Deduction, §§2–7](https://arxiv.org/html/2402.01428v1)
separates bidirectional typing, its sequent-calculus correspondence, a machine,
and algorithmic resource management. Preservation/progress are not termination
theorems. The garbage and strictness results concern closed computations that
terminate at purely positive result types. Section 6 adds recursion; §7 needs
more than the bidirectional rules to decide context splitting. None of those
machine theorems is imported into this implementation.

Our independent source is [`Ty` and `Term`](../../SquareKit/AdjointModes/Syntax.lean).
It has unit, tensor at L, product at U, symmetry/association, composition,
U-only copying/discarding, both shifts, their functorial actions, unit/counit,
and the strong monoidal downshift operations. Typed primitive signatures are
parameters. There are no function spaces, sums, additive conjunction, recursive
syntax, dependent types, or named-variable elaboration. This is a combinator
presentation of the chosen fragment, not a formalization of either complete
paper calculus or a proved equivalence with its natural deduction.

The context of a combinator is its domain object. Tensor combines distinct
input components; it does not feed one L input to two branches. At U a product
can be copied or discarded explicitly. A mixed L context contains downshifted
U components alongside L components. `downMap` only accepts a U computation.
`upMap` changes both endpoints of an L computation to U; it cannot promote a
live L input into a U conclusion. The only unit starts at U. Thus the mixed
client can use U data inside L without granting L data U's permissions.
`Above`, its reflexivity/transitivity, `permissions_monotone`, and the negative
policy cases state the fixed two-mode policy separately. There is no parameter
allowing a caller to replace it silently while retaining this source syntax.

## Independent resource meaning and shift adjunction

[`Resources`](../../SquareKit/AdjointModes/Resources.lean) models an L object as
a type with a natural-number degree. A morphism is a function preserving that
degree exactly. Tensor adds degrees and its unit has degree zero. U consists
of ordinary types and functions. `down X` places X in degree zero; `up A` is
the zero-degree fiber of A. The model is specified without reference to the
compiler or the syntax of programs.

`shiftAdjunction` constructs

```
Map (down X) A ≃ (X → up A).
```

Both naturality equations and both triangle equations are checked. Source
`Term.transpose` and `Term.untranspose` use the restricted unit/counit and
functorial shift rules. Their compiled round trips are identities;
`transpose_compiles` identifies the source construction with this hom equivalence.
[`Category`](../../SquareKit/AdjointModes/Category.lean) packages these data as
Mathlib functors and an `Adjunction`. `compare_right_adjoint` reuses the existing
`AdjointComparison.curry` theorem to compare any other chosen right adjoint.
This makes the boundary usable by the existing categorical infrastructure;
merely declaring two oppositely directed maps would not have sufficed.

The degree-one atom has inhabitants but admits neither a map to its tensor
square nor a map to the tensor unit: those would require `2 = 1` or `0 = 1`.
It also admits no function to its zero fiber, rejecting the invalid promotion
semantically. `no_generic_linear_copy` and `no_generic_linear_discard` use the
compiler's sound interpretation to refute source terms with an empty primitive
signature. These are counterexamples to generic operations, not claims that
no particular linear object can be copied or discarded. `copyDown` and
`discardDown` exhibit such operations on downshifted objects. The examples
also accept U copying/discarding and reject both an indiscriminate mode order
and reversed structural permissions.

Degree is a resource model, not a measurement of Lean allocation or proof of
pointer uniqueness. The model allows supplied operations with nontrivial
payload behavior so long as their input/output degrees agree. An operation
that consumes one resource and returns another can satisfy this contract;
identity of physical resources would require a richer observation.

## Compiler passes and selected results

[`Compiler`](../../SquareKit/AdjointModes/Compiler.lean) separates two meanings:
`Term.denote` interprets selected payloads by ordinary functions;
`Term.compile` builds certified resource maps by structural recursion.
`Ty.forget` removes degree certificates while retaining payloads. An author
supplies each primitive's resource-preservation proof and a payload commuting
equation. `compile_preserves` derives that equation for every source term;
`resource_sound` derives exact degree conservation. Neither conclusion assumes
whole-program preservation as an input.

[`Translation`](../../SquareKit/AdjointModes/Translation.lean) replaces each
primitive by a typed program. `translate_preserves` extends local replacement
certificates to all programs. `translate_identity` and `translate_comp` give
literal source-tree identity and composition laws. `Term.square` exposes the
compiler result through the existing `Squares.Square`; `square_identity` and
`square_comp` recover its existing composition interface.

The [client](../../Examples/AdjointModes.lean) specifies `addDouble(n,x) =
(n+n)+x` followed by `finish(x) = x+1`. Here `n` is unrestricted and `x` is a
linear payload. The first pass replaces `addDouble` by a U doubling operation
and a linear addition primitive. The second replaces doubling by U copying
and addition. Both passes change syntax; neither is an identity wrapper. The
final program sends the L input through one linear addition and then one
successor, while copying only the U argument. `pipeline_preserves` derives
correctness for every source term, not just this client. `selected_result`
uses that theorem to retain `12` for `(3,5)`. `selected_resources` retains degree
one. The source grammar and the explicit expanded client account for linear
input threading; the degree theorem alone is not an operational use-count
proof.

The direct contract baseline is `directClient`: one resource map for
`(n,x) ↦ (n+n)+x+1` and its degree proof. `compiler_agrees_direct` identifies the
compiled map with it. For this one client, the direct interface is much shorter.
The mode layer additionally rejects unavailable structural operations, supports
compositional primitive expansion, and derives whole-program obligations.
This experiment does not establish an agent-productivity advantage.

## Scoped execution and equality

[`Evaluation`](../../SquareKit/AdjointModes/Evaluation.lean) defines a big-step
relation independently from `Term.denote`, with separate rules for composition,
tensor, shifts and primitive evaluation. `Eval.sound`, `Eval.complete`, and
`Eval.deterministic` prove agreement and uniqueness for the finite fragment.
`compile_evaluates` connects resource compilation to that relation, and
`selected_evaluation` recovers the concrete output. Primitive meanings here
are total functions. Completeness is therefore scoped to finite combinator
syntax with those functions; it says nothing about recursion, divergence,
lazy environments, garbage collection, or the source paper's abstract machine.

All displayed commuting equations use Lean equality of selected payloads or
functions. Resource maps additionally preserve the stated degree. The syntax
has no equation quotient, and preservation does not reflect semantic equality
back to syntactic identity. Source-tree identity/composition, categorical
adjunction, resource conservation, big-step evaluation, and denotation
preservation are distinct checked statements.

## Interface comparison and next use

| Interface | Obligations for this client | What it gives |
|---|---|---|
| Separate U functions and L resource maps | Direct update and degree proof; caller connects any transfers | The smallest contract for one update; no source-level permission checking or generic pass extension |
| Per-mode interfaces plus shifts | Down/up hom equivalence and naturality; typed primitive meanings and local compatibility | Mixed computations, checked forbidden operations, whole-program preservation, compositional passes, ordinary square reuse |
| Maximal unified logic package | Would additionally request function spaces, additive rules, recursive evaluation or dependent structure | No exercised benefit here; those obligations should belong to future clients that use them |

The small shift extension fits this experiment. Its categorical bridge can
participate in #351's adjoint comparisons without identifying resource policy
with categorical quantifier transport. #297's lock calculus still owns a
different dependency problem. The compiler need not replace existing squares
or institutional capabilities to use this layer.

Under #36/#290, a next consumer should justify a named-context elaborator or
additional connective before it is added. Under #235, compare incremental
primitive-authoring effort only after choosing a repeated compiler extension.
A future runtime ownership client must strengthen the resource observation
and prove its own operational contract. #108 and #107 remain untouched.

## Statement review and checked cases

- Policy results quantify over the fixed two modes and both permissions. The
  malformed order and malformed permission assignment genuinely contradict
  monotonicity; they are not rejected by an unrelated typing error.
- Resource maps conserve degrees for every input. The atom countermodel has
  an explicit inhabitant, so its impossible morphisms are nonvacuous. The
  shifted-U positive cases prevent overreading the negative results.
- The adjunction covers every type X and every resource object A in the stated
  universe. Naturalities and triangles are literal map/function equalities;
  the Mathlib adapter reuses the same hom equivalence.
- Compiler and pass preservation quantify over every term of the fragment.
  The only supplied correctness assumptions are local primitive contracts.
  The selected `(3,5) ↦ 12` case exercises both expansion passes and the final
  resource compiler. The direct baseline checks the independently stated
  arithmetic specification.
- Evaluation is deterministic and total only in the finite, total-primitive
  fragment. It preserves selected values; it does not infer heap behavior from
  the degree model.

The integrated example imports all six supporting modules into the normal
build and exhaustive proof audit. Validation records for the immutable
candidate are supplied with the implementation review.

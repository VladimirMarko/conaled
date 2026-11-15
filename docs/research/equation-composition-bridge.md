# Equation views and finite composition

Issue [#277](https://github.com/VladimirMarko/conaled/issues/277) connects a
bounded fragment of `EquationTranspose` to `IndexedCompositional.Rule`.
The bridge generates a local rule from one authored equation table, and proves
that transposing the table produces exactly the same rule. Semantic
compatibility with an independently defined algebra is still required.

## Supported cells and their boundary

The selected fragment has output cells and request-indexed successor cells.
Constructor fields contain the immediate outputs of its children. An output
cell returns the constructor's output. A successor cell returns a finite
`Term` whose leaves name either an original child (`Slot.ret`) or a requested
successor of a child (`Slot.succ`). Its result sort is `Behavior.next j r`.
Neither a concrete child representation nor its future observations are an
input to an output cell.

The equation index packages the result sort and operation because the type of
successor slots depends on that operation. The request belongs to the observer
name because the result sort depends on the request. `ULift` accommodates the
equation calculus's uniform universe without erasing these dependencies.
Primitive interpretations are total and separately supplied. Expressions retain
the existing binding-free variables, products, projections, and primitive
applications. Binding, local matching, recursive definitions, arbitrary parser
inspection, and automatic recognition of suitable foreign primitives are outside
this translation.

This boundary was selected from the existing interfaces: `EquationTranspose`
allows primitives over full parsers and vectors, whereas `Rule.out` receives
only immediate child outputs. The bridge therefore does not claim to compile
every original equation program. The parser instance covers union and scalar
evidence; concatenation, star, and snapshots keep their existing APIs and proofs.
The vector instance covers nil, cons, and pointwise doubling. Its successor
cells use literal finite templates; their leaves still carry checked indices.

## Checked recovery

[The shared bridge](../../SquareKit/EquationComposition.lean) evaluates supported
cells to obtain `Rule.out` and `Rule.step`. `compile_transpose` proves equality of
the complete rules extracted from the column and row presentations, for every
primitive interpretation. Equality includes output values, template syntax,
original-child references, requests, and successor sorts. It consequently
preserves every lifted interpretation.

`observations` then applies `Rule.fold_morphism` and `Behavior.observe_morphism`
to arbitrary finite terms and typed paths. Its hypotheses are local
compatibility with the independent algebra and a morphism for the leaves.
There is no hypothesis asserting correctness of the desired composite.
Transposition alone supplies neither of those semantic hypotheses.

[The vector specialization](../../Examples/IndexedCompositional.lean) now
generates its public `rule` from equations. The independent meanings remain
`Fin n → Nat`, constructor insertion, and pointwise multiplication by two.
Its existing compatibility, coordinate, substitution, and incorrect-rule
counterexample proofs still check. [The bridge examples](../../Examples/EquationComposition.lean)
recover the original equation-table head observation, retain the original tail
at its exact length, and obtain 22 from the second coordinate of
`double (cons 7 (cons 11 nil))` through `observations` after transposition.

[The parser specialization](../../Applications/Languages/EquationComposition.lean)
proves compatibility with both the native parser algebra and finite witness
tries. `original_union_output`, `original_union_next`, `original_scale_output`,
and `original_scale_next` identify the compiled cells with the existing
`Transposition.equations` cells, interpreting successor slots through native
parsers. `recovered` proves exact `Decision` equality at every bounded word of
an arbitrary finite mixture. A checked union of two scaled atom parsers selects
the left branch's scalar 7, rather than the other successful branch's 11, both
in the trie fold and in the transposed rule interpretation.

## A source cell the rule cannot express

The existing vector `at` primitive can read the second coordinate of a child.
If that observation is demanded as a constructor's immediate output, while the
child exposes only its head, it cannot be implemented by this rule format.
`second_coordinate_not_local` proves that no function of the head gives the
second coordinate of every two-element vector: `(0,0)` and `(0,1)` have the
same head and different second coordinates.

The missing obligation is factorization of the proposed output through the
child-output block. A request followed by an observation can read that
coordinate, but changes the requested contract from an immediate output to a
path. Enlarging the output interface is another possible change. Neither is an
automatic consequence of transposing the source expression. This is an
interface mismatch relevant to [#235](https://github.com/VladimirMarko/conaled/issues/235),
not a reason to replace ordinary vector or parser APIs.

## Author obligations and remaining duplication

Previously, equation views and compositional rules were authored separately.
In the vector specialization the hand-written `Rule` cases have been removed:
one table supplies the source view, its transposed row view, and the rule.
The parser fragment likewise supplies all three from one table. Neither
specialization writes a second row body or a second local rule body.
The original broader equation tables remain as independent API implementations
and recovery references; this change does not remove all repository duplication.

An author still provides the signature, primitive vocabulary and interpretation,
independent algebra, and local compatibility proofs. Writing typed expressions
and lifted values adds notation compared with a direct `Rule` definition.
The bridge is useful when both equation presentations and composition are
wanted; a caller needing only native parser operations gains no obligation to
use it. The checked results establish exact semantic recovery, not reduced
runtime work, sharing, or a general compiler for arbitrary Lean definitions.

# Indexed constructor–destructor transposition

Implementation of [#256](https://github.com/VladimirMarko/conaled/issues/256).
The bounded calculus transforms typed equation syntax between observer-grouped
and constructor-grouped programs. It proves both syntactic inverse laws and
preservation of every interpreted cell. It does not identify arbitrary data
values with arbitrary codata behaviors.

## Source account

Elliott's [language derivatives paper](https://conal.net/papers/language-derivatives/paper.pdf),
§§4.2–4.3, Figures 5–9, organizes the same equations around observers in the
symbolic representation and constructors in the automatic representation.
The language index retains parse witnesses. Concatenation keeps its original
right operand; nullable star needs empty-parse evidence. Figure 8 disables
termination checking for concatenation; Figure 9 introduces sizes. Our finite
observations do not establish the infinite implementation's productivity.

Ostermann and Jabs's [2018 GADT transposition calculus](https://ps.informatik.uni-tuebingen.de/publications/ostermann18dualizing.pdf),
§§2–4, Figures 4–6, gives each cell its constructor and destructor parameters.
Enclosing function binders do not scope into these cells. Lemma 3 and Corollary 1
connect matrix preservation to typing and reduction preservation. Its types use
explicit applications and index unification; local/deep matches are excluded.
Adding a row requires checking its new equations, not an assumption that all
extensions preserve old guarantees.

Binder, Jabs, Skupin and Ostermann's [2020 local-match calculus](https://ps.informatik.uni-tuebingen.de/publications/ostermann20decompositiondiversity.pdf),
§§5–7, adds explicit captures and uses de Bruijn variables in its formalization.
Its transformation combines lifting, transposition and inlining. Inversion is
modulo declaration/case ordering and, with named variables, alpha-equivalence.
The paper discloses unmechanized well-formedness obligations in §7; we have not
replayed its Coq artifact. Combining local matching with the earlier polymorphic
calculus remains future work in §8. Neither paper supplies automatic termination
or a general dependent-language transformation.

## Selected calculus and admissibility

[EquationTranspose.lean](../../SquareKit/EquationTranspose.lean) has an index
family `I`. At each index it supplies constructor names, observer names,
constructor field types, observer argument types and observer result types.
An equation is required for every constructor/observer pair at that index.
Index-incompatible pairs have no slot. This is intrinsic Lean indexing, not an
implementation of GADT unification or a parser for an external language.

Each cell has two typed variable blocks. Products or dependent pairs may be
packed into a block. `Expr` contains variables, named unary primitives, pairing
and projections. Primitive names and their interpretations are separate.
Primitive applications include the constructor and observer calls used in the
examples. There are no cell-local binders, local matches, mutually recursive
program definitions, or implicit captures. Terms are finite inductive trees;
evaluation terminates structurally given total primitive interpretations.
A signature may have a parameterized family of names; no finite enumeration
or inference procedure is claimed.

`DataProgram` stores observer definitions with constructor cases. A data value
is a tagged constructor with its fields. `CodataProgram` stores constructor
methods with observer cases. A codata value supplies its observations. The
transformation swaps the two groups and recursively renames every variable in
every syntactic body. It preserves the primitive applications and projections;
it does not replace cells with opaque semantic functions.

The equality is Lean equality of intrinsically typed syntax and extensional
equality of the indexed tables. Names are indexed keys, so there is no list
ordering quotient. Variables are positional and there are no local binders, so
there is no alpha-equivalence quotient. `Expr.swap_swap` proves the renaming
involution; `untranspose_transpose` and `transpose_untranspose` lift it to both
program organizations. `transpose_preserves` follows from `eval_rename` and
agreement of the exchanged environments. Result values, including parse
witnesses, remain equal, rather than merely having equal Boolean erasures.

The calculus is intentionally separate from `CategoricalCompiler.Term`: that
syntax has one base type and a fixed type grammar. Here an equation's result can
be a parser at a derivative language index, or a decision over a particular
witness type. The new syntax is a small application-specific multi-sorted
fragment, not a replacement compiler frontend or a universal AST. It reuses
ordinary Lean products, dependent sums and equality and imports the existing
square foundation. Interpreting cells in settings other than total Lean types
requires another explicit model and preservation contract; no such portability
is inferred from this experiment.

## Checked applications

[Transposition.lean](../../Applications/Languages/Transposition.lean) reifies
union, concatenation and star, with nullable, character derivative and finite
snapshot observations. Its derivative equations expose sum, scale, construction
and witness transport as syntax. The concatenation body uses the unchanged right
operand. The star body retains the empty-parse list in `scaleEmpty` and uses the
existing proved `derivativeStarIso`.

`equations_correct` relates the source cells to existing symbolic operations.
`methods` is generated by `transpose`, not written independently.
`methods_correct`, `recovered_nullable` and `recovered_derive` recover the exact
symbolic results. `recovered_snapshot` recovers the selected parse decision for
all words within the requested finite depth. `concat_automatic` and
`star_automatic` connect these observations to #255's direct trie combinators.
The snapshot cell calls the already verified finite `unfold`; this experiment
does not derive that recursion from syntax or produce an infinite trie runtime.

[EquationTranspose examples](../../Examples/EquationTranspose.lean) additionally
use vectors indexed by length. Empty, cons and repeat constructors have different
field types; lookup accepts `Fin n`. The head/tail example expects 7 and 11 in
that order, and an empty-vector lookup has an impossible argument. A checked
syntax equality verifies that both parameter blocks move. Unlike parser cells,
the lookup body actually uses both blocks, so a broken observer-argument swap
would not be hidden by unused arguments. Both program inverse laws are exercised.
The parser cases preserve concatenation syntax and distinguish the empty nullable
star witness list from a singleton list.

## Extension and statement review

Adding a constructor adds one equation per existing observer. Adding an observer
adds one equation per existing constructor. `restrictConstructors` and
`restrictObservers` describe the two boundaries independently; their cell laws
show that transposition retains the old equations. The vector examples recover
the repeat-only constructor fragment and the lookup-only observer fragment.
These are conservative additions of cells when old bodies are retained. Changing
a primitive's interpretation can change old behavior and needs its own proof.

Statement review checked the following boundaries:

- Renaming and inverse laws quantify over arbitrary primitive syntax and every
  well-typed expression; they do not assume semantic equality to prove syntax
  equality. The table inverses use function extensionality.
- Preservation fixes a total primitive interpretation and compares the same
  constructor fields and observer arguments in reversed environments. It is an
  exact denotational equality, not operational simulation or a cost theorem.
- Parser result types retain the language and word indices. Snapshot lookup has
  the explicit length bound; neither the proof nor an erased Boolean decision
  asserts unbounded storage or enumeration of all parses.
- Vector indexing excludes nil at a positive length and lookup arguments at
  length zero. The example is a one-layer constructor interface whose tail is
  a finite function, not a newly proved recursive vector compiler.
- Exhaustiveness is enforced by the total indexed table field. Termination is
  structural for cells; all recursion inside parser/trie primitives is inherited
  from their existing checked definitions. No termination override or new axiom
  is introduced.

The old #255 finality theorem alone would not discharge these obligations:
this increment contains the expression grammar, variable transformation, syntax
inverses and explicit transformed derivative clauses.

## Remaining scope and architecture handoff

The unsupported top-level parser constructors are zero, universal, epsilon,
atom, intersection, scale and arbitrary transport. They may occur inside operand
parsers, and some are primitives in equation bodies, but they do not yet have
rows in this reified signature. Extending the row inventory requires reifying
and checking their equations. It does not require revising the shared transpose
proof. #8 owns that remaining language-derivative coverage; it is not a claim
that the entire ten-constructor source program has been transformed.

#36/#200 retain local/dependent binders, index-unification algorithms, recursive
source calls and changes of semantic setting as broader research. These need
explicit scoping, substitution, equality and recursion contracts before extending
this fragment. #235 owns evaluation of whether this typed equation interface
should connect to the shared internal-language machinery. No retrofit is justified
by this one experiment, and no new universal preservation family is asserted.

The author used the existing parser equations and #255's public proofs. The new
work was the variable permutation proof, table organization and explicit cell
reification. Lean needed universe lifts for decisions because parsers inhabit a
higher universe; those lifts do not erase witnesses. Rewriting through concrete
signature projections sometimes required `erw` or an explicit equality chain.
These are encoding/elaboration costs, not evidence against the duality. Reusing
the fixed-base STLC would instead require an indexed type extension or packing
away the very result indices being tested; that retrofit is deferred rather
than weakening the examples. This is a single Codex author experiment on the
pinned Lean toolchain, not an independent usability study. Exact model build and
per-task token cost were unavailable; weekly allowance was 11% at task start.

The subsequent [duality findings and language agenda](duality-language-directions.md)
separates the stronger semantic hypotheses and speculative connections from this
bounded result. #266 now owns the omitted parser rows and verified-view author
experiments; #267–#270 own observation extensions, composition laws, pairings and
symmetric proof-syntax assessment.

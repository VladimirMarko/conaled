# Indexed constructor–destructor transposition

Implementation of [#256](https://github.com/VladimirMarko/conaled/issues/256),
extended with parser coverage and authoring routes in
[#266](https://github.com/VladimirMarko/conaled/issues/266).
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
all ten constructors of the existing `Parser`: zero, universal, epsilon, atom,
union, intersection, scale, concatenation, star and arbitrary transport. Each
has nullable, character derivative and finite snapshot observations. Its derivative equations expose sum, scale, construction
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

#266 completes the omitted top-level parser rows without changing the existing
union/concat/star bodies or the general recovery proofs. The coverage is of
one-layer typed equations over the current parser API. Recursive parser calls
remain interpreted primitives; extending this coverage does not establish a
recursive source transformation. The original `Parser` and `WitnessTrie` APIs
remain available directly. #8 retains the broader language-derivative programme.

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
bounded result. #266 supplies the completed parser rows and the matched authoring comparison
below; #267–#270 own observation extensions, composition laws, pairings and
symmetric proof-syntax assessment.


## Completed parser rows and exact recovery

The added structural equations are explicit. Intersection computes the product
of nullable decisions and intersects the derived operands. Scale retains its
original decision while differentiating its parser operand. Transport maps the
nullable decision through `e []`; its derivative uses `e (a :: w)`, keeping the
word index in the isomorphism. Zero and universal derive to themselves. Epsilon
and atom derivative cells invoke the existing `Prim.derive` on their constructed
leaf parser, so their equality test and contradiction/isomorphism machinery
remain in `Parser.derive`. The leaf nullable cells likewise call the existing
nullable primitive. These cells expose the selected call boundary; they do not
compile recursion, synthesize equality decisions, or reprove those primitives.

`equations_correct` still proves every cell by reduction to the independently
existing parser operations. `methods_correct` applies `transpose_preserves`,
and the unchanged `recovered_nullable`, `recovered_derive` and
`recovered_snapshot` theorems cover every new constructor. Snapshot lookup has
its original `w.length ≤ n` premise. `intersection_automatic`, `scale_automatic`
and `transport_automatic` additionally compose that recovery with the existing
`WitnessTrie.unfold_*` theorems, obtaining the direct automatic combinators at
every finite depth. No finite enumeration of nullable-star parses is assumed.

[ParserViews](../../Examples/ParserViews.lean) checks the expected results through
those public theorems: zero refutes a parse; universal selects `PUnit` on a
nonempty word; epsilon retains empty-word equality evidence; atom accepts its
own singleton and rejects another; intersection returns both witnesses; scale
returns the chosen `true` payload and its epsilon witness; a transport swapping
ambiguous alternatives returns the right witness. The last example would fail
if a view preserved only Boolean acceptance. Structural derivative examples
retain both operands, the scale decision, and the reindexed transport map.
The old concat syntax and nullable-star witness distinction remain checked in
[EquationTranspose](../../Examples/EquationTranspose.lean).

`ULift` moves the `Decision A` value into the universe occupied by parsers;
`scale`'s field is `ULift (Decision A) × Parser P`. The lift is administrative
packaging, with no witness quotient. Transport's language parameters and
isomorphism are carried by its constructor name, and its parser is the field.
This accommodates arbitrary supplied isomorphisms without an implicit coercion
or an erased result index.

## Authoring additions from either view

`CodataProgram.addConstructors` takes an existing constructor-grouped program,
a family of new constructor names, their field types, and a new row for every
name. A row supplies an expression for each existing observer. Old constructor
names enter through `Sum.inl`, new names through `Sum.inr`.
`DataProgram.addObservers` is the corresponding observer-grouped route: supply
new names, their argument/result types, and an expression for each existing
constructor. It retains the old columns through `Sum.inl`.

Both helpers reuse the existing `Expr`, `Slot`, `transpose` and `untranspose`.
Their `*_old` laws give literal equality of retained syntax. The signature
extensions are abbreviations so Lean can expose field and result types during
elaboration. A new observer result can have a different type from existing
results; no common untyped output is introduced. `untranspose_preserves` provides
the reverse denotation equation, alongside the existing forward theorem.
Both use `Expr.eval_swap`, so their meaning is relative to one fixed primitive
interpretation. If an author changes that interpretation, old syntax retention
alone proves nothing about equality of old and new meanings.

[EquationViews](../../Examples/EquationViews.lean) begins with the existing
vector nil/cons constructors and lookup observer. From the constructor view,
`repeatRow` adds a repeat constructor: each lookup returns the payload from the
constructor block. After switching to the observer view, `withSize` adds a size
column: each cell returns the vector index using `Prim.size`. This is a new
equation, not a consequence of the old lookup contract. At length two with
payload seven, repeat lookup returns seven and size returns two.

`old_constructor_cells` and `old_observer_cells` instantiate the shared retention
laws. `old_lookup_after_views` composes those laws and the inverse theorem to
recover the original syntax after both additions and view changes. Both
round-trip directions are checked for both extended programs.
`repeat_matches_direct` and `size_matches_direct` derive the expected native
function results through `untranspose_preserves` and `transpose_preserves`.
The existing head/tail test still yields eleven at the second position.
`empty_lookup_impossible` retains the negative index boundary after observer
extension: no argument inhabits `Fin 0`.

Names are intrinsic keys, not source strings subject to alpha-renaming.
Constructor and observer parameters live in separate positional blocks.
Inside the constructor view, `Slot.first` is the observer argument and
`Slot.second` is the constructor field; the observer view reverses that order.
The type of each block remains attached to its slot. There is no ambient local
variable context or implicit capture: a local value must be represented in a
block or supplied explicitly as part of a primitive's meaning. Local binders,
local matches and recursive source calls are not constructors of `Expr`.
The inverse laws are equality of this typed syntax (using extensional equality
for tables), not merely equal denotations and not source-text equality modulo
arbitrary formatting or declaration reordering.

## Matched author comparison and remaining interfaces

| Matched task | Direct/native route | Verified-view route |
| --- | --- | --- |
| Repeat vector lookup | `directRepeat n x` is `fun _ => x`; application gives the payload. | Supply the new name/field family and `repeatRow`; the shared helper retains old rows, and `untranspose_preserves` connects the observation to the same direct function. |
| Vector size | `directSize` returns the type index. | Supply one new column using `Prim.size`; the helper retains lookup. Both round trips and the retained-cell theorem apply without editing their proofs. |
| Scale/transport parser observation | Call `Parser.scale` or `Parser.transport`, then nullable/derive/parse directly. | Reify their constructor and primitive cases and the typed equation bodies; unchanged generic recovery handles both organizations and bounded snapshots. |
| Direct automatic parser result | Use existing `WitnessTrie.intersection`, `scale`, `transport` and their `unfold_*` laws. | Apply `methods_correct`, then the same existing law. No second recursive implementation or proof is authored. |

The direct route is smaller for a single ordinary call. The view route adds
names, signature cases, `Expr` constructors, `Sum` tags, and parser universe
lifts. Its benefit is checked reorganization and extension with retained old
cells and reusable recovery. Existing users need not import or construct these
wrappers. The parser retrofit added rows and interpretations; it did not change
the earlier union/concat/star bodies, `Parser`, `WitnessTrie`, or recovery proof
structure. The vector extension leaves its native function implementation and
original example module intact.

This implementation encountered concrete Lean diagnostics: opaque signature
extensions hid expected field types during numeral elaboration, an omitted
index left a size expression underdetermined, and ordinary `rw` did not unfold
a projected field type. Making the signature constructors abbreviations,
supplying the index, and applying the public equality with explicit arguments
resolved those problems without casts or stronger mathematical assumptions.
The distinction is between elaboration bookkeeping and the mathematical index
obligation: `Fin 0` remains impossible, and a new size column still needs its
own body. The helpers reduce repeated sum-case code but do not yet provide a
surface-language editor or automatic error explanation.

This is a matched comparison by one implementation agent using the repository
skills and pinned `lean-toolchain`, not an independent author trial or a general
human-usability result. No trial was launched under #117. Exact model build,
reasoning configuration and token/resource budget were unavailable to the task;
the record supports code and diagnostic comparison rather than measured author
performance. Future independent trials belong with #117's coordinated protocol.

For #116, these results support offering alternative organizations when both
surfaces can elaborate to this scoped, indexed cell contract. They provide
reusable round-trip, extension and denotation criteria. They do not establish
that this matrix should mediate arbitrary dependent syntax, effects, recursive
programs or changes of mathematical setting. #235 retains those interface
mismatches: cell-local binders need explicit scoping/substitution; dependent
observer results varying with parameter values need transports beyond the
current result family; recursive calls need a separate termination/productivity
contract. #271 owns the related index-changing observation design. Keeping the
ordinary APIs usable is part of any proposed extension to those interfaces.

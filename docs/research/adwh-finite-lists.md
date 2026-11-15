# Finite list observations and composed pipelines

This reconstruction uses the ordinary finite `List` interfaces. Shared
function-accumulator reasoning extends `SquareKit.ListFusion`; the suffix
trimming algorithm belongs to `Applications.Sequences.SuffixTrim`; checked
standard-interface specializations and cross-application clients are in
`Examples.FiniteListInterfaces` and `Examples.ListPipelines`.

The declaration map is
[`adwh-finite-lists-declarations.tsv`](adwh-finite-lists-declarations.tsv).
It retains all 153 named declarations from the selected source modules, including
explicit owners for the 13 rows outside this ticket. Its dispositions identify
source correspondence, not a claim that Chapter 1 or the textbook is complete.

## Source identity and ownership

The supplied successor archive has SHA-256
`9e8bee022149e8456c9c4ab318f3be0d5d7f8361c25e7409cfe1c12bf8eb812c`.
The three selected members are beneath `project/adwh-lean/ADWH/Chapter01/`:

| Member | Named declarations | SHA-256 |
|---|---:|---|
| `Lists.lean` | 111 | `6f08454e2deeb5fe00df14e997b9d7f24bd53ba979546c8636bc3254e4a151b0` |
| `Interfaces.lean` | 36 | `17b51cd1806d370ea3561a3cf7418158a33c81604259e62f9739a61656f89d0a` |
| `SourceDerivations.lean` | 6 | `9d6d162340d202ec3cd48384c790a37b4b2ab7f7c7e9aa317a3370168a3a5485` |

Local 1008 owns 140 finite observation/replacement rows. Local 1007 owns the five
final `Interfaces` declarations concerning function equality and permutation
generators. Local 1009 owns the eight definitions/correctness rows for
`foldrByHead`, `foldlByInit`, `foldrViaHead`, and `foldlViaInit`. Those four
executions remain distinct: the first two unfold selectors once before invoking
the ordinary fold; the latter two recurse through selectors. Their differing
structural costs are not discharged by equal finite output values here.

The source's basic-list recursions already carry returned-value refinements to
standard Lists. Consequently, definitions such as map, filter, fold, reverse,
flatten, scan, take/drop, and extrema are replaced by the existing interfaces
and their laws. There is no parallel ADWH list implementation or source-name
alias collection. The table identifies the exact standard or local contract
for each selected declaration and preserves any domain or orientation change.
It also records the declaration's source line and the inspected standard-source
files. In that column, `lean:` is the Lean 4.35.0 source root and `repo:` is
the conaled root, including its pinned packages. The Mathlib revision is
`56a005855ea17e0b0958f73ec801ae140b0a1679`. These source inspections support the
replacement decisions; they do not claim that the standalone source package
was rebuilt in conaled.

## Arbitrary observers of append functions

`SquareKit.ListFusion.foldl_append_functions` states, for every result type,
observer `observe : List α → β`, list of blocks, and tail:

```lean
(blocks.foldl (fun f xs => fun ys => f (xs ++ ys)) observe) tail =
  observe (blocks.flatten ++ tail)
```

The observer needs no homomorphism, injectivity, or other law. The result type
need not be a list. This retains the source's arbitrary final function and
every-tail quantification while broadening its codomain.

The client `Examples.FiniteListInterfaces.dlistBlocks` actually folds append
over `Batteries.DList.ofList` blocks. `dlistBlocks_apply` proves the entire
appended result for every tail; `dlistBlocks_toList` is its empty-tail
observation. `dlistBlocks_observer` connects the original function accumulator
to this existing certified DList realization. It does not replace that
connection with equality only at `[]`.

The retained case appends `[[1,2],[],[3]]` before `[9,8]`. An observer returning
the pair `(length, optional last element)` produces `(5, some 8)`. The actual
DList client reaches that result through the observer bridge and generic law.
A separate case retains empty blocks, repeated values, and a nonempty tail in
the full sequence `[1,1,2,1,9]`.

These results concern values and observations. They do not attach a cost to
an arbitrary observer or infer materialization complexity from a function
equality.

## Function-level derivations with a real consumer

`Examples.ListPipelines` retains all six source function-level declarations
using standard APIs. In particular, the map/filter/flatten calculation keeps
the intermediate equalities:

1. Distribute filtering through flattening.
2. Distribute mapping through flattening.
3. Fuse the two outer maps.
4. Identify flatten-after-map with standard `flatMap`.

The final statement is

```lean
List.map f ∘ (List.filter p ∘ List.flatten) =
  List.flatMap (List.map f ∘ List.filter p)
```

`foldr_concat_from_master` separately derives nested folding through the existing
`SquareKit.ListFusion.foldr_reachable` theorem, using invariant `True` and the
ordinary append/fold law as the commuting equation. Its step need not be
associative, and the accumulator type can differ from the input element type.
The ordered-word example retains a nonempty accumulator tail. The source
scan fixture `[1,2,3]` gives `[6,5,3,0]` through the existing suffix-values
law in `SquareKit.ListFusion`.

`forest_distribution` applies the calculation to the actual
`Resources.TreeFlattening.fromTs` traversal through its existing refinement to
ordered fringes. `compressed_forest` then transports an independent
`RunCompression.Spec` certificate to the source-style equality-build consumer.
This connects existing producer and consumer implementations, rather than
comparing two freshly invented definitions.

The selected forest has fringe `[1,0,1,2,1]`. Removing zero and mapping successor
gives `[2,2,3,2]`; the supplied adjacent-input certificate gives `[2,3,2]` after
compression. The final 2 remains a separate run. Empty forest behavior is also
proved through the same public composition theorem. These full list equalities
retain ordering and duplicate occurrences; a sum or membership observation
alone would not express the same contract.

## Suffix trimming and its independent specification

`Applications.Sequences.SuffixTrim.trim` is the actual right-fold algorithm:

```lean
xs.foldr (fun x ys => if p x && ys.isEmpty then [] else x :: ys) []
```

Its independently defined `Spec p xs out` requires an all-true suffix whose
removal yields `out`, together with shortest-prefix minimality: for every
decomposition `front ++ back = xs` with all entries of `back` satisfying `p`,
`out` is a prefix of `front`. The specification mentions only decompositions,
the predicate, and prefix order, not `trim` or another executor.

The public results establish:

- Exact finite equality with `(xs.reverse.dropWhile p).reverse`.
- Reconstruction of the input from the retained prefix and removed suffix.
- Invariance under appending any all-true suffix.
- Shortest-prefix minimality, correctness for `Spec`, uniqueness, and the
  equivalence `trim p xs = out ↔ Spec p xs out`.
- Idempotence of trimming.

The source even-suffix fixture maps `[1,4,3,6,2,4]` to `[1,4,3]`. The internal 4
is retained. Empty input, an entirely matching input, and an entirely
nonmatching input exercise the boundary cases.

The actual consumer trims zero padding before run compression. The theorem
`trim_compress_padding` permits every all-matching padding suffix, without
requiring a lawful equality procedure merely to transport an exact input
equality through the consumer. The concrete compression certificate does use
the normal lawful natural-number equality: trimming `[1,1,2,1,0,0,0]` and
compressing produces `[1,2,1]`.

The matching prefix law in `Examples.FiniteListInterfaces.takeWhile_maximal`
is explicitly about initial segments. It does not assert maximality among
arbitrary subsequences. The reverse/drop and fold trimming implementations
have equal finite outputs; their traversal, demand, or allocation costs are
separate obligations.

## Finite interface and domain checks

The standard-function correspondence preserves the following distinctions:

| Contract | Retained interface or bridge |
|---|---|
| Optional head, tail, last | `List.head?`, `List.tail?`, and `List.getLast?`; bare total tail would lose empty-input failure. |
| Optional init | Scoped `init?` distinguishes empty failure from singleton success with `[]`. |
| Singleton extraction | Scoped `singleton?` succeeds iff the whole input is `[x]`, not merely nonempty. |
| First-element decomposition | `uncons_observation` uses standard head?/tail and states the exact cons equation. |
| Signed counts | Take/drop use `Int.toNat`; nonpositive counts produce `([], xs)`, and natural counts agree exactly. |
| Signed indexing | `indexSigned` rejects negative integers before converting; natural indices include standard out-of-range failure. |
| Labels | `labels_offset` swaps standard `zipIdx` pairs to `(index,value)`, with arbitrary offset; zero-based labeling is a specialization. |
| Empty extrema and bounded zip | Empty maximum/minimum return `none`; `zipWith` truncates to the shorter input. |
| Finite head/takeWhile folds | Checked equations connect the source expressions to ordinary APIs, without asserting lazy demand. |
| Associative fold agreement | Only the source associativity and identity hypotheses are used; the accumulator theorem needs only right identity. |

The monoid fold specializations use `List.foldl_eq_apply_foldr` and
`List.foldr_eq_foldl`, packaging the supplied laws as local standard instances.
They do not use a stronger commutative-fold theorem. Ordered concatenation is a
checked client.

Pinned `List.filter_filter` writes its combined predicate as `p x && q x`,
whereas the source writes `q x && p x`. `filter_fusion_value` bridges the
finite values by Boolean commutativity. This does not exchange the operational
order or cost of predicate evaluation in a partial, effectful, or lazy model.

## Scope and verification

The declaration table preserves all source rows, including standard replacements
and the separate partial-spine and resource developments. General finite laws are
specialized in checked clients; independent source expectations are retained
through the public bridges. New modules are reachable from
`SquareApplications` through `Examples.ListPipelines`.

The source PDF is absent from the supplied recovery package; provenance here
uses its actual reconstructed source and recorded extraction/coordinates. These
finite returned-value results do not establish partial-list behavior, infinite
productivity, Haskell laziness, machine overflow, floating arithmetic, or runtime
cost. Those Chapter 1 contracts remain separately scoped. No numerical sixteen-
queen proof or generated numerical artifact is part of this development.

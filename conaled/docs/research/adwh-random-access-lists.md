# Binary random-access lists (#171)

`Applications.Sequences.RandomAccess` reconstructs the complete finite semantic
closure of checkpoint233 `Chapter03/RandomAccessLists.lean`. The raw operations
retain per-node cached sizes, binary digits, carrying, borrowing and indexed
descent. Standard List supplies the independent sequence semantics. Five small
modules separate the representation/invariants, access/update, borrowing and
canonicality, tree construction, and existing-square consumers.

## Invariants and independent observations

`Tree.node` stores a size at every internal node. `Perfect rank` recursively
requires equal child ranks and the exact power-of-two cache at each node.
`Valid rank` assigns increasing ranks to digits and excludes trailing zero
digits; `Inv` starts at rank zero. The executable source `invRA` checks only
outer cached sizes. `invRA_of_Inv` proves validity implies that check. It does
not assert the converse.

The cached carrier differs from the existing `Bracketing.Tree`, whose forks
have no size field. Huffman and bracketing outer caches likewise cannot supply
per-node size descent. `erase` forgets caches into that shared tree.
`fromT_eq_fringe` identifies ordered decoding with `Bracketing.fringeSpec`;
`fromT_ne_nil` reuses its nonempty-fringe theorem. `cached_size_erasure` connects
correct caches to `Bracketing.size` through its fringe-length law. Executors
operate on cached trees directly; erasure is an observation bridge.

`Cached` recursively checks size sums without asserting balance. `Perfect.cached`
proves perfect trees satisfy it, but the converse is false. The standalone
`tree` builder returns none on empty input, and a tree with the original fringe
and valid caches on every nonempty input. Power-of-two length additionally
proves `Perfect` at the given rank. Lookup correctness still requires Perfect,
not merely Cached.

## Operations and canonicality

`consT` carries through occupied digits by joining cached trees; `consRA` starts
with a leaf. `toRA` folds cons over a List. Decoding preserves exact order and
occurrences. Construction and cons preserve validity, and decoding the encoding
returns the original List. Empty valid representations correspond exactly to
empty decoded lists.

`fetchT` selects a child using half the stored size, and `fetchRA` traverses
digits using their stored tree sizes. Their refinement theorems identify the
result with standard zero-based optional indexing. The compatibility name
`fetch` is an abbreviation for `xs[k]?`, replacing the source List traversal.
`fetchRA_none_iff` characterizes out-of-bounds lookup under validity.

`updateT` and `updateRA` follow the same cached branches, preserving perfectness
and validity. Decoding an update is exactly `List.set`, including out-of-bounds
indices. The latter leave the entire valid representation unchanged, proved
using canonicality rather than assuming decoder equality implies raw equality.

`unconsT` performs binary borrowing, reports malformed or empty failure, and
returns a tree at the current rank with a valid residual digit list.
`unconsRA` extracts the rank-zero leaf. Both cons/uncons round trips are proved,
along with ordered decomposition, head and optional-tail observations. Empty
optional tail is none; singleton optional tail is some empty representation.
The finite induction for `toRA_fromRA` decreases decoded length. Together with
decode-after-encode it proves injectivity on valid representations. Raw invalid
states are not included in that injectivity claim.

## Existing representation interfaces and clients

`Carrier α` is the subtype of digit lists satisfying Inv. `representation`
uses the existing `Squares.Rep` with this carrier, standard List and the decoder.
`decode_encode` and `encode_decode` expose both inverse laws. Validity is present
in the carrier; it is never inferred from shallow checking or decoding alone.

`encodeSquare`, `updateSquare`, `lookupSquare`, `consSquare` and `unconsSquare`
use the existing square type. Their implementations call the raw executors,
while their specifications use List operations. `unconsCarrier` packages the
proved validity of a successful residual state; it does not decode to compute
the result. `updateSquare_encode` uses canonicality to identify the updated
representation exactly with encoding the updated List.

`updateQuery` composes actual update and actual lookup through `Squares.compose`.
Its public laws cover same-index reads, other-index reads and the full List.set
observation, including invalid indices. `pushPop` similarly composes cons and
uncons; it preserves both the decoded head/tail observation and the exact prior
valid representation. No random-access command language or square framework
is introduced.

## Connected cases and statement review

`Examples.RandomAccessLists` checks empty and singleton lookup/head/tail/update,
first/last lookup and updates, at-length and larger indices, duplicate Nat
values and String symbols. Exact digit observations show three occupied digits
at length 7 and three leading zero digits after carrying to length 8. Public
cons refinement establishes order and validity; borrowing and composed push/pop
return the exact original seven-element representation.

Three negative boundaries distinguish the invariants. The source tree
`node 1 (leaf 10) (leaf 20)` passes invRA but returns 20 at index zero while its
ordered decoding begins with 10. Lookup refinement therefore disproves Inv.
`[zero]` passes the checker and decodes empty while nullRA is false; emptiness
refinement disproves Inv. A recursively Cached but unbalanced tree with a
two-leaf left child and one-leaf right child returns 30 at index one instead of
20. Its cache/size bridge holds, but lookup refinement disproves Perfect at
any rank. Builder examples connect empty, length-three Cached and length-four
Perfect results to shared fringe/size and lookup observations.

The expected carry/borrow and malformed-cache cases fixed the mathematical
obligations: recursive validity, exact occurrence order and cache-guided access
must connect to standard List independently of the executors. Final examples
consume refinement, invariant, canonicality and composition results; raw
reductions establish concrete digit shapes and counterexamples alongside those
connections. Statement review covered every claim family: rank progression,
cache recursion, trailing-zero exclusion, arbitrary finite symbol types,
zero-based bounds, unchanged invalid-index updates, explicit optional failure,
valid residuals, the decreasing measure in canonicality, Cached versus Perfect,
and the actual implementations/specifications in each composed square.
No premise is replaced by the weaker executable checker.

## Preserved source and validation

The [declaration ledger](adwh-random-access-lists-provenance.tsv) accounts for all
75 named source declarations, including the three negative examples. The exact
member SHA256 is
`937c93b447d687f8c91233704476c65372c717565ff906c6df1ccf7733119582`.
It was recomputed from the repository ZIP and matched against its manifest and
the inspected extraction. Selected arguments are adapted from that preserved
source, with shared tree observations and standard List indexing replacing
unnecessary independent interfaces.

`RandomAccessLookupCosts.lean` (SHA256
`c1df20833c4dd42ce1ae64a584a4b63596b29e3202e24fd14c10104d5e3e0568`)
and `RandomAccessEndCosts.lean` (SHA256
`26bdb3a5f21959ffa672adf502b020d20f05d1a9449a2904ca26b710e016fb7c`)
remain deferred in [checkpoint-233](../history/algorithm-design-haskell/README.md).
No operation, allocation, sharing, logarithmic, bulk-update or amortized bound
is claimed. Their sparse-index and mixed push/pop qualifications remain part of
the preserved evidence for later reconstruction.

Targeted validation is `direnv exec . lake build Examples.RandomAccessLists`.
The public entrypoint imports these examples. Fresh full validation, exhaustive
proof audit and independent reviews belong to the integration session.

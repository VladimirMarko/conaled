# Trie: positive numbers, total tables and collision counting

This note owns the current Lean correspondence for the `Trie` chapter of
*Verified Functional Algorithms*. CTB-94 supplied the pure increment under
CTB-15, with receiving context in upstream issue #558: number observations and
arithmetic, the actual default-bearing trie, its total-table abstraction and
the three collision programs. CTB-95 adds the complete retained resource
correspondence in [Trie work](vfa-trie-work.md), including measured arithmetic,
sequential amortization, explicit history/trie costs and the qualified
asymptotic progression. Source qualification requires the exact frozen checks
and both independent review axes; when those gates pass, Trie brings VFA to
13 of 17 units including Preface. Priqueue, Binom, Decide and Color then remain,
along with the outstanding FDSA/PFDS chapters and appendices. The standing task
and receiving acceptance remain open.

## Source and maintained owners

The source is VFA edition 2.1, dated 2026-08-24 10:11, from the pinned archive
with SHA-256 `f03296c763d78aa5bc18a545d848d398292575e5c8af4b5aa94dc25709e169b8`.
Its `vfa/Trie.v` member has 26,268 bytes and 712 lines, SHA-256
`a5af2b4db4c2cb639a8deb063e57909e11eb44ee763782ad0af9afbf45a78f3e`.
The entire primary text, including exercises and surrounding prose, was read.
The [canonical plan](../history/textbooks/checkpoint-012/books/vfa/records/research/specifications/1013-Trie.md)
has SHA-256 `ff3874effda4d56e22a84d16b685e723c72dc210d70a1aec0d38799b7ceaa56e`.
The [source inventory](../history/textbooks/checkpoint-012/books/vfa/records/research/source/vfa-source-inventory.json)
identifies 55 declaration records, 12 exercise headings and 11 pedagogical
commands. It is a lexical aid; neither a count nor a grading marker proves an
obligation. The retained [MIT notice](../licenses/vfa-MIT.txt) applies to the
source correspondence. Downloaded primary bodies remain outside the checkpoint.

| Maintained owner | Responsibility |
| --- | --- |
| [PositiveKeys](../../Applications/Numerals/PositiveKeys.lean) | Existing `PosNum`, `PNat` and `Nat` observations, the shifted key bijection, comparison observations and function transport. |
| [PositiveArithmetic](../../Applications/Numerals/PositiveArithmetic.lean) | Exact carry-addition branches, reused successor and completed comparison, the append printer, digits and bit-length mathematics. |
| [PositiveNumbers](../../Examples/PositiveNumbers.lean) | Source ten, key boundaries, observation transport, both carry orientations, comparison override and size endpoints. |
| [PositiveTrie.Basic](../../Applications/Search/PositiveTrie/Basic.lean) | Explicit-default raw trie, source lookup and all six insertion cases, raw laws and the existing total-table interface. |
| [PositiveTrie.Models](../../Applications/Search/PositiveTrie/Models.lean) | Shifted natural abstraction, source relation, observation algebra, Squares and finite-word behavior. |
| [PositiveTries](../../Examples/PositiveTries.lean) | Exact source tree and queries, arbitrary payloads/defaults, update histories and the limits of raw or optional observations. |
| [Collisions.Basic](../../Applications/Search/Collisions/Basic.lean) | The executable query-before-write client, arbitrary-state transport and the independent repetition-count specification. |
| [Collisions.Representations](../../Applications/Search/Collisions/Representations.lean) | Source Nat/function, signed-binary/function and positive-key/trie programs, with their actual operand orientations. |
| [CollisionCounting](../../Examples/CollisionCounting.lean) | The three source numeral lists and connected empty, distinct, repeated, signed and representation cases. |

The useful staged positive-key mathematics has one maintained owner in
`Numerals.PositiveKeys`. Its historical staged source remains unchanged as
provenance and is not imported. No competing positive datatype, binary tree,
table hierarchy, order framework or generic command language is introduced.

## Number observations and arithmetic

For a positive binary number `p`, write `numeric p` for its unshifted natural
value and `bitLength p` for `PosNum.natSize p`. The existing constructors have
the source meanings: `one` denotes 1, `bit0 p` denotes twice the child value,
and `bit1 p` denotes twice the child value plus 1. Positivity and numeric
injectivity are proved through the existing provider. `toPNat` preserves the
same value with its positivity witness; its inverse and equivalence reuse the
existing shifted construction.

Natural table keys use a different observation. `encode n` is exactly
`PosNum.ofNatSucc n`, with numeric value `n + 1`; `decode p` is the natural
predecessor of its positive value. Both round trips and both injectivities are
proved. Thus positive one is natural key zero, positive two is key one, and
the source constructor for ten has numeric value 10 and table key 9. The
unshifted `PosNum.ofNat` maps both zero and one to positive one and is not
injective. The examples also distinguish clamped positive predecessor from
the zero-capable predecessor and shifted key observation.

`binaryPNatEquiv`, `binaryNatEquiv`, the existing `Equiv.pnatEquivNat`
observation and both function round trips retain these precise conventions.
The function transports permit arbitrary payload universes, including
type-valued observations. These are value correspondences; the recursion of
`ofNatSucc` does not acquire a logarithmic conversion-cost theorem from them.

Successor reuses `PosNum.succ` and exposes its three exact source cases.
`addc` follows all eighteen source branches, including a nested successor on
the remaining strict child when the other input is terminal. The theorem
`addc_correct` has both carry values and arbitrary positive operands:

\[
\operatorname{numeric}(\operatorname{addc}(c,p,q))
= [c] + \operatorname{numeric}(p) + \operatorname{numeric}(q).
\]

Here `[c]` is 1 for true and 0 for false. Source `add` starts with false carry.
`add_eq_add` identifies its result with existing positive addition, and
`addc_true_eq_succ_add` identifies the true-carry result with the successor of
that sum. These semantic adapters do not identify the algorithms' work.

The correct completion of the comparison exercise reuses `PosNum.cmp` and
exposes all nine constructor pairs. In mixed low-bit cases, the comparison of
higher bits takes precedence; the low bits decide only the equal higher-part
case. `compare_correct` gives the source match-valued numeric result, while
`compare_keys` and `compare_eq_iff` recover equality of the actual positive
keys in the equal branch. The source's unfinished catch-all less-than branch
fails already on one versus one; `placeholder_boundary` records that diagnostic.

`printInBinary` keeps the literal source recurrence: the child's display is
followed by a singleton digit. It displays ten as `[1,0,1,0]`.
`printInBinary_eq_bits` relates this display to reversed `Nat.bits`, mapped by
`Bool.toNat`. Every displayed digit is zero or one and the display starts with
one. The low-bit-first `digits` observation ends in one and is nonempty.
Its length and the printer's length equal the existing positive bit length.
These observations do not identify append allocation with a different printer.

The size results retain both positive endpoints:

\[
2^{b(p)-1}\leq\operatorname{numeric}(p)<2^{b(p)},\qquad
b(p)=\operatorname{Nat.log2}(\operatorname{numeric}(p))+1.
\]

Powers of two have size exponent plus one, including exponent zero. For both
carry values, the result size is at least the maximum operand size and at most
that maximum plus one. The thirteen-plus-two examples attain the two endpoints
depending on the incoming carry. The measured recursive work now has its own
owner in `Resources.PositiveArithmetic`; its result-size and logarithmic bounds
consume these exact pure theorems.

The signed carrier is the existing `ZNum`, with zero, positive and negative
constructors and its integer observation. Positivity of each magnitude avoids
two representations of signed zero. The source explicitly leaves general
signed addition/subtraction implementations to its library. This increment
uses the pinned signed provider and proves the observations needed by the
actual signed collision program.

## The raw trie and its total meaning

`Search.PositiveTrie.Table ν` is exactly `ν × BinaryTree ν`: a stored default
and a raw tree. A source node with left subtree, value and right subtree is
`BinaryTree.node value left right`. `look` is the existing
`BinaryTree.getOrElse`; positive one selects the current root, `bit0` descends
left, `bit1` descends right, and a leaf returns the supplied default.

Insertion recurses on the positive key. Its six equations distinguish each
key constructor at a leaf and at a node. Descending below a leaf materializes
default-filled intermediate nodes. Updating an existing node preserves the
untouched child and, unless the key terminates there, its old value. The table
operation preserves its stored default. This is trie insertion rather than
ordered-key binary-search-tree insertion.

`look_ins_same` and `look_ins_other` hold on every raw tree, with arbitrary
payloads, when lookup and insertion use the same default. There is no payload
equality, ordering, inhabitation, search invariant or balance hypothesis.
The source representation invariant is correctly `True`, with the original
empty/insertion validity wrappers retained. `ops default` and `laws default`
instantiate the existing `Search.TotalTable.Ops` and `Laws`; the latter uses
`fun _ => True`. A table supplied to these operations may have a different
stored default from the chosen empty default. The raw get/set laws still hold.

The natural abstraction is
`abstract table n = lookup (encode n) table`, and `Abs table meaning` is equality
of those functions. The empty theorem gives the constant default function.
`lookup_decode` recovers a positive-key lookup through the abstraction, and
`abstract_insert` updates the abstract function at `decode key`. The source
`empty_relate`, `lookup_relate` and `insert_relate` retain their intended
premises and query/written-key direction. The shifted bijection supplies the
required equality decisions without introducing a new representation invariant.

Observation laws reuse the accepted total-table/history and function-update
owners. They cover arbitrary chronological writes, repeated-write shadowing,
self-update and commutation at different keys. The representation and empty,
insert and lookup Squares package the same correspondence for composition.
No raw-tree extensionality is assumed: an empty table and an explicit write of
its default can have identical total meanings while their raw trees differ.
An intermediate filler can also yield `some default` under optional tree lookup
without being an explicitly written key. Neither the total abstraction nor
optional presence reconstructs an insertion history.

The source `three_ten` writes positive ten and then positive three. Its complete
constructor tree is checked, as are the source queries `[3,1,4,1,5]`, which
return `[true,false,false,false,false]`, and the lookup at ten, which returns
true. Its natural meaning writes at 9 and then 2. Connected cases exercise
strings, type-valued payloads, nontrivial defaults, overwrites and arbitrary
write histories. A separate counterexample shows why the raw look/insert law
must share a default.

### Words, transitions and the finite-state qualification

`word` records the low-order bits of a positive key and omits the terminal one:
one gives the empty word and ten gives `[false,true,false]`. The raw-tree
`coalgebra` uses root observation and left/right transitions through the
existing `SquareKit.WordCoalgebra` interface. `run_word` identifies its finite
word behavior with `look`. The existing depth-indexed snapshot construction is
related by `lookup_unfold_word`, with its explicit word-length hypothesis;
the snapshot datatype is not the raw default-bearing source trie.

A leaf is absorbing in this word semantics. Processing an unused word suffix
there still yields the default, although actual `look` stops immediately at
the leaf. The semantic equality supplies no equality of step counts. For one
fixed finite input tree, every reachable state belongs to the existing
`Trees.subtrees` set. A private finite-set proof uses that owner's singleton
and union equations, and transition closure uses `Trees.Subtree.trans`.
`reachable_finite` states the restricted result. It does not assert finiteness
of the entire `BinaryTree ν` carrier or of all possible words.

## Collision programs and the independent result

`Search.Collisions.step` queries before deciding what to do. A true result
increments the counter and keeps the table; a false result writes true and
keeps the counter. `run` is the ordinary list fold on the actual counter/table
state, and `loop` observes its counter. The executable operations require no
finite-support witness and carry no validity proofs.

The independent specification is `count xs = xs.length - xs.dedup.length`.
It counts each occurrence after the first; three copies contribute two rather
than the three unordered equal pairs. `Seen` is a proof-only finite-set witness
for tables reached from a finite initial seen set. `run_spec` proves validity,
the union of initial seen keys with input keys, and the conservation equation

\[
c_{\mathrm{final}}+|S\cup\operatorname{keys}(xs)|
=c_{\mathrm{initial}}+|xs|+|S|.
\]

The initial counter is arbitrary. `run_from_empty` and `collisions_correct`
give the complete result and final seen set. `prefix_seen` applies to every
processed prefix. Separate offset, bounds and transport theorems work for
arbitrary valid initial tables, including Boolean functions with infinite
support; they do not assume every total function admits a finite seen witness.
`run_agrees` transports both final counter and total observation. `loop_reindex`
permits an injective change of key type and corresponding arbitrary initial
tables, leaving target values outside the image unrestricted. `count_map`
proves the matching independent-result invariance.

The three source realizations retain their actual carriers and operand order:

| Source program | Executable realization and result bridge |
| --- | --- |
| `VerySlow` | Nat keys, a total Boolean function, `Function.update`, and source counter `c + 1`. `loop_common` holds for arbitrary initial counters and functions; `collisions_correct` proves the independent count. |
| `RatherSlow` | `ZNum` keys and counter, constructive Boolean equality, the source point update and `c + 1`. `eqb_int` connects equality to integer observation. The loop theorem observes an arbitrary signed starting counter plus the common client's collision increment. The result and key-observation theorems preserve signed keys. Bounds imply nonnegativity for every zero-start prefix, including with an arbitrary initial table. |
| `FastEnough` | Actual positive keys and `PositiveTrie.Table Bool`, with source counter `1 + c`. Its loop theorem consumes the actual trie `ops`/`laws`. Observation and injective-key transport connect it to function tables and to numeric, shifted and encoded key lists. |

All three source lists are numerals `[3,1,4,1,5,9,2,6]` in their own carriers
and return one. Their positive numerals are not silently replaced by shifted
encodings of the displayed natural list. Additional cases retain empty and
distinct inputs, repeated keys, signed negative keys and initial counters,
overwrite behavior, arbitrary-state transport and a noninjective relabeling
counterexample. None of these semantic results establishes a native cost for
Lean's `Nat`, `ZNum`, function update or generated code.

## Complete source record ledger

In this table, `Keys` means `Numerals.PositiveKeys`, `Arithmetic` means
`Numerals.PositiveArithmetic`, `Trie` means `Search.PositiveTrie`, and collision
subnamespaces are under `Search.Collisions`. Example owners are the linked
files above. The measured owners and complete resource argument are linked in
[Trie work](vfa-trie-work.md). Every record and exercise is mapped; the final
frozen validation and independent review remain separate qualification gates.

| Source ID | Lean witness or disposition |
| --- | --- |
| `Trie.VerySlow.loop@79` | `VerySlow.loop` and its arbitrary-counter/function `loop_common`. |
| `Trie.VerySlow.collisions@87` | `VerySlow.collisions`, connected to `count` by `collisions_correct`. |
| `Trie.VerySlow.collisions_pi@90` | The Nat source-list result in `CollisionCounting`, through the public result theorem. |
| `Trie.Integers.positive@131` | Existing `PosNum.one`, `bit0`, `bit1`; `Keys.numeric_*` gives all constructor meanings. |
| `Trie.Integers.ten@143` | `Examples.PositiveNumbers.ten`, the literal source constructor. |
| `Trie.Integers.positive2nat@147` | `Keys.numeric`, with exact constructor equations and positivity/injectivity. |
| `Trie.Integers.print_in_binary@160` | `Arithmetic.printInBinary`, its three equations and reversed-`Nat.bits` adapter. |
| `Trie.Integers.succ@190` | Existing `PosNum.succ` through `Arithmetic.succ` and its three equations. |
| `Trie.Integers.addc@200` | `Arithmetic.addc` and all eighteen explicit branch equations. |
| `Trie.Integers.add@222` | `Arithmetic.add = addc false`, with existing-addition value correspondence. |
| `Trie.Integers.succ_correct@239` | `Arithmetic.succ_correct`. |
| `Trie.Integers.addc_correct@247` | `Arithmetic.addc_correct`, with both carry values and arbitrary positive operands. |
| `Trie.Integers.add_correct@253` | `Arithmetic.add_correct`, using the carry theorem. |
| `Trie.Integers.comparison@279` | Existing `Ordering.lt`, `eq`, `gt`. |
| `Trie.Integers.compare@283` | `Arithmetic.compare = PosNum.cmp`, all nine constructor cases; the unfinished source placeholder is explicitly refuted. |
| `Trie.Integers.positive2nat_pos@293` | `Keys.numeric_pos` and `one_le_numeric`. |
| `Trie.Integers.compare_correct@300` | `Arithmetic.compare_correct`; `compare_keys` strengthens only the equality observation to actual key equality. |
| `Trie.Integers.Z@320` | Existing `ZNum`, retaining its single zero and positive/negative magnitudes. |
| `Trie.RatherSlow.total_mapz@358` | `RatherSlow.TotalMap ν = ZNum → ν`, with arbitrary payload universe. |
| `Trie.RatherSlow.empty@360` | `RatherSlow.empty`, the constant function. |
| `Trie.RatherSlow.update@361` | `RatherSlow.update`, `eqb_int` and `update_apply`, preserving written/query orientation. |
| `Trie.RatherSlow.loop@365` | `RatherSlow.loop`, with signed arbitrary-initial-counter `loop_common`. |
| `Trie.RatherSlow.collisions@373` | `RatherSlow.collisions` and its integer-observed correctness. |
| `Trie.RatherSlow.collisions_pi@375` | The actual `ZNum` source-list result in `CollisionCounting`. |
| `Trie.goal_at_line_419@419` | `Examples.PositiveTries.ten_constructor` equates the actual positive numeral ten to the exact source constructor. |
| `Trie.trie@427` | Existing `BinaryTree`, with the source node argument permutation made explicit. |
| `Trie.trie_table@433` | `Trie.Table ν = ν × BinaryTree ν`. |
| `Trie.empty@435` | `Trie.empty`, retaining the explicit stored default. |
| `Trie.look@438` | `Trie.look = BinaryTree.getOrElse`, with leaf and three node equations. |
| `Trie.lookup@449` | `Trie.lookup`, using the table's own default. |
| `Trie.ins@452` | `Trie.ins` and all six source key/tree equations. |
| `Trie.insert@468` | `Trie.insert`, preserving the table default. |
| `Trie.three_ten@472` | `Examples.PositiveTries.three_ten`, its complete constructor result and source queries. |
| `Trie.FastEnough.loop@491` | `FastEnough.loop`, retaining `1 + c` and using actual trie operations. |
| `Trie.FastEnough.collisions@499` | `FastEnough.collisions` and the independent-result theorem. |
| `Trie.FastEnough.collisions_pi@501` | The actual positive-numeral source-list result in `CollisionCounting`. |
| `Trie.manual_grade_for_successor_of_Z_constant_time@526` | Administrative marker only. The exercise is discharged by `Resources.PositiveCounter`'s full measured digit bridge, exact potential and positive-one sequential average; the marker itself supplies no proof. |
| `Trie.look_leaf@548` | `Trie.look_leaf` for every positive key and arbitrary default. |
| `Trie.look_ins_same@557` | `Trie.look_ins_same` on every raw tree and payload. |
| `Trie.look_ins_other@565` | `Trie.look_ins_other`, shared default and actual distinct positive keys. |
| `Trie.nat2pos@577` | `Keys.encode = PosNum.ofNatSucc`. |
| `Trie.pos2nat@578` | `Keys.decode`, natural predecessor of the positive value. |
| `Trie.pos2nat2pos@580` | `Keys.encode_decode`. |
| `Trie.nat2pos2nat@590` | `Keys.decode_encode`. |
| `Trie.pos2nat_injective@600` | `Keys.decode_injective`. |
| `Trie.nat2pos_injective@603` | `Keys.encode_injective`. |
| `Trie.is_trie@614` | `Trie.isTrie`, exactly `True`. |
| `Trie.abstract@624` | `Trie.abstract`, lookup after shifted encoding. |
| `Trie.Abs@627` | `Trie.Abs`, equality with the abstract total function. |
| `Trie.empty_is_trie@636` | `Trie.empty_isTrie`. |
| `Trie.insert_is_trie@639` | `Trie.insert_isTrie`, retaining the source premise. |
| `Trie.empty_relate@650` | `Trie.empty_relate`. |
| `Trie.lookup_relate@660` | `Trie.lookup_relate`, querying the abstract function at `decode key`. |
| `Trie.insert_relate@674` | `Trie.insert_relate`, point update at `decode key`. |
| `Trie.Abs_three_ten@684` | `Examples.PositiveTries.Abs_three_ten`, natural writes at 9 and then 2. |

### Exercises and pedagogical commands

The successor, carry-addition and comparison exercises (238–310) have the
universal statements above; finite examples supplement those statements.
The three raw lookup exercises (547–568) hold without an invented structural
invariant. Both bijection injectivities (599–605), the invariant exercise
(630–642), and all three abstraction exercises (644–679) are explicit. The
successor-cost exercise (515–527) uses the completed measured sequential
argument in `Resources.PositiveCounter`. It retains arbitrary initial
potential, before states `1,…,N`, final value `N+1`, the distinction between
states and transitions, and the positive-length average. Its optional choice
between a uniform-random argument and successive increments does not require
proving both alternatives; the completed route is the latter.

| Command line | Adaptation and boundary |
| --- | --- |
| 106 | `Resources.CollisionHistory.unaryEqRun` follows the displayed Boolean recurrence, proves its value and exact `min x y + 1` work, and is consumed by the measured history client. Lean's native Nat equality is not assumed to execute that unary recursion. |
| 154 | `ten_numeric = 10`. |
| 167 | `ten_print = [1,0,1,0]`. |
| 175 | `ten` retains the displayed nested constructors; custom postfix syntax is unnecessary. |
| 338 | Reuse the actual existing `PosNum` datatype and constructors. |
| 344 | Existing `PosNum.cmp`, with the completed source cases and correctness. |
| 345 | Existing positive addition, connected by `add_eq_add`. |
| 347 | Existing signed addition, used by the actual signed source loop and its integer-observed theorem. |
| 413 | The same positive carrier indexes the raw binary trie. |
| 475 | `three_ten_constructor`, the complete source tree. |
| 482 | `three_ten_queries`, the exact source query vector. |

The remaining prose explains representation choices, the difference between
mathematical and machine integers, imperative array access, binary-key tries,
and applications to symbol tables and graphs. The array comparison assumes a
declared indexed-array model and in-range keys; it is not a theorem that every
pure language must suffer a logarithmic slowdown. The discussions of Hoare
logic, Haskell IO, CompCert and the source `PositiveMap` interface provide
context, without requiring a new language semantics or a formalization of an
unmentioned API. Lean proof checking, runtime execution, numeric representation
and the cost models below retain separate claims.

## Complete resource correspondence

The [resource note](vfa-trie-work.md) records the actual recurrences, tariffs,
proof endpoints, examples and model boundaries for all seven obligations
retained by CTB-94. The complete canonical plan remains authoritative.

| Retained obligation | Maintained result |
| --- | --- |
| Successor, carry addition and comparison | `Resources.PositiveArithmetic` instruments every actual branch, proves result erasure, bounds successor visits and all nested addition work, and gives the exact minimum-bit-length comparator count. Long carry/equal-length families and immediate comparison against one are checked. |
| Successor exercise and zero-start signed counter | `Resources.PositiveCounter` proves canonical digits and full measured bridges to existing BinaryCounter execution. Exact potential holds on the same positive or Num trajectory; positive-one average, zero first write, signed `c+1`, nonnegativity and sparse increments are explicit. |
| Unary equality, functional history and counter | `Resources.CollisionHistory` has the exact Boolean unary recurrence and newest-first history decoder. Empty-start prefix length equals distinct-key count. Literal unary `c+1` costs are included, with exact counter accounting and the complete magnitude-dependent total bound. |
| Signed binary equality and history | The inspected signed comparator uses actual measured positive comparison with separate sign/selection charges. Bool/Int bridges, the independent bit-length bound, history work, wrapper calls and same-trajectory amortized binary counter are all included. |
| Accepted balanced-tree collision specialization | `Resources.CollisionRedBlack` preserves actual BST/red-black shape and finite-key invariants, bounds size by distinct keys, and includes lookup, insertion, balance, concrete binary comparison, counter writes and overhead. It proves the corrected `n(B+1)(1+log(D+1))` upper family. |
| Native-positive trie work | `Resources.PositiveTrie` proves early-stopping lookup and exact insertion call/construction counts on every raw tree, with complete collision sum and bit-bound totals. The one-long-key family separates path length from distinct insertion count. |
| Qualified asymptotic progression and lower family | `Resources.CollisionGrowth` supplies explicit half-open key and length hypotheses, the positive `key+1` offset, corrected finite bounds and standard real `IsBigO` statements for the actual four clients. The distinct unary interval has the canonical lower expression and a matching cubic upper bound. Other stages remain upper bounds. |

Operational qualifications are part of the correspondence. Native-positive
lookup excludes key encoding, numeric casts, parsing and printing. The
recursive `ofNatSucc` construction is not made logarithmic by bijectivity.
Changed-digit writes, syntactic node constructions and native allocation are
different observations. Word behavior agrees in value without equating its
absorbing-leaf steps to an early-stopping lookup. The half-open array comparison
requires declared RAM/indexing assumptions; no universal impossibility claim
about pure updates or new mutable-array realization is added.

Trie requests no new timing experiment. The unchanged Extract and Redblack
runtime executions remain historical checkpoint-041 evidence, retaining their
original candidate/tree, controls and limits. Checkpoint-043 source and selected
artifact identity checks do not relabel those executions. The resource claims
do not certify physical sharing, stack usage, compiler correctness, garbage
collection or universal native performance.

## Validation and continuation

The correspondence, exact statement domains and connected cases above are
ordinary research/source owners. Historical author probes distinguished authored
and generated declarations; they do not replace current candidate validation.
[CTB-94/CTB-95](../textbooks/CTB.json) retain the donor Trie qualification and
remaining boundary. Current CTB-78 receiving acceptance requires the applicable
whole-library build/audit, affected behavior and both independent review axes on
the integrated tree. No historical focused probe or retained signature count is
relabelled as a receiving pass.

Old checkpoint payload/target counts and mandatory retention of every earlier
statement output are incidental history, not mathematical requirements of Trie.
Useful source/exercise maps, failure cases and actual current evidence remain;
processed wrappers can retire only after their destinations and links have been
verified. At the donor, later VFA chapters are already locally qualified. Current
remaining work follows CTB's integration gate and the complete three-book scope.

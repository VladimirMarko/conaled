# Binary rotation certificates: structural foundations and remaining verifier

CTB-24/FDSA-5-93 requires an explicitly encoded rotation-distance decision problem
with polynomial-size witnesses and polynomial verification. The fixed-width
binary predecessor, measured partial rotations, actual structural equality,
finite-word encodings and linear bit/path/move prefix parsers now have concrete
Lean owners. Stack tree/input parsing, streaming verification and the complete
polynomial-checkability conclusion remain unfinished. No new source row is
qualified; current whole-library, exhaustive-audit and receiving gates remain
separate. [CTB](../textbooks/CTB.json) owns the complete requirements and progress.

Cumulative source integration is tracked in
[issue #660](https://github.com/VladimirMarko/conaled/issues/660). FDSA-5-85 already
has receiving acceptance under #659. This paper records implemented foundations
and remaining mathematical obligations; accepting those foundations does not
complete FDSA-5-93.

## Existing semantics and source boundary

[Mixed execution](../../Applications/Trees/Rotations/Mixed.lean) and
[minimum distance](../../Applications/Trees/Rotations/Distance.lean) supply actual
partial moves, state-dependent subtree positions, sequential composition,
preservation, inverse traces and attained shortest traces. For `Shape n`,
`distance_spec` gives a successful trace whose length is the actual minimum;
`distance_le_iff` connects the threshold to existence of a sufficiently short
trace; `distance_le_two_mul_sub_two` gives the empty-safe natural bound `2*n-2`.
The [distance paper](fdsa-rotation-distance.md) and existing
[examples](../../Examples/RotationDistance.lean) retain empty, repeated-label,
disconnected-label and stale-position distinctions. FDSA-5-91 is represented by
those owners. The original FDSA-5-94 tariff/finite-mean work belongs to
[the three-key paper](fdsa-three-key-search-mean.md), not this remaining plan.
FDSA-5-92's [sharp diameter](fdsa-rotation-diameter-preparation.md) is a separate,
mandatory obligation and is neither needed nor waived by this construction.

This work continues the 18 November 2026 preparation by
`/root/rotation_distance_cases` and the subsequent fixed-width-threshold design.
The original author read Basic/Position/Bounds at donor 117 and extracted the
relevant FDSA printed pages 67 and 76 from the 27 July 2026 PDF, SHA256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Its rendering attempt did not establish fresh visual inspection. The later root
continuation reread the complete certificate section without claiming a complete
new reading of both earlier preparation papers. The current implementation
reuses the actual repository interfaces and preserves these source-reading limits.
No present research-status assertion follows from the textbook's historical
prose. The canonical owner is
[FDSA-5-93](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter05-obligations.md).

## Declared structural observation

All new programs return `Resources.Measured value Nat`. The tariff charges:

- one entry/dispatch per activation of each named recursive primitive or later
  parser/checker state, covering its finite local constructor/tag distinctions;
- one per newly constructed list cons or tree node;
- one per returned `some`, `none`, or Boolean literal.

Nil, Unit and finite tag constants, projections, tuple/record/control packaging,
aliases and reuse of an already returned value are free. Returning a recursive
result directly constructs no additional result. `Measured.bind` and natural
addition used only to accumulate observations are measurement machinery.

This is an explicit source-event observation. It is not compiler instrumentation,
allocation measurement, bit complexity or machine time. Variable traversals,
reconstruction, binary borrowing and structural comparison are actual programs;
none is replaced by an uncharged whole-operation oracle. Mathematical node
counts, decoded natural values and lengths occur in contracts and proofs, not as
unaccounted runtime work in these primitives.

## Implemented fixed-width predecessor

[BinaryCounter/FixedWidth](../../Applications/Resources/BinaryCounter/FixedWidth.lean)
reuses the existing little-endian `Bits` and independent mathematical `value`.
Leading high zeros are permitted. Empty and nonempty all-zero words both denote
zero. The executable `decFixedRun` never calls `value`, normalizes its width, or
expands the encoded natural into a unary list.

Its complete equations bind the actual returned recursive Option:

| Input/recursive outcome | Actual result | Work |
| --- | --- | --- |
| Empty word | `none` | 2 |
| `true :: tail` | `some (false :: tail)` | 3 |
| `false :: tail`, recursive failure | `none` | recursive work + 2 |
| `false :: tail`, recursive success `ys` | `some (true :: ys)` | recursive work + 3 |

The true branch reuses the untouched higher-bit suffix. A borrowed prefix is
reconstructed only after the recursive predecessor succeeds. Existing `decBits`
retains its distinct canonicalizing contract: it maps `[true]` to `some []`,
whereas the new operation returns `some [false]`.

The public proofs establish, for every bit word `bs`:

- failure iff `value bs = 0`;
- every actual successful result `ys` has `ys.length = bs.length` and
  `value bs = value ys + 1`;
- positive value has an actual successful result, without canonicality;
- actual work is at most `3*bs.length+2`.

The arithmetic is independent of the implementation. At a true low bit,
`1+2*v` becomes `2*v`. At a false low bit, recursive success gives `v=w+1`,
and the returned true low bit has value `1+2*w`; thus `2*v=(1+2*w)+1`.
These equations also supply positivity where natural subtraction would need it.

Two exact whole-result theorems make early termination explicit. An all-zero word
of width `b` fails with work `2*b+2`. A word consisting of `r` low zeros followed
by one and any higher suffix returns `r` ones followed by zero and that unchanged
suffix, at work `3*(r+1)`. Numeric magnitude may vary arbitrarily in the reused
suffix without affecting that executed work.

## Implemented partial rotation and reconstruction

[RotationCertificate/Execution](../../Applications/Resources/RotationCertificate/Execution.lean)
uses the existing `RotationDirection`, `RotationMove`, `applyAt?` and `applyMove?`.
All rotations and positioned callbacks remain polymorphic in an arbitrary label
type and universe; they require no equality, ordering, inhabitance, cache or
legality assumption on raw inputs.

`rotateRun` executes the two legal root patterns, binding both newly constructed
nodes into the actual returned Option. Success costs 4: entry, two nodes and
`some`. An illegal root returns `none` at cost 2. Its value erases exactly to
`direction.apply?`, including every malformed root.

`applyAtRun` executes an actual measured callback. An empty position charges one
entry and calls it even at nil. A nonempty position at nil returns `none` at work
2 without inspecting the remaining path. At an ancestor it follows the selected
child, binds its actual result, and either propagates failure with 2 extra units
or reconstructs the original parent and untouched sibling with 3 extra units.
Both branch recurrences and raw callback erasure are public. `applyMoveRun` is a
free specialization to `rotateRun`, not a second rotation semantics.

The successful-depth theorem is derived from the actual partial operation:

`applyMove? move source = some target -> move.position.length + 2 <= source.numNodes`.

Each traversed ancestor contributes one node; a legal root rotation requires two
more. The premise is actual success, not a certificate field asserting a bound.
Measured success transports this law and existing node preservation/inversion
through the proved raw erasure. Successful work is exactly `3*d+5` for path
depth `d`. For **every** raw move/tree, actual work is at most `3*N+3`, where
`N` is source node count. This includes arbitrarily long supplied paths: traversal
stops at the first missing node.

The recurrences also explain the two failure forms. If the path reaches an
illegal root after `d` nonempty ancestors, work is `2*d+3`. If it instead reaches
nil while branches remain, work is `2*d+2`. Here `d` counts reached ancestors,
not the unvisited supplied suffix. The connected cases retain both distinctions.

## Implemented structural equality

`eqTreeRun` compares Unit-labelled shapes by actual constructor inspection and
left-first short-circuit recursion. Nil/nil and constructor mismatch each cost 2.
Two nodes charge one entry and compare the left subtrees. A false left result
returns a false literal at one extra unit; a true left result executes and
returns the right result directly. It never invokes a whole-tree equality oracle
and assigns it one unit.

The proofs give actual Boolean value `decide (source = target)`, work at most
`3*source.numNodes+2` for every target, and exactly that work for self-comparison.
The asymmetrical bound is intentional: an unmatched target subtree can be
arbitrarily large and is not visited after a constructor mismatch. The self case
sums both child costs and one entry, giving
`(3*L+2)+(3*R+2)+1 = 3*(L+R+1)+2`.

## Connected cases and minimum-versus-route separation

[MeasuredRotationCertificate](../../Examples/MeasuredRotationCertificate.lean)
connects the public contracts to independently fixed literal and arbitrary-input
cases. Receiving #660 accepts these foundations with a complete whole-library
build and exhaustive proof audit. This does not qualify the unfinished
FDSA-5-93 verifier or its full polynomial-checkability requirement.

The bit cases are empty failure at 2; `[1] -> [0]` at 3; `[0,1] -> [1,0]` at 6;
`[0,0,1] -> [1,1,0]` at 9; `[1,0,0] -> [0,0,0]` at 3; and three zero bits failing
at 8. Arbitrary suffix, width, returned-value and positivity clients consume the
public general theorems.

Write `E` for nil, `U` for a singleton, `L2` and `R2` for the two-node chains,
`L3` for the left three-node chain and `B3` for the balanced three-node shape.
Equality costs are 2 for `E/E`, 5 for `U/U`, 8 for `L2/L2`, and 4 for the
left-first mismatch `L2/R2`. Arbitrary skipped right trees and arbitrary target
subtrees retain these mismatch observations. A root-right move on `L2` succeeds
at positioned work 5; the opposite illegal move costs 3. A root-right rotation
at the left child of `B3` fails at 5. A nonempty position at `E` fails at 2,
independently of its remaining length. Callback clients at nil demonstrate both
success and failure, and both parent branches use the actual replacement tree.

The existing stale-position example is now connected to measured execution:
root-right maps `L3` to `B3`, while right-at-left is legal on the original `L3`
but illegal on the reached `B3`. Each move must be checked in its current state.

The previously missing normalization separator is also concrete and proved:

- `rightPositions L3 = [[],[]]` and `rightPositions B3 = [[]]`;
- `connectionMoves L3 B3 = [rootRight,rootRight,rootLeft]`, length 3;
- the displayed route actually succeeds;
- one root-right move and distinct endpoints prove `Shape.distance L3 B3 = 1`;
- `distance_spec` supplies an attained trace of length 1, strictly shorter than
  the normalization route.

Thus a threshold-one completeness proof cannot simply submit the normalization
route. The final verifier must accept a short witness selected from the attained
minimum, while allowing a non-shortest certificate whenever its own length fits
the supplied threshold.

## Implemented finite-alphabet codes and accumulator emitters

[Encoding](../../Applications/Resources/RotationCertificate/Encoding.lean) fixes
`Tag = Fin 16` and `Word = List Tag`, with distinct symbols:
`E=0`, `N=1`, `sep=2`, `bit0=3`, `bit1=4`, `endInput=5`, `rotL=6`, `rotR=7`,
`pathL=8`, `pathR=9`, `endMove=10`; codes 11 through 15 are invalid syntax.
Each symbol is representable by four bits. A later binary machine API still needs
actual packing/unpacking and incomplete-block rejection; it is not run here.

The independent mathematical codes are now defined:

- preorder tree: `E -> [E]`, `node () l r -> [N] ++ treeCode l ++ treeCode r`;
- input: first tree, separator, second tree, separator, its actual little-endian
  bit tags, then `endInput`;
- move: direction tag, branch tags in order, then `endMove`;
- certificate: actual move words concatenated in execution order, with implicit EOF.

Their exact proved lengths are `2*N+1` for a tree;
`2*Ns+2*Nt+b+5` for an input with bit width `b`; `path.length+2` for one move;
and the sum of those move lengths for a certificate. Empty and high-zero bit
words remain distinct words, even when their independently decoded values agree.

The actual measured emitters use an accumulator suffix. Tree emission first
binds the actual emitted right suffix into left emission, then constructs the
parent N cons; nil constructs an E cons. Bit and path emission bind their actual
recursive result before constructing the current symbol. No executable body
uses a specification append as an uncharged whole-list callback.

| Actual emitter | Proved returned value | Exact structural work |
| --- | --- | --- |
| `emitTreeRun t tail` | `treeCode t ++ tail` | `4*N+2` |
| `emitBitsRun bs tail` | `bitTags bs ++ tail` | `2*b+1` |
| `emitPathRun p tail` | `pathTags p ++ tail` | `2*d+1` |
| `emitMoveRun m tail` | `moveCode m ++ tail` | `2*d+3` |
| `emitCertificateRun ms tail` | `certCode ms ++ tail` | `2*W+1` |
| `emitInputRun s t bs` | `inputCode s t bs` | `2*M-1` |

Here `d` is path length, `W` the certificate word length and `M` the input word
length; none of these mathematical sizes is computed by the emitters. The move
emitter is a free nonrecursive adapter around path emission and two actual
conses, so it has no additional recursive-entry charge. Certificate emission
adds its own entry per move. Input emission has its specified wrapper entry and
constructs all three delimiter conses. Its subtraction-free cost theorem is
`cost+1 = 2*M`, justified by the exact positive input length; it also exposes the
natural subtraction form.

## Implemented linear prefix parsers

[LinearParser](../../Applications/Resources/RotationCertificate/LinearParser.lean)
contains actual bit, path and move parsers. A bit/path parser dispatches on its
next symbol. Its delimiter returns the empty decoded list and the exact supplied
suffix at work 2; EOF or a foreign symbol returns none at work 2. An element tag
calls the parser on the actual tail. Recursive failure adds entry+none, or 2;
success binds the actual decoded tail and suffix, reconstructing cons+some under
that entry, or 3. No unvisited suffix is scanned after either terminal case.

The move parser recognizes a direction, calls the actual path parser and returns
its actual path and suffix inside the existing `RotationMove` record. Its own
dispatch and returned Option add 2; record/pair packaging is free. It decodes
syntax only and does not claim the move is legal on a supplied tree.

The complete public recognition statements quantify over every raw word:

```
parseBitsRun raw returns some(bs,rest)
  iff raw = bitTags bs ++ [endInput] ++ rest
parsePathRun raw returns some(path,rest)
  iff raw = pathTags path ++ [endMove] ++ rest
parseMoveRun raw returns some(move,rest)
  iff raw = moveCode move ++ rest
```

These are equivalences to the independently defined codes, not only roundtrip
checks on encoder outputs. Complete whole-result prefix equations also prove
the exact returned suffix and work for any encoded value followed by arbitrary
material. Applying the actual parser to equal prefixes proves uniqueness of
both decoded value and suffix. Separate roundtrip theorems feed actual measured
emitter outputs directly to the actual parsers.

| Parser | Exact successful work | Bound for every raw word |
| --- | --- | --- |
| Bits of width `b` | `3*b+2` | `3*raw.length+2` |
| Path of length `d` | `3*d+2` | `3*raw.length+2` |
| Move at depth `d` | `3*d+4` | `4*raw.length+2` |

Failure bounds include missing delimiters, foreign symbols and reserved tags.
Successful consumption is exact: bit/path parsing consumes decoded length+1;
move parsing consumes `position.length+2`. Consequently an actual successful
move parse consumes at least two symbols and strictly shortens the unconsumed
suffix. These are proved facts about the executed parser, available for later
stream termination without computing a runtime suffix length.

[RotationCertificateCodecs](../../Examples/RotationCertificateCodecs.lean) retains
independently fixed literal words/costs and general clients. Empty, singleton and
two-node tree emitters cost 2,6,10. The empty-tree input word has length 5 and
emission cost 9; the one-step two-node input with threshold `[1]` has length 14
and emission cost 27. The decoder checks root and one-branch moves at 4 and 7;
missing move delimiters cost 4 or 6, and a leading foreign symbol costs 2.
Both directions/branches, arbitrary foreign suffixes, every reserved code 11–15,
redundant high zeros, exact consumption and prefix uniqueness are included.
Decoded root and nonroot moves can still be illegal on the selected tree; those
cases consume the existing actual partial executor and its distinct work.

## Remaining stack tree parser and full input parser

The tree and input prefix-recognition theorems still require their actual
parsers. Use a stack preorder parser, with frames awaiting a left child or
holding a returned left child while awaiting the right. A node tag pushes a
frame; nil feeds a value to a structural frame-resumption routine. A returned
right child constructs the parent and resumes the shorter stack. A resume result
requests the next tree or finishes with the actual tree and untouched suffix;
the input loop recurses only on its actual input-list tail.

A mathematical stack-prefix invariant can express the consumed parent/left
prefix without running another traversal inside the parser. Its two resume
identities and tree-induction consumption equation yield exact suffix soundness
and completeness. Frame potential pays for repeated resumes. The retained
concrete preparation derives targets `7*N+3` on an encoded tree and
`5*raw.length+2` on all raw input from the actual intended entries, stack conses,
constructed nodes and final Option. Those parser theorems are still unproved.
The existing resource/writer, stack execution and suffix-parsing interfaces were
inventoried; their unrelated grammars are not assumed to supply this parser.

Input parsing must bind the actual tree/separator/tree/separator/bit results,
then require the final suffix to be empty. Wrong/missing separators, missing tree
subterms, foreign/reserved tags, a missing bit delimiter and material after
`endInput` must reject. The intended exact successful work is
`7*Ns+7*Nt+3*b+15`, with all-input bound `20*(M+1)`; these remain targets until
the actual composition is proved.

A complete extra certificate move is another move to charge and check.
Different-size input trees need no separate size traversal: successful rotations
preserve size, and final actual structural equality rejects unequal sizes.
Preserve that semantic argument in the completed checker theorem rather than
charging an unbounded size computation as one operation.

## Remaining streaming verifier and polynomial conclusions

The intended checker charges one state entry. At certificate EOF it runs actual
structural equality. At a nonempty suffix it first decrements the actual binary
fuel; zero rejects before parsing. It then parses exactly one move, applies it
to the current tree, and recurses on the actual predecessor bits, returned tree
and unconsumed certificate suffix. Every failure stops immediately. Do not parse
the full certificate first or traverse a remaining list after failure.

The semantic target is acceptance iff the word encodes a successful mixed trace
whose length is at most the independently decoded threshold. Define the input
language by explicit input encodings of equal-size shapes with distance at most
that threshold; the verifier itself never computes distance. Soundness uses
binary predecessor correctness and the actual minimum interface. Completeness
chooses the attained minimum, which fits both the supplied threshold and `2*n-2`.

Every successful position has `path.length+2 <= n`, and successful preceding
moves preserve `n`. The certificate length formula is now proved. Composing
these laws with the attained minimum will give certificate size at most
`n*(2*n-2) <= 2*n^2`, including the empty case.
The input encoding bounds `n` by its explicit length `M`, yielding a prospective
witness bound `2*M^2`. This reasoning is not yet a completed encoded-witness Lean
theorem: the attained-minimum witness and completed verifier still have to be connected.

For work, let `W` be certificate-symbol length and `b` input bit width. The
implemented components bound each decrement by `3*b+2`, each raw positioned move
by `3*n+3`, and final equality by `3*n+2`. The width stays exactly `b`; successful
rotations preserve `n`. Each actual successful move parse now proves its exact
consumed prefix and strict suffix decrease. Compose these facts over streaming
execution to prove disjoint consumption and at most `W` nonempty attempts. A suitable derivation target
is then

`stream work <= (3*b+3*n+12)*W + 3*n+6`.

With a proved input-parser bound `20*(M+1)` and `n,b <= M`, a conservative full
verifier target is `32*(M+W+1)^2`. The parser coefficients and complete composition
are still unproved targets. Recalculate any coefficient from its actual helper
recurrences if the implementation changes; retain a universal polynomial bound
for every malformed or overlong input/certificate, not only successful runs.
A bound on rotation count alone does not count parsing, bit work, position
traversal, reconstruction or equality.

The remaining fixed cases include zero fuel before parsing, a legal rotation and
inverse at thresholds one and two, long borrow with a short witness, malformed
and trailing input, unequal sizes, and arbitrary unparsed suffixes after a stale
position or exhausted-fuel failure. The now-proved minimum-versus-route example
must be connected to the actual encoded verifier.

The final source-level conclusion must include exact syntax, codec erasure and
round trips, soundness, completeness, a polynomial-size witness theorem and a
uniform polynomial work theorem for the actual measured checker. Membership in
a named formal machine NP class additionally needs that machine's encoding and
cost-simulation bridge. No assumed `polynomialTime` field, source-level operation
count or historical prose supplies that bridge. Assess the full canonical
FDSA-5-93 requirement against the completed statements before qualification.

## Remaining tree-parser derivation

This unformalized derivation was preserved from the 20 November 2026 codec
preparation. The implemented linear parsers above do not yet discharge it.

### A structurally recursive stack tree parser

Use concrete frames `needLeft` and `needRight leftTree`. Define a free control
result `done tree` or `next frames`. These are control packaging, not charged
Option returns.

`resumeTreeRun frames t` recurses structurally on frames:

- Empty frames: return `done t`, charging the resume entry1.
- `needLeft :: outer`: return `next (needRight t :: outer)`, charging entry1
  and the replacement frame cons1.
- `needRight l :: outer`: construct the actual node(l,t), charge entry1 and
  node1, then resume the shorter outer stack with that returned node.

`parseTreeLoop raw frames` recurses structurally on the actual input list:

- EOF or foreign tag returns none at2.
- N charges entry1 and a `needLeft` cons1, then parses the actual tail.
- E charges entry1 and binds `resumeTreeRun frames nil`. A `done t` produces
  the one final `some(t, actual tail)` at1; `next frames'` parses the actual tail
  with frames'. Returning that recursive result directly constructs no Option.

No loop body computes a suffix length or reparses a consumed prefix. There is
no problematic mutual recursion: resume only traverses frames and returns
control; the input loop invokes itself only on its structural list tail.

### Soundness invariant with an independent prefix description

Define a mathematical `stackPrefix`, never used by the executable parser:

```
stackPrefix [] = []
stackPrefix (needLeft :: outer) = stackPrefix outer ++ [N]
stackPrefix (needRight l :: outer) = stackPrefix outer ++ [N] ++ treeCode l
```

The resume proof has two precise outcomes:

```
resume frames t returns done u
  -> stackPrefix frames ++ treeCode t = treeCode u
resume frames t returns next frames'
  -> stackPrefix frames ++ treeCode t = stackPrefix frames'
```

Both follow by structural frame induction. In the needRight branch, the
induction consumes exactly the independently defined code of node(l,t).
Then input-list induction gives the useful general soundness invariant:

```
parseTreeLoop raw frames returns some(u,suffix)
  -> stackPrefix frames ++ raw = treeCode u ++ suffix.
```

For N, the pushed-frame prefix supplies the consumed N. For E, substitute the
corresponding resume identity; `next` then uses the tail induction hypothesis.
The empty stack gives the desired forward prefix theorem. A converse for
arbitrary stacks is unnecessary.

### Completeness and exact successful work

Let `finishRun frames t rest` mean the actual measured resume followed by its
control branch: done creates the final some, next invokes the input loop on rest.
There is no extra helper-entry charge if this is only the named expression
already used by the E arm, rather than an extra executed state.

Prove by tree induction the whole-result consumption equation

```
parseTreeLoop (treeCode t ++ rest) frames
  = let actual := finishRun frames t rest
    (actual.value, (7*t.numNodes+1) + actual.cost).
```

The nil tree contributes its E-loop entry1. For a node, the N entry/push gives2,
left consumption gives `7*L+1`, needLeft resume/replacement gives2, right
consumption gives `7*R+1`, and needRight resume/node gives2 before resuming the
outer frames. Their sum is `7*(L+R+1)+1`. This derivation binds actual intermediate
results and does not erase failed suffix continuations.

For empty frames, finish costs2 (resume entry and final some), so every encoded
tree followed by arbitrary material returns precisely its tree and that material
with cost `7*n+3`. Together with soundness this proves the exact suffix iff,
round trips and code injectivity, without assuming a parsing oracle.

### Uniform work, including malformed input

Structural frame induction proves two amortized resume inequalities:

```
done result at cost c: c <= 2*frames.length+1
next frames' at cost c: c+2*frames'.length <= 2*frames.length+2.
```

Use these in input-list induction to obtain
`parseTreeLoop raw frames` work `<=5*raw.length+2*frames.length+2`.
The N branch adds2 and one frame; a continued E branch spends its resume cost
against the decreased/replaced frame potential. A completed E branch stops and
retains the arbitrary suffix. Empty initial frames give `<=5*raw.length+2`.

Keep the previously fixed malformed cases: `[N]` fails at4, `[N,E]` fails at7,
and `[E,rotR]` returns nil with unchanged foreign suffix at3. Reserve all expected
values before coding. If an actual helper design changes these costs, account
for its executed events and update the derivation explicitly, never weaken the
full semantic or polynomial requirement to accommodate a proof failure.

The eventual input parser binds actual tree/separator/tree/separator/bit results,
then checks the actual final suffix is empty. Successful work remains the target
`7*ns+7*nt+3*b+15`; failures stop at the failed component. These are preparation
targets until the actual definitions and complete Lean proofs are compiled.

## Remaining verifier protocol and independent cases

The following retained specification fixes actual failure order, universal raw
input bounds and independent expected cases before checker implementation.
The predecessor, execution and linear-parser cases already have checked owners
above; tree/input parsing and stream cases remain proof targets. Coefficients
are derived targets, not existing Lean verifier theorems.

### 3. Streaming checker and complete public conclusions

Implement `checkStreamRun bs current target certificate` as follows:

1. Charge its entry. Empty certificate calls actual `eqTreeRun`.
2. On nonempty certificate, first execute `decFixedRun bs`; zero returns false
   without parsing a move.
3. Parse exactly one move. Failure returns false. On success apply that move to
   the **current returned tree**; failure returns false.
4. Recurse using the returned predecessor bits, returned tree, and returned
   unconsumed certificate suffix. No equality check is run before the final EOF.

This intentionally specifies failure order. Do not use a list fold that still
traverses its suffix after an Option accumulator has failed. No full certificate
parse occurs before this streaming execution. A pure complete-certificate
decoder may be a separate useful client, but must not replace the actual stream.

The exact semantic contract is:

```text
(checkStreamRun bs s t cert).1 = true ↔
  ∃ moves, cert=certCode moves ∧ applyMoves? moves s=some t ∧ moves.length≤V bs.
```

Prove it from decrement arithmetic and partial execution, retaining fixed width
after every success. `verifyRun input cert` charges its wrapper entry, executes
the input parser, returns false on failure, and otherwise calls this stream.
Required final public theorems, all tied to that actual `verifyRun`, are:

```text
accept_iff:
  (verifyRun input cert).1=true ↔
  ∃ s t bs moves, input=inputCode s t bs ∧ cert=certCode moves ∧
    applyMoves? moves s=some t ∧ moves.length≤V bs

sound: (verifyRun input cert).1=true → Yes input
complete_small: Yes input → ∃ cert, cert.length≤2*input.length^2 ∧
  (verifyRun input cert).1=true

work_all: (verifyRun input cert).2 ≤ 32*(input.length+cert.length+1)^2
```

These are proposed proof targets, not proved receipts. Their pointwise scope
includes malformed and overlong input/certificate words. Here is a concrete
coefficient route, rather than a whole-bound premise: with decoded source size n,
bit width b and certificate length W, at most W nonempty stream attempts occur.
Their successful parsings consume disjoint prefixes; total move-parser work is
at most `4W+2`. Decrement work per attempt is at most `3b+2`, move work at most
`3n+3`, stream entries at most `W+1`, and terminal equality/false at most `3n+2`.
Thus the deliberately slack stream target

`work ≤ (3b+3n+12)*W + 3n+6`

follows from actual component recurrences and node preservation after successful
prefixes. Valid input gives n,b≤M. Add the input parser and verifier entry to
obtain at most `6MW+12W+23M+27`; invalid input rejects within the input-parser
envelope. Writing `z=M+W`, use `6MW≤3z²` and `12W+23M≤23z` to obtain the stated
`32(z+1)²`. Recalculate if helper implementation adds charged events; preserve
the universal polynomial requirement even if a larger coefficient is needed.

For the witness bound choose the **attained minimum** from `Shape.distance_spec`.
It is at most k and at most `2n-2`. Every successful move has path length+2≤n,
so `|certCode moves|≤n*(2n-2)≤2n²≤2M²`. Empty/singleton shapes use the empty
trace. Neither this witness choice nor `V`, distance, n, M or W is computed by
the verifier. The inequality is a theorem about its explicitly represented data.

### 4. Independent literal cases fixed before coding

Let `U=node () E E`, `L2=node () U E`, `R2=node () E U`,
`L3=node () L2 E`, `B3=node () U U`, and `R3=node () E R2`.
Root moves encode `[rotR,endMove]` or `[rotL,endMove]`; right-at-left encodes
`[rotR,pathL,endMove]`. Costs in the checker table concern `checkStreamRun`,
excluding the separately charged input parser/wrapper.

| Fixed-width input | Expected Option | Exact cost |
| --- | --- | ---: |
| `[]` | none | 2 |
| `[1]` | some `[0]` (not `[]`) | 3 |
| `[0,1]` | some `[1,0]` | 6 |
| `[0,0,1]` | some `[1,1,0]` | 9 |
| `[1,0,0]` | some `[0,0,0]` | 3 |
| `[0,0,0]` | none | 8 |

| Structural/parser case | Expected result and observation |
| --- | --- |
| Tree codes | `E:[E]`; `U:[N,E,E]`; `L2:[N,N,E,E,E]`; `R2:[N,E,N,E,E]`. |
| Tree prefix `[E,rotR]` | some `(E,[rotR])`, cost 3; the foreign suffix is untouched. |
| Tree `[N]`; `[N,E]` | none, costs 4 and 7. No fabricated missing child. |
| Move `[rotR,endMove]`; `[rotR,pathL,endMove]` | Root/right-at-left, costs 4 and 7. |
| Move `[rotR]`; `[rotR,pathL]`; `[endMove]` | none, costs 4, 6, 2. |
| Bits `[endInput]`; `[bit0,bit0,endInput]`; `[bit0,bit0]` | some empty / some two zero bits / none; costs 2/8/6. |
| Equality `E,E`; `U,U`; `L2,L2`; `L2,R2` | true/true/true/false, costs 2/5/8/4. Last case skips both right subtrees after the left mismatch. |
| Root right on L2; root left on L2 | some R2 / none, positioned costs 5/3. |
| Right-at-left on B3 | none, positioned cost 5; root right rotation on the reached U is illegal. |
| Nonempty path at E | none, cost 2, independent of remaining path length. |

| Source → target; bits; certificate | Expected stream result and exact cost |
| --- | --- |
| E→E; `[]`; empty | true, 3 |
| U→U; `[]`; empty | true, 6 |
| L2→R2; `[]`; empty | false, 5 |
| L2→R2; `[]`; any nonempty word | false, 4; neither parser nor move/equality executes |
| L2→R2; `[1]`; root right | true, 22 |
| L2→R2; `[1]`; root left | false, 12; illegal rotation stops before equality |
| L2→L2; `[1]`; right then left | false, 19; second zero-fuel failure skips parsing that move |
| L2→L2; `[0,1]`; right then left | true, 38; a legal non-shortest witness is allowed |
| L2→R2; `[0,0,1]`; root right | true, 28; longer borrow, no unary expansion |
| L3→R3; `[0,1]`; root right then right-at-left | false, 33; second move was legal initially but is illegal in the reached B3 |
| L3→B3; `[1]`; root right | true, 25 |
| L3→B3; `[1]`; normalization connection route | false, 19; actual route is right/right/left at root, length 3, while distance is 1 |
| E→U; `[]`; empty | false, 3; unequal sizes need no explicit size pass |

The last stale-path and short-witness cases connect respectively to
`RotationDistanceExample.stale_position_fails` and `initially_legal_moves.1`.
For the latter, `rightPositions L3=[[],[]]` and `rightPositions B3=[[]]`, so
`connectionMoves L3 B3` has exactly the displayed three moves. One actual root
move and distinct endpoints establish distance one. This fills the maintained
paper's previously missing concrete normalization-route separator.

Full wrapper calibration: `verifyRun (inputCode E E []) []` should be true
with cost `1+15+3=19`. The one-step L2→R2 instance with `[1]` has input length
14, parser cost 46, stream cost 22, hence total 69. Input trailing any tag after
endInput rejects. Reserved tags, repeated separators, an early endMove, missing
tree branches, and a path with arbitrarily many branch tags before its delimiter
must all satisfy `work_all`. Appending any suffix after the stale-path failure
changes neither its Boolean nor stream cost; no suffix parse occurs. With
threshold `[1]`, appending a second move of arbitrary path length after the
first successful move also rejects before parsing that second move.

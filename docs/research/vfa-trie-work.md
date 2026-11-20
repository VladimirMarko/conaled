# Trie: measured arithmetic and collision complexity

This note completes the resource correspondence accompanying
[the Trie source ledger](vfa-trie.md). The canonical owner is
[CTB-15's source specification](../history/textbooks/checkpoint-012/books/vfa/records/research/specifications/1013-Trie.md).
CTB-94 supplied the pure arithmetic, trie and collision semantics; CTB-95
supplies measured recurrences, the sequential successor exercise and the four
qualified collision bounds. The primary source remains VFA 2.1 `Trie.v`,
26,268 bytes, SHA-256
`a5af2b4db4c2cb639a8deb063e57909e11eb44ee763782ad0af9afbf45a78f3e`.

The observations below count declared source operations. They are tied to the
actual measured program by result erasure. Their asymptotic theorems concern
those counts; they do not certify a compiler's machine instructions, allocation,
garbage collection or elapsed time. All implementations use the existing
`Resources.Measured`, `bind`, `reweight` and `run`. The collision algorithms
specialize one common measured client rather than introducing four executors.

## Maintained owners

| Owner | Responsibility |
| --- | --- |
| [PositiveArithmetic](../../Applications/Resources/PositiveArithmetic.lean) | Actual successor, all eighteen carry-addition branches and all nine comparison branches, with value erasure and bit-length bounds. |
| [PositiveCounter](../../Applications/Resources/PositiveCounter.lean) | Canonical digit observation, full measured binary-counter bridges, same-trajectory potential accounting, positive and zero-capable counters. |
| [CollisionWork](../../Applications/Resources/CollisionWork.lean) | One polymorphic query-before-write client, invariant/decoder transport, cost projections and counter potential; actual first-operand unary addition. |
| [PositiveTrie](../../Applications/Resources/PositiveTrie.lean) | Exact raw lookup/insertion instrumentation, native-positive collision client, sum bounds and the single-long-key family. |
| [CollisionHistory](../../Applications/Resources/CollisionHistory.lean) | Explicit newest-first functional-update histories, actual unary equality and signed comparison, both source counter realizations and independent-parameter bounds. |
| [CollisionRedBlack](../../Applications/Resources/CollisionRedBlack.lean) | Accepted balanced-tree operations with actual binary comparisons, finite distinct-key invariants and a measured binary counter. |
| [CollisionGrowth](../../Applications/Resources/CollisionGrowth.lean) | Half-open bounded natural keys, shifted positive encoding, corrected finite bounds, ordinary asymptotics and the unary interval lower family. |

The six connected example owners are
[PositiveArithmeticWork](../../Examples/PositiveArithmeticWork.lean),
[PositiveCounterWork](../../Examples/PositiveCounterWork.lean),
[PositiveTrieWork](../../Examples/PositiveTrieWork.lean),
[CollisionHistoryWork](../../Examples/CollisionHistoryWork.lean),
[CollisionRedBlackWork](../../Examples/CollisionRedBlackWork.lean) and
[CollisionGrowth](../../Examples/CollisionGrowth.lean).
They fix independent expected values and costs, exercise public theorems and
retain the small, repeated, signed and long-key boundaries.

## Actual arithmetic, with separate visit and write observations

Write `b p = PosNum.natSize p` for the positive bit length and `ν p` for its
unshifted natural value. The accepted pure owner proves
`2^(b p-1) ≤ ν p < 2^(b p)` and `b p = Nat.log2 (ν p) + 1`. The plus-one
convention matters at one and at every power of two.

`PositiveArithmetic.succRun` returns the actual successor together with a pair
of counts. Its reweightings `succVisitRun` and `succWriteRun` observe that same
run, using these exact charges:

| Source branch | Entered constructor-pattern visits | Changed-digit writes |
| --- | ---: | ---: |
| `one` | 1 | 2 |
| `bit0 p` | 1 | 1 |
| `bit1 p` | 1 plus the child's visits | 1 plus the child's writes |

The terminal positive one writes its low bit to zero and adds a high one.
This explains two changed digits without asserting two physical allocations.
The result of each recursive measured call supplies the returned constructor.
`succRun_value` identifies the result with `PosNum.succ`; visits are at most
`b p` and writes at most `b p + 1`. The all-one carry family attains these
bounds. The examples distinguish one from two at the terminal case, three
visits from four writes for seven-to-eight, and immediate termination for
ten-to-eleven.

`addcRun` follows all eighteen source branches, with the Boolean carry retained
as an argument. Every entered branch costs one. A terminal operand can invoke
the measured successor of a strict child of the remaining operand; that work
is included, in either operand orientation. The bound
`addcRun_cost_le` is the maximum of the two input bit lengths. Erasure reaches
the accepted source `addc`, including both carry values. The pure result-size
theorem then yields the result-bit-length and result-logarithm bounds. These
proofs do not replace the source recurrence by a primitive addition with an
assumed cost.

`cmpRun` also follows the actual recurrence. Both nonterminal operands strip
one bit and recurse; mixed low-bit cases inspect the returned higher-bit
ordering before selecting the result. The exact terminal-inclusive count is
`min (b p) (b q)`, and the value is `PosNum.cmp p q`. Equal-length families
realize the worst case. Comparison against one terminates after one call even
when the other key is arbitrarily long, so a universal tight bound in the
first argument's length would be incorrect.

## The sequential successor exercise

The selected source exercise route is successive increments from positive one.
No random-input distribution or expected-cost assumption is introduced.
The accepted digit observation is `(ν p).bits`, low bit first. Its constructor
equations, nonemptiness and length are supplemented by canonicality and the
`BinaryCounter.value` interpretation in `PositiveCounter`.

`digits_succ` gives the exact digit result. The stronger
`succWriteRun_digits` identifies both the result and write count with the
existing `BinaryCounter.incWithCost`. Thus the existing potential theorem
applies to this actual source run, not to a separate numeric simulation.
`positiveAdvanceRun` executes the measured step through `Resources.run`, and
its complete digit-and-cost result equals `BinaryCounter.advanceWithCost`.

For `N` increments from `p`, the exact identity is

\[
 W + \operatorname{ones}(\operatorname{digits}(p_{\rm final}))
 = 2N + \operatorname{ones}(\operatorname{digits}(p)).
\]

The arbitrary-start bound retains initial potential. From positive one the
initial potential is one, and the final positive number has at least one one
bit, so `W ≤ 2N`. For `N > 0`, the rational average is at most two. The before
states are exactly `1,…,N`, and the value after `N` transitions is `N+1`.
Observing `N` states without incrementing the last takes `N-1` transitions;
the public prefix theorem and empty/small examples retain that distinction.

`numDigits` extends the same observation to existing `Num.zero` by the empty
list. `numAddOneRun` charges one first write at zero and otherwise delegates to
the measured positive successor. Its value is the actual Num `c+1`, its Nat
observation is `c+1`, and `numAddOneRun_toZNum` reaches signed `c.toZNum + 1`.
The measured digit bridge, nonnegative interpretation and local potential
identity supply the zero-start collision counter. Wrapper dispatch is charged
separately by its clients. The source cost claim concerns this reachable
nonnegative trajectory, not arbitrary negative initial counters.

The sparse-increment example uses the same executor and potential theorem on
increment/stay commands. Counter work is charged on the duplicate branches of
the actual collision run; no extracted sequence is run a second time to justify
its amortized bound. General persistent branching would need its own resource
contract and is not inferred from this sequential result.

## One collision client and four concrete observations

`CollisionWork.step` takes measured read, write and increment operations plus
a loop tariff. It reads the key first. A true result increments the actual
counter and leaves the table alone; a false result writes true and leaves the
counter alone. `CollisionWork.run` uses the established executor and adds one
terminal observation. Counter and table carriers have independent universes.

The common API supplies exact branch bills, invariant preservation, transport
of both state coordinates to accepted `Search.Collisions.run`, additive
reweighting, and sums over the actual trajectory. Its allowed-key versions
retain finite-support assumptions where an operation bound needs them.
Counter potential telescopes over the selected duplicate branches of this same
client. None of those generic lemmas invents a cost for a supplied operation.

The independent result remains
`Search.Collisions.count xs = xs.length - xs.dedup.length`.
Three copies of a key contribute two collisions. Each measured realization
erases to the accepted source program or its accepted total-table client.
`CollisionGrowth.represented_counts` connects all four programs on injectively
represented natural inputs; it does not identify their costs.

### Explicit functional-update histories

`CollisionHistory.History κ` is the ordinary list `List (κ × Bool)`, newest
update first. Its decoder is the accepted constant-false function followed by
`Function.update`. A write constructs one history cell without traversing old
bindings. Lookup tests a cell's written key before consulting the rest and
charges one empty-terminal observation if the search reaches the end.

Eight coordinates distinguish equality tests, equality work, lookup terminals,
created history cells, counter work, counter wrapper calls, loop transitions
and the final loop terminal. Their unit-price total is explicit. The `Good`
invariant says that keys are distinct and all stored values are true. It is
preserved because a new cell is created only for a key whose lookup is false.
`run_history_length` proves that each empty-start processed prefix has exactly
as many cells as distinct keys in that prefix. The finite support invariant
bounds this by the complete input's distinct count.

Unary equality is the displayed Boolean recurrence: zero/zero is true, exactly
one zero is false, and two successors recurse. Its actual terminal-inclusive
work is `min x y + 1`; its value is natural equality. The source counter uses
`CollisionWork.unaryAddRun c 1`, which recurses on its first operand and costs
`c+1`. Commuting it to `1+c` would change this model. If the number of collisions
is `r`, exact counter accounting gives `2Wcounter = r(r+1)` from zero.

The signed comparator follows the inspected `ZNum.cmp` branches. Sign/wrapper
dispatch costs one, a nonzero same-sign branch uses the measured positive
comparator, and the negative branch reverses its two magnitudes. Selecting `.eq`
or `.lt` adds one. `signedEqRun` has the accepted source Boolean equality and
its integer-observation bridge; `signedLtRun` agrees with integer less-than.
For

\[
b_Z(z)=\max(1,\operatorname{Nat.size}(|z|)),
\]

zero has length one, and equality/less-than work is bounded by either
argument's `bZ + 2`, hence by `2(B+1)` for an input bit bound `B`.
This is a declared realization of equality, not an exact-cost assertion about
Lean's `DecidableEq` implementation. The signed client uses the measured Num
increment, with exact write potential and separately counted wrapper calls.
Arbitrary represented histories and Nat/Num starting counters have source-loop
erasure; the complete-program bounds start from zero and empty history.

### The accepted balanced tree

`CollisionRedBlack` consumes the existing Redblack lookup, insertion, balance,
shape and height contracts. It introduces no further tree algorithm. Its
invariant combines actual search ordering, a valid red-black shape, and stored
keys in an explicit finite set. The proof of size at most that set's cardinality
uses the tree's actual key enumeration and its no-duplicates theorem. Thus
every reached prefix has height at most `2 log₂(D+1)` when the permitted set
has `D` keys.

The measured lookup and insertion retain all accepted table coordinates,
including balancing and syntactic construction. The supplied comparator is
the concrete signed less-than run above, not a unit-cost comparison. The
counter is the same measured Num increment; one counter dispatch and one loop
entry are separate overhead observations. Its total is table work plus counter
writes plus overhead. Empty input has one terminal observation.

### The native-positive trie

`PositiveTrie.lookRun` follows the raw `BinaryTree` equations. A leaf returns
the default after one call, and a node either returns its value at positive
one or recurses into the actual selected child. Calls are at most the key's
bit length; lookup constructs no nodes. The explicit-default wrapper preserves
that behavior for arbitrary payload universes and all raw trees.

`insRun` follows all six key/tree branches, including default-filled paths
created below a leaf. Both its recursive-call count and syntactic
node-construction count are exactly the key bit length, independent of the
old tree's size. Its measured result is the actual source insertion. Lookup
after insertion visits the entire inserted path; overwrite still constructs
that path even when the resulting tree's number of nodes does not grow.

The trie collision client retains five projections: trie calls, node
constructions, unary counter calls, loop steps and the loop terminal. The source
counter is literally `1+c`; under the declared first-operand unary-addition
model it costs two calls including the terminal. It differs from the unary
history client's `c+1` model. `totalWork` is the additive sum of these five
observations.

For the family obtained by applying `bit0` `h` times to one, numeric value is
`2^h` and bit length is `h+1`. Empty insertion creates `h+1` nodes; lookup of
that inserted key visits `h+1` nodes. There is only one distinct explicitly
inserted key. Intermediate default nodes are not separate insertion events.
This checked family rules out an unconditional trie traversal bound based
only on the logarithm of the number of distinct writes.

## Independent finite bounds

Let `n` be input length, `D` its distinct-key count, `M` an upper bound on
natural key magnitude, `B` an upper bound on represented binary key length,
and `S = Σ b(key)` for native-positive inputs. Every empty input is included.
The complete unit-price operation totals satisfy:

| Actual measured program | Explicit bound |
| --- | --- |
| Unary update history | `n D (M+1) + n D + n(n+1) + 4n + 1` |
| Signed-binary update history | `2 n D (B+1) + n D + 6n + 1` |
| Balanced signed-binary tree | `90 (n+1)(B+1)(1 + log₂(D+1))` |
| Native-positive trie | `3S + 3n + 1`, hence `3n(B+1)+1` |

For the history bounds, the `nD` equality-test dispatch count is retained
separately from equality work. The first bound includes actual unary counter
work, and the second includes its binary counter's amortized writes. History
creation and all terminal/wrapper/loop observations are present.

The balanced-tree provider retains the more precise tariff before the displayed
majorant. With comparison tariff `K` and unit table prices it is
`2(32+4K) log₂(D+1)+5`; the complete collision bill is at most
`n*(tariff+4)+1`. Substituting `K=2(B+1)` gives the displayed corrected bound.
For nonempty input it also gives `180 n(B+1)(1+log₂(D+1))`. No assumption
identifies `D` with `n` or silently omits counter work when both `B` and `D`
are small.

The trie component bounds remain available before taking their total: at most
`2S` calls, at most `S` constructions, at most `2n` unary counter calls,
exactly `n` loop steps and exactly one final terminal. Source examples retain
the actual positive numeral list separately from an encoded natural list.

## Bounded natural keys and asymptotic progression

For the comparison, choose the half-open condition `0 ≤ key < 2n` and an
input length at most `n`. Natural keys already satisfy the lower endpoint.
The positive encoding has numeric value `key+1`, so the bit-length proof must
include that offset. The signed representation observes the same natural
value through ZNum. Both maps specify already represented inputs for the
collision run; constructing those representations is outside its work count.

`CollisionGrowth.logScale n = 2 + Nat.log2 (2n+1)` is at least two. The actual
encoded-key length plus one and the distinct-key logarithm are bounded by
this scale. Signed magnitude has the corresponding bound. For `n ≥ 2`, the
real cast of this scale is at most `5 log₂ n`. The explicit finite bounds are

| Client on the stated bounded inputs | Bound using `L = logScale n` | Standard upper family |
| --- | --- | --- |
| Unary history | `4(n+1)^3` | `O(n³)` |
| Signed-binary history | `8(n+1)^2 L` | `O(n² log n)` |
| Balanced tree | `180(n+1)L²` | `O(n(log n)²)` |
| Native-positive trie | `6(n+1)L` | `O(n log n)` |

The four standard theorems use the existing `Asymptotics.IsBigO` API over real
casts of these actual measured counts. They quantify over any indexed list
family satisfying the explicit length and key hypotheses. The small-size
corrections occur in the finite bounds; no operation theorem takes a logarithm
of zero or assumes empty input disappears.

For the unary stage, the distinct interval `List.range' n n` supplies the
lower family `n,n+1,…,2n-1`. Each fresh lookup traverses all earlier cells,
and each unary equality costs at least `n+1`. Its equality work, and therefore
its complete total, is at least

\[
 (n+1)\frac{n(n-1)}2.
\]

The empty and singleton cases are retained. For `n ≥ 2`, `n³` is at most four
times this expression. Together with the same family's cubic upper bound,
this gives a tight cubic family. The binary-history, balanced-tree and trie
results remain upper bounds; no matching lower family for those stages is
claimed.

## Operational boundaries and the array comparison

The textbook's imperative comparison can use an array of `2n` Boolean cells
for the selected half-open key range, with constant-time indexed access under
an explicitly assumed RAM model and linear initialization. A closed endpoint
would instead require `2n+1` cells. This is a contextual model assumption;
there is no new verified mutable-array or IO realization in this chapter.
The source's broad assertion about pure functions is qualified by the actual
persistent representation and primitive model. No general impossibility
theorem for all pure indexed-update interfaces is asserted.

Native-positive lookup takes a PosNum key directly. The pure abstraction
`abstract table n` includes shifted encoding only as a mathematical observation
unless that execution is separately selected. `PosNum.ofNatSucc` recurses on
Nat, so neither its bijection nor the representation Square proves logarithmic
Nat-to-positive conversion. Numeric casts, parsing, preprocessing and printing
remain separate. A different conversion algorithm would require its own cost
and realization proof.

Finite-word behavior is a value observation: the coalgebra can remain at an
absorbing leaf while reading a suffix, whereas actual lookup stops there.
Their value equality does not identify their operation counts. Changed-digit
writes, unary recursive calls, history cells and syntactic tree constructors
also remain distinct from physical heap objects, compiler sharing and native
integer instructions. No uninspected finite-word primitive is assumed to have
the declared structural cost.

Trie requests no timing benchmark. Its source computations and connected cases
are kernel-checked facts under the focused workflow. The unchanged Extract and
Redblack runtime suite remains historical checkpoint-041 execution evidence,
with original candidates and controls; current identity checks do not relabel
it as a new run. Frozen focused build/audit, complete actual-type assessment,
independent Standards/Spec review, exact reconstruction and successful durable
publication remain distinct acceptance gates. Whole-library and receiving
acceptance remain delegated, and all later units of all three books remain
part of the standing task.

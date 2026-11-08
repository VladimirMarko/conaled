# Total compositional memoization and retained execution

Issue [#263](https://github.com/VladimirMarko/conaled/issues/263) now has a
bounded implementation of the total representation and retained-execution
contracts proposed in [the source assessment](elegant-memoization-fit.md).
The implementation distinguishes equality of functions from reuse of their
computations. Both are checked, through different interfaces.

## Representation and extension

`Applications/Memoization/Representation.lean` gives a family of ordinary
`Equiv`s between stored carriers and total functions on a key domain. Empty
keys store unit, unit keys store one value, Boolean keys store a false/true
pair, sums store paired tables, and products store nested tables. Both inverse
laws hold for **every carrier value**, not only tabulated values. Extensionality
then proves result-map identity, composition and lookup naturality.

`map` is defined by lookup and tabulation. Its semantic law does not promise
cheap mapping or sharing. The interface makes no cost claim for an arbitrary
representation. `operation_eq_map` states the local lookup square that a new
result operation must satisfy; extensionality identifies its semantic action.
Domain encoding/decoding costs are likewise not erased by equivalence: the
`Fin 4` example has no measured transport tariff. The measured Fibonacci client
uses its native finite indices and does not invoke that transported interface.

Domain transport uses an actual `Equiv`, preserving the carrier and changing
lookup by the inverse key map. `transport_map` proves result naturality through
that change. `Examples/Memoization.lean` transports two Boolean flags to
`Fin 4` and reuses the generic map-observation theorem. A structural four-cell
increment's local lookup law also yields equality to semantic map through
`operation_eq_map`. The existing FFT
`Factor` tables instantiate this same contract using their existing
`get_tabulate` and `tabulate_get` proofs. The FFT algorithms were not changed.

`Words.lean` builds the recursive key shapes
`K 0 = Unit` and `K (d+1) = Unit ⊕ (Bool × K d)`. A proved equivalence identifies
them with Boolean lists of length at most `d`. The stored tree has one value
at every admitted word; `storedEntries_cells` gives the exact recurrence
`cells 0 = 1`, `cells (d+1) = 1 + 2*cells d`. Observation rejects overlength
words. Physical prefix restriction preserves admitted observations and composes
with repeated restriction. The independently chosen client retains the entire
word alongside its little-endian numeric value, so order and exact keys remain
observable. No finite table of all finite words is asserted.

## Retained state and actual recursive calls

`Cache.lean` adds a small local `Storage` contract to a representation: measured
read/write implementations and their lookup equations. `call` reads a stored
`Option` value. On a hit it returns that value and the unchanged state without
calling the body. On a miss it calls the supplied body, accepts its returned
state, then writes the result into that state. `Valid` fixes the function
meaning for this retained instance. `call_correct` proves value agreement,
validity and presence of the queried value; `repeat_hit` proves a repeated
query adds no body evaluation. `Retains` and `call_retains` also preserve
previous populated entries when the body does.

`Slots.lean` supplies inhabited storage as nested finite products, with
structural read and path update. Its successor representation agrees with the
sum of a singleton and the preceding keys through `splitEquiv`. Read and
write counters increment during traversal; each operation on key `i` visits
or rebuilds exactly `i+1` cells. The implementation is a unary table, so this
is deliberately not a constant-time lookup claim. Eager setup constructs one
empty cell per admitted key, with a checked counter and equality to empty
tabulation.

`Fibonacci.lean` is well-founded recursion on the requested natural number.
Both smaller calls invoke the **same memoized evaluator**, with the second
using the first call's returned cache. The answer agrees with the independent
recurrence for every admitted input and every valid starting cache. Previous
entries survive, the requested answer is stored, and querying it again has
exactly one hit, zero body evaluations, `n+1` read visits and zero writes.
The generic cache theorem discharges the local miss obligation; the recursive
proof does not assume the complete evaluator's correctness.

The workload uses existing `Resources.Measured`, additive tuple observations
and `Resources.run`. It introduces no new global cost monad. The observation
tuple is `(hits, body evaluations/misses, read visits, rebuilt path cells)`.
The checked workload at input 10 has the following counts:

| Workload | Result | Body evaluations | Hits | Read visits | Rebuilt cells |
|---|---:|---:|---:|---:|---:|
| Ordinary recursion | 55 | 177 | Not applicable | Not measured | Not measured |
| Cold memoized query | 55 | 11 | 8 | 110 | 66 |
| Next query on its returned cache | 55 | 0 | 1 | 11 | 0 |

Cold setup additionally constructs 11 empty cells. Rebuilding before each of
two queries incurs 22 body evaluations and two setups; the retained workload
incurs 11 body evaluations and one setup. The zero-input control has the same
one body evaluation as ordinary recursion and incurs extra setup/read/write
work. This establishes saved body evaluations for the stated workload, not a
wall-clock speedup. Arithmetic, result size, reference counting, reclamation,
compiler optimization, and peak live storage are excluded. The write count
measures source-level path reconstruction, not physical heap allocations.
Keeping old persistent versions can retain more storage than the latest table.

Universal proofs cover correctness, validity, entry retention and repeated
hits. Closed-form cold-count equations for all natural inputs are not claimed.
The executable checks test the proposed cold-count equations for inputs 0
through 12, separately from the kernel-checked input-10 observations.

## Controls and validation

The independent word/Fibonacci contracts were frozen before table code was
written. Checked cases cover all elementary constructors, arbitrary carrier
round trips, key equivalence, empty and boundary words, rejected overlength
words, repeated restriction, recursive base cases, repeated versus rebuilt
instances, and stale/malformed caches. A cache valid for the constant function
7 is rejected for the constant function 8; without validity, its hit returns
the old 7. This makes the instance boundary an explicit proof obligation.

Run `direnv exec . lake env lean --run scripts/MemoizationTest.lean` for the
executable assertions, after building `Examples.Memoization`. The script
checks actual returned state and counters, full ordered word results,
restriction/rejection and stale-instance behavior. Normal `check.sh` integrates
the formal examples and exhaustive axiom audit. Independent acceptance reviews
and exact candidate receipts are maintained by the enclosing orchestration.

## Source boundary and remaining owners

The [pinned talk](https://github.com/conal/talk-2014-elegant-memoization/blob/470b6d828b92a30cb061d47587b6c790423f0aa8/elegant-memoization.lhs)
and [MemoTrie implementation](https://github.com/conal/MemoTrie/blob/dd3f6a2290d00872178ed304be3e061a1a5a8183/src/Data/MemoTrie.hs)
motivate the constructors and the requirement that recursive calls use the
memo interface. The source assessment records Hinze's strict-continuous-map,
coalesced-sum/smash-product and hyper-strict qualifications. These total Lean
proofs do not remove those qualifications. In particular, a Haskell constant
function can ignore bottom while Boolean trie lookup inspects it. That
counterexample is a source-semantic deduction, not a Haskell execution result.
Replacing memoization with its pointwise-equal function can remove the retained
computation. No Haskell benchmark or contextual-equivalence theorem is supplied.

Adopt the total representation and local retained-storage contracts, keeping
native clients available. The parser tables in #282/#304 return
`Decision (P word)`, whose type depends on the key. This homogeneous table API
cannot replace that contract directly. A dependent table or an exact tagged
adapter must retain parser instance identity, selected witnesses and view
validity. That adapter remains with #309/#235 and the memoization agenda;
recognition-only Boolean erasure is not a substitute. Language derivative tries
in #255 and these key-shaped tables therefore retain their distinct meanings.

#307 owns executable guarded-stream progress and can proceed independently.
#309 owns parser policy selection and arena lifetime; #193 owns broader
resource interpretation. General recursion, arbitrary function-valued keys,
non-strict equivalence, polymorphic/deep memoization and general space results
remain in the #8/#263 agenda. This bounded delivery does not resolve those
research questions or require the other consumers to adopt this storage layout.

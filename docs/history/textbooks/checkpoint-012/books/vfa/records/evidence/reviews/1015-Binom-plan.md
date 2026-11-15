# Independent bounded review — #1015 Binom plan

**Outcome: clear for planning after one statement-scope correction. No open findings.**
This is an independent source/reuse-plan review within the existing whole-book
workflow. It is not an ordinary implementation review axis, a compiler or
benchmark result, or acceptance of Binom or the running candidate. All new
algorithms, proofs, measured bridges, applications and executed measurement
work described by the plan remain future implementation obligations.

## Frozen inputs and correction history

The author announced the complete plan frozen before assessment. I read all
of those bytes and independently reconciled their source/provider claims.

| Version | SHA-256 | Size |
| --- | --- | --- |
| Initially reviewed `../specs/1015-Binom.md` | `70072768193116d551067b42be889c1e3296bb5969c6df6cec81e25f60552713` | 71,344 bytes; 843 lines |
| Corrected, final reviewed plan | `956eacc44542fc26fe5dee1b7a4cd119acb00f6f92ed82d46dc17ccdbdec77c7` | 71,393 bytes; 844 lines |

Root applied the single requested bullet correction under an initial-digest
guard after the author had finished. I independently compared the corrected
file against my in-memory original snapshot. The only changed block is the
canonical-size bullet beginning at original line 559: its length equality is
now explicitly at base zero, and its nonempty inequalities/log equation
repeat that premise. Every other character is unchanged. The final digest
and byte/line counts were independently checked.

| ID | Status | Finding and resolution |
| --- | --- | --- |
| `BINOM-PLAN-001` | Resolved | Section 8 introduced the mass/slot obligations under `priq' i`, then left the canonical `length = Nat.size mass` and logarithm formulas without an explicit base-zero scope. The rank-one singleton forest described below refutes the generalized reading. The final plan explicitly restricts that bullet and its inequalities/log formula to base zero. |

The counterexample is `q = [Node 0 (Node 0 Leaf Leaf) Leaf]`. It satisfies
`priq' 1`, ends in an occupied slot, has one slot and two keys, while
`Nat.size 2 = 2`. Thus the unshifted length equality would assert 1 = 2.
For a nonempty canonical forest at general base i the correct shift is
`Nat.size (mass q) = i + q.length`. Restricting the plan's existing formulas
to base zero is sufficient and matches its intended public queue bounds.
This is mathematical source inspection, not a newly compiled counterexample.

A separate **pre-freeze preparation clarification** is preserved here for
continuity. The author initially considered requiring antisymmetry or an
injective decoder for generic exact deletion. I pointed out that the literal
source maximum scan retains the first maximal root and the auxiliary removes
that same root. The author agreed before freezing and added the stronger
chosen-occurrence provenance obligation. No such excess generic premise is
present in either frozen version reviewed above; this was not a second
finding against the frozen plan.

## Source, inventory and required readings

- Complete VFA 2.1 `reference/vfa/vfa/Binom.v`: SHA-256
  `f73f18cac4c3a6a38a0e83d4194429eb7ab684ee68068a88025610a13d5c31ed`,
  13,042 bytes, 400 lines. I independently read the entire chapter,
  including every raw fallback, relation constructor, optional exercise,
  source demonstration and runtime exercise.
- `../source/Binom.inventory.json`: SHA-256
  `a353316c6502b49edd90d11b98171ecd396db60f940bfc17a77b5247bd2c1680`.
  All records, status metadata, exercise ranges/tags, the module and the
  command were inspected and compared with the plan.
- The inspected main candidate is
  `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`; its working tree is clean.
  The frozen Priqueue planning input has SHA-256
  `0028ed8013db98fb62e365eb31153ab5030d027bc9a3b9d06f7e8fbb43a42c7d`.
  Neither that plan nor current provider availability is chapter acceptance.

I independently retrieved both exact primary readings in memory and read all
their extracted page text. The ordinary web reader returned HTTP 403; the
bounded direct read-only requests returned HTTP 200. No reference file was
written or added to a deliverable.

| Reading | Independently verified identity |
| --- | --- |
| [Appel, Binomial Queues](https://www.cs.princeton.edu/~appel/Binom.pdf) | 20 pages; 820,707 bytes; SHA-256 `b5e6e8f3e7115ed4e7faffc629ac18f777fd21b77ffb5b061819e276f9d78b69` |
| [Sedgewick, section 9.7 excerpt](https://www.cs.princeton.edu/~appel/BQ.pdf) | 11 pages, printed 406–416; 236,099 bytes; SHA-256 `300abc44d593f97ed609dab095f3b4db08c956d21d0f2f129dafbef9e3e73d69` |

The plan correctly distinguishes the readings' explanations from VFA's
authoritative executable recurrences. In particular, the source permits
equal keys; the slide wording suggesting strict heap dominance is not copied
as an invariant. The textbook distinguishes resizing from fixed historical
capacity and separately discusses total insertion comparisons. Its imperative
linking and merge association are not source algorithms. Its separately
numbered exercises are not silently added to the VFA inventory.

Applicable AGENTS, architecture/domain guidance, GLOSSARY, language direction,
ADRs 0001/0002/0010, implementation workflow, README build/audit rules and
local user requirements were followed. The priority-queue reuse note,
computational-assumptions note, and resource/execution obligations were read;
consequential APIs were inspected directly rather than trusted from those
notes alone. No additional implementation review loop was started.

## Complete coverage check

All **44 inventory IDs occur exactly once and in inventory order**. Their
classifications agree: 22 definitions, 20 admissions, one source-proved record
and one grading item. All **21 exercise names, ranges, star counts and
required/optional tags** match in order. Ten are optional in the book and
remain mandatory here; none is advanced. The single module at line 28 and
single Eval command at line 68 have complete dispositions.

Two nonlexical gaps are handled explicitly. The forest relation is an empty
inductive placeholder even though the inventory calls it a definition; the
plan requires its real constructors and nonvacuity. The measurement exercise
has no named declaration, but still requires an actual executed experiment.
The grading constant does not become a mathematical stub in Lean. Source
merge validity is not treated as independent of its admitted join lemma.

The exact demonstration retains its left-fold insertion order, four dense
slots, two intervening Leaf slots and the complete rank-three tree. Checking
only its maximum or multiset would miss source algorithm changes; the plan
requires the stronger constructor result and its nine occurrences.

## Raw operations, shape and rank

BinaryTree has the source's value/left/right constructor order, so the carrier
reuse is direct. The source right link is a sibling link. The plan preserves
the different bound passed to the left child and the right sibling, the
perfect inner binary shape, and the requirement that a whole rank-n heap have
an empty outer right subtree. The inner tree has `2^n - 1` nodes and height n;
the whole heap has `2^n` keys and BinaryTree height n+1. Leftist rank and
ordinary binary max-heap order are not substituted for these properties.

I compared all operation cases with the source:

- Smash uses strict greater, retains the exact child placements, and chooses
  the second root on a tie. Its malformed-input Leaf result is preserved.
- Carry retains all five ordered patterns and the `smash t u` argument
  order. It places a nonempty carry at the first hole without scanning the
  remainder, and it does not trim a Leaf suffix.
- Join retains both empty-input bases and all eight occupancy cases. With
  all three slots occupied it emits the incoming carry and links the two
  operand heads; an alternative association is not declared equivalent as
  a source program merely because contents agree.
- Unzip traverses the right sibling spine, reconstructs detached roots and
  reverses their rank order through continuations. Its arbitrary-continuation
  equation appends `cont []` after `unzip t id`; applying cont to the final
  child forest is generally a different value. Heap deletion uses the id
  continuation only for the proper outer shape.
- Find-max inspects roots, initializes from the first occupied root and
  replaces only on strict improvement. Zero is not an empty sentinel.
- The deletion auxiliary skips exactly roots strictly smaller than its
  threshold. Its first qualifying root and malformed-node fallback remain
  visible, including reconstruction of any traversed prefix.
- Whole deletion composes the full maximum scan, auxiliary split and native
  join. Merge remains the literal zero-carry join.

The proposed recursive definitions have genuine structural decreases. No
fuel or termination assumption is needed. Generalized `priq' i` advances its
base through every list slot, including holes. Removing an absolute-rank-r
heap creates a child forest beginning at zero, not at the original forest's
base. The plan preserves that distinction in the auxiliary obligations.

## Relations, maximum provenance and interface use

The planned tree and forest relations preserve all permutations and all
multiplicities. Their equivalence with explicit finite contents has both
directions on every raw state. Totality, permutation closure and uniqueness
therefore have real witnesses; validity-guarded source wrappers are retained
even where a stronger raw theorem is available. Contents are mathematical
observations, not preprocessing inserted into executable operations.

The raw None characterization is sound: every Node contributes a key, so
empty contents means every forest slot is Leaf. Both maximum lookup and
whole deletion return None exactly in that case, even on raw forests. This
does not equate semantic emptiness with the literal empty list. Conversely,
smash's malformed fallback makes unguarded occurrence-preservation claims
false, and the plan retains the source shape/rank premises on those laws.

Each source permutation orientation was checked: smash concatenates its two
tree witnesses; carry places queue contents before carry contents; join
places carry contents before the two forest witnesses; merge relates any
output witness to concatenated input occurrences; deletion relates the
original witness to returned key cons residual witness. Residual keys have
a non-strict upper bound, so duplicate maxima can remain.

The generic first-maximum provenance obligation is sufficient under a lawful
total preorder. The maximum scan exposes the literal selected root, with all
earlier occupied roots strictly smaller and all later roots at most it. The
auxiliary must therefore remove that very root. There is no need to identify
arbitrary distinct keys in the same comparator equivalence class. A weaker
arbitrary-threshold lemma would not suffice. The planned tagged-key example
tests exactly this boundary without asserting residual stability.

The complete deletion chain includes child-forest validity and contents,
prefix reconstruction, native join, a real output witness and one-occurrence
loss. A theorem conditional on an impossible residual Abs is not allowed to
stand in for successful deletion. All eleven PRIQUEUE law obligations remain
future concrete proofs.

The proposed ExactQueue adapter matches the actual project types. Its
add-exactness and None fields quantify over every carrier state, so a subtype
of valid forests makes the source guarded laws applicable. `Valid := True`
is justified on that subtype, not on malformed raw trees. Unit/OrderDual
encoding reverses minimum priority into maximum Nat without deleting repeated
keys. Source residual bounds plus permutation/reflexivity supply the existing
bound on original entries. The separate native merge law is necessary because
Operations has no merge field. The accepted predecessor's right-fold batch
adapter is not confused with the source's left-fold constructor example.

## Actual provider boundaries

Pinned Batteries has a real binomial implementation, but its forest is sparse
and carries explicit ranks. Its non-strict combine retains the first equal
root, and its deletion stores the selected node/context. These are useful
proof references, not the dense source recurrence. Its HeapNode.WF has the
expected child/sibling recursion, but its edge order is conditional on an
actual TotalBLE instance. Strict greater cannot supply totality on equal
keys.

The inspected rank and size theorems have the claimed forms, including
inner realSize plus one equal to the rank power of two. They do not supply
source permutation, exact maximum occurrence or measured work. The plan
therefore uses BinaryTree directly and does not create an otherwise unused
sparse conversion merely to cite those results.

Actual ExactQueue, OrderDual, multiset, relation/square and list-fusion
providers support the proposed semantic boundaries. Counts preserve repeated
occurrences; finite-set membership would not. Relational preservation does
not require an arbitrary chosen decoder, while this concrete finite carrier
can supply its explicit witness observation. Measured erasure, reachable
workload fusion and potential telescoping remain separate results. The
unguarded potential step identity can be supplied on a valid-state subtype;
the invariant-guarded workload fusion theorem retains its own closure premise.

## Source counts and size conditions

The phase counts are mathematically consistent with the inspected source
branches and remain future measured-definition/proof obligations:

- A proper smash makes one comparison and contains two Node construction
  expressions. A nonempty valid carry through r occupied slots makes r links,
  r+1 carry calls and r+1 list-cons constructions. Insertion adds its singleton
  Node, giving `2*r+1` Node expressions.
- Join consumes paired heads and then one carry suffix. With M the maximum
  input slot length, its bounds of M+2 combined calls, M comparisons and
  M+1 list-cons expressions account for both base cases and any terminal
  carry extension.
- The combined find-max scan makes L+1 calls. Its comparison count is zero
  for no occupied roots and otherwise one less than the occupied count;
  an already initialized find-max-prime compares every occupied root.
- A sibling spine of rank r entails r+1 unzip calls, r constructed closures,
  r detached-root Nodes and r cons expressions. Continuation applications
  and an arbitrary supplied continuation's cost are charged separately.
- Deleting a selected base-zero slot j uses j+1 auxiliary calls, at most
  j+1 comparisons, the reconstructed prefix/hole and the rank-j child unzip.
  Whole deletion additionally pays the full scan and the final join. The
  proposed `3*L` comparison upper bound is conservative; None still pays
  the complete structural scan.

The counters describe syntactic source events, not physical heap allocation,
GC, stack behavior or native time. The plan does not assign a source unary
comparison cost to native Lean Nat or deduce a tariff from a comparison law.
It also does not derive constant-time physical persistence from value equality.

The generalized mass equation includes its factor `2^i`. For public base-zero
forests, mass is less than `2^L`, and therefore its bit length is at most L.
The reverse bound needs canonical final-slot occupancy. Finding
`BINOM-PLAN-001` is resolved by making that base-zero condition explicit for
the canonical equality and logarithm formula.

The all-Leaf family is the decisive boundary: for arbitrary L it is valid
with zero mass but costs L+1 scan calls. Singleton deletion actually returns
a one-Leaf forest, so ordinary reachability does not imply trimming. The plan
requires this counterexample rather than silently normalizing the source.

The proposed exact stored-length laws are consistent with the actual
recurrences. Raw carry/join never shorten the retained forest and can extend
the old maximum by at most one; extension ends in an occupied slot. On valid
base-zero inputs, insertion and merge lengths are the maximum of previous
stored lengths and the bit length of output mass. Successful deletion retains
the original length: its child forest is shorter, and a new occupied slot at
the old length would contradict the smaller output mass. These statements
yield the stated historical-capacity invariant, with an extra initial padding
bound where required and explicit hypotheses on persistent merge operands.

Normalized-input live-size bounds are consequently conditional statements,
not an invariant promised after source deletion. The separate growth/drain
family and historical-size theorem retain the consequence when live mass
returns to zero. Actual Nat.size/log premises and the real-cast Big-O provider
were read directly; neither supplies those missing representation conditions.

## Insertion potential and runtime measurement

The source occupancy bridge matches BinaryCounter.inc, including padded valid
inputs. Link comparisons equal leadingOnes, whereas flipCost also charges
the final write. Combining the actual source count with the provider's
potential law gives one unit of amortized comparison charge. The repeated-run
identity retains initial and final potential. From empty, positive N implies
positive final occupancy, yielding fewer than N comparisons; N=0 is treated
separately. The plan does not let branches from one retained version spend
the same initial potential without accounting for it.

The final measurement exercise remains an executed requirement. It compares
the literal source Binom and source Priqueue programs with identical stored
workloads and an independent complete occurrence oracle. Sorting-based list
removal, leftist queues or Batteries cannot replace either benchmark subject.
Merge, repeated maxima, empty/zero distinctions, growth/drain padding and
bounded persistence observations have explicit roles.

I inspected the actual four core providers for the experiment. Int64 signed
comparisons use the signed bitvector relations and have native overrides;
their decoded order and range-guarded conversion lemmas have the claimed
types. The Nat correspondence is restricted below `2^63`; the 64-bit runtime
carrier is kept distinct from the separate signed 63-bit model. Queue keys
are only compared, while generation, conversions and checksums still need
their own range/overflow accounting.

The seeded generator is explicit, randNat endpoints are inclusive, and the
clock reports monotonic elapsed nanoseconds rather than process CPU time.
The plan requires exact correctness checks, bounded actual runs, preserved
commands/raw results, explicit timing phases and honest failure reporting.
No statistical uniformity, universal speedup, external compiler correctness
or native runtime equivalence is inferred from the mathematical proofs.

## Identity checks and final disposition

All **36 workspace identities and four core-file identities** in the initial
frozen plan match actual bytes. Both external PDF identities were independently
verified as well. The sole corrected bullet does not change these tables,
coverage records or provider claims. Consequential APIs and source bodies were
read directly, including the exact source priority-queue signature, native
heap differences, resource recurrence/potential interfaces and runtime APIs.

`BINOM-PLAN-001` is closed against the final plan identity above. No additional
actionable omission, false provider claim, weakened source obligation,
unjustified generic premise or unsupported completion claim remains.

The plan is clear as preparation. Actual chapter completion still requires
accepted #1014, integrated source coverage and all proofs, the executed
measurement exercise, isolated stable candidate validation and exhaustive
audit, both independent implementation review axes, and immediate final
candidate verification. This report closes no ticket and grants no acceptance.

Only this review file was written for the Binom assignment. No compiler,
proof implementation, algorithm execution, benchmark, cache/configuration/
checkout/tracker/GitHub mutation or chapter acceptance was performed. Root
retains all gate, tracker and durability-checkpoint ownership.

# Independent bounded review — #1013 Trie plan

**Outcome: clear for planning; no actionable findings.**
This is a source/reuse-plan review within the existing whole-book workflow.
It is neither an ordinary chapter implementation review axis nor acceptance
of Trie, a staged module, or the running candidate. All proposed new proofs,
adapters, cost results and executable demonstrations remain implementation
obligations.

## Exact reviewed inputs

- The author announced the final plan frozen before its assessment:
  `../specs/1013-Trie.md`, SHA-256
  `ff3874effda4d56e22a84d16b685e723c72dc210d70a1aec0d38799b7ceaa56e`,
  61,546 bytes, 698 lines. The identity was checked before and after reading.
  No correction to those bytes was requested or made.
- Full VFA 2.1 `Trie.v`: SHA-256
  `a5af2b4db4c2cb639a8deb063e57909e11eb44ee763782ad0af9afbf45a78f3e`,
  26,268 bytes, 712 lines. I read the complete chapter independently,
  including the experimental number representations, incomplete comparison,
  all collision programs, successor prose exercise, trie laws and final
  abstraction example.
- Inventory: `../source/Trie.inventory.json`, SHA-256
  `38117a5d14986171b4c4bf5345dc18a29dd1011d54faa1c79b19f488ff764326`.
  All records and metadata were inspected and mechanically compared with the
  plan in addition to the complete source read.
- Project HEAD at final read-only check:
  `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`, with clean working tree.
  The accepted Redblack predecessor is unavailable; later predecessor reuse
  remains explicitly conditional on its gate and actual public declarations.

Applicable AGENTS, architecture/domain guidance, GLOSSARY, shared language
direction, ADRs 0001/0002/0010, implementation workflow, README build/audit
rules and local user requirements were followed. The positive-key reuse note,
Trie resource obligations, tree-reuse boundaries, applicable computational
assumptions and sharing/space note were read. The complete staged positive-key
module and its independent review, table-observation draft and relevant unary
cost model were inspected. This assessment does not rerun or extend their
reported focused validation.

## Coverage verification

The plan maps all **55 inventory IDs exactly once, in inventory order**, with
no extra record IDs. All **12 exercise names and source ranges**, **11 recorded
command lines** and **four source modules** are covered. The classifications
match: 31 definitions, eight source-proved records, fifteen admissions, and
one grading item. All exercises are standard; none is optional or advanced.

The complete source read confirms the important nonlexical obligations:

- The comparison's catch-all returning lt is deliberately wrong and must be
  replaced. Its lexical definition status is not treated as proof of validity.
- `successor_of_Z_constant_time` is mathematical work, despite the inventory
  containing only its manual-grade constant.
- The admitted `is_trie` definition and the admitted final `Abs_three_ten`
  sanity check are required, not lost outside named exercise boundaries.
- Arithmetic and collision complexity prose is assigned explicit measured
  recurrences, source corrections and qualified asymptotic consequences.
- Constructor, numeral, printing and lookup evaluations retain their exact
  source results. Commands and namespace mechanics receive Lean adaptations.

## Positive arithmetic and actual APIs

The existing PosNum carrier has exactly the required one/bit0/bit1 shape.
Its cast equations differ only in ordinary arithmetic presentation from
source `positive2nat`; the staged numeric adapter supplies the all-input
equations. `PosNum.succ` matches the source's three branches exactly.

All **eighteen carry-addition branches** in the plan were compared with the
source, including both asymmetric terminal cases and every nested successor.
The stated carry theorem has the correct summands and quantifies both carries
and both positive inputs. Existing `PosNum.add` has a different recurrence,
notably successor applied to a recursive sum in the bit1/bit1 case. The plan
correctly requires the source carry recurrence and an actual numeric adapter
before consuming the existing addition theorem or discussing source counts.

Direct inspection confirms that `PosNum.cmp` already completes the intended
source comparison. Both mixed-low-bit cases let a strict high-bit comparison
override the low bit; the recursive eq case selects the appropriate low-bit
ordering. The H/H case is eq, while H/non-H and non-H/H terminate with lt and
gt respectively. `cmp_to_nat` has actual PosNum equality in its eq branch,
and the cast/order/iff providers have the claimed orientations. Numeric order
is not confused with Color's later bit order.

Nat.bits is least-significant-bit first; `bit0_bits` requires the nonzero
child supplied by positivity. The source printer is the reverse order with
Bool-to-digit conversion. The plan retains its source append equations and
does not identify an output-equivalent reverse-based implementation with the
same allocation work. `Nat.size`, its power bounds and logarithm providers
have the stated premises. Positive bit length includes the terminal one.

The shifted key seam is accurate: encode n has numeric value n+1, decode p is
the natural predecessor of its numeric value, and both inverse directions
hold in the staged declarations. PNat's existing equivalence has precisely
this shift. `ofNat 0 = ofNat 1`, clamping by positive predecessor, and numeric
ten versus shifted key nine remain explicit boundary cases. No inverse or
logarithmic conversion cost is inferred from a similarly named theorem.

ZNum supplies the intended zero/positive/negative representation. Its actual
successor, addition and comparison branches, signed cast laws and injection
were read directly. Int is a mathematical observation of the binary carrier.
The planned signed-size measure gives zero size one and counts sign dispatch
separately; positivity is imposed on the reachable counter trajectory, not on
all RatherSlow inputs or arbitrary initial counters.

## Trie semantics, defaults, and abstraction

`BinaryTree.node` takes value before children, while the source constructor
takes left child, value, right child. The plan's adapter preserves both
children. Actual `BinaryTree.get`/`getOrElse` match the source lookup directly:
one selects the current root, bit0 goes left, bit1 goes right, and nil returns
the explicit default. Lookup needs no ordering or payload equality. Source
insertion still needs its six-case implementation, including default-valued
nodes newly created below a Leaf; existing ordered-label `indexOf` is not
substituted for either operation.

The ten path is left/right/left/stop. The full `three_ten` constructor result
matches the source after argument reordering, as do the five queried Boolean
results. The later total-map example correctly writes at Nat 9 then Nat 2,
corresponding to positive keys 10 then 3.

Same-key and distinct-key lookup laws retain every raw tree and the source's
explicit shared default. The other-key law would fail with arbitrary
unrelated insertion/lookup defaults because filler nodes can become visible.
No BST, balance, pruning or payload inequality premise is needed. The proposed
`is_trie := True` therefore supports all source validity and refinement laws
without making them vacuous. Source-facing wrappers retain the displayed
validity premises even when stronger unconditional observations are available.

The abstraction uses lookup at encode n, and lookup refinement uses the
positive round trip. Function.update's query/write orientation and the
injective reindexing theorem were checked. Shadowing, self-update and
commuting writes are observation equalities; empty/default-write trees can
have equal observations and different raw structures. Optional tree lookup
records materialized paths, including filler nodes, not explicit insertion
history. The plan makes no unjustified partial-map, injective-decoder or
surjective-total-map claim.

The small proposed word adapter also fits the actual WordCoalgebra API.
Arbitrary output observations, Bool recognition, finite reachable subtrees,
and the distinct depth-indexed snapshot carrier are kept separate. The
absorbing Leaf interpretation can consume suffix bits after actual lookup
would stop, so its semantic equation is not presented as a cost equation.

## Collision correctness and resource scope

All three source loops retain query-before-update behavior, no write on a hit,
their own counter type and the source increment orientation. The independent
specification `length - dedup.length` counts repeated occurrences, not unordered
equal pairs. Its generic equality assumptions and injective list-map transport
match the actual dedup APIs. The source numeral lists are not silently replaced
by successor-shifted labels. Signed negative keys remain valid RatherSlow
inputs. Reachable-prefix invariants establish the seen-key observation without
asserting finite support for arbitrary Boolean functions.

The proposed cost claims are mathematically consistent with the inspected
recurrences and are explicitly future proof obligations:

- Terminal-inclusive successor visits are at most positive bit length.
  Carry-addition charges both its recursive calls and the terminal successor
  on the remaining strict child; the proposed maximum-input-bit-length bound
  accounts for both. Comparator visits are exactly the smaller bit length,
  so comparison against H is not incorrectly described as linear in the
  other input's length.
- BinaryCounter's actual Bool-list model charges two writes at positive H:
  `[true]` becomes `[false,true]`. The plan uses that charge, one at O, and
  one plus the recursive charge at I, and requires a measured bridge.
  Initial/final potential remains in the general identity. For n sequential
  increments from H, initial potential is one and the final positive state
  has at least one one-bit, giving the stated `2*n` upper bound. N states
  and N transitions are distinguished, as are amortized and random-input
  claims. RatherSlow's zero-start bridge is a separate obligation.
- VerySlow uses an explicit update history: creating a closure/history cell
  does not scan previous bindings, whereas lookup can traverse them. The
  source equality model is not confused with the staged less-or-equal model.
  Counter work for source `c+1` is charged separately.
- Sequence length, distinct input keys, magnitude and signed/positive bit
  length are independent parameters. The balanced-tree bound retains binary
  comparator work, balancing and counter work; a merely per-increment log
  bound would need its extra n-log-n term. FastEnough lookup/insert counts
  follow the key length, with constructor events distinguished from runtime
  allocation.
- The distinct family n through 2*n-1 justifies the proposed unary-chain
  lower-bound route. A single long positive key justifies the separate
  warning that distinct-write count alone does not bound trie paths. Array
  initialization endpoints, small-size logarithms and key-conversion cost
  are preserved. No upper bound is relabelled a tight bound without its
  own family, and no observation equality certifies native timing or GC.

## Identity checks, findings, and disposition

All **34 file hashes** in the frozen plan's identity table match the actual
files. Consequential providers were read directly, including Num/PNat,
bits/size/log, tree storage/get, update/reindexing, dedup, staged key/table
adapters, WordCoalgebra/Machines, Squares/ListFusion and measured
workload/potential/BinaryCounter/Growth declarations. Their explicit premises
and universe boundaries agree with the plan's proposed use.

| ID | Status | Finding |
| --- | --- | --- |
| — | None | No actionable omission, false provider claim, weakened source contract, unjustified added premise or unsupported completion claim found. |

The plan is clear as preparation. It still awaits accepted #1012, actual
chapter integration, meaningful checked applications, the isolated stable
candidate build and exhaustive audit, both independent implementation review
axes and final candidate verification. This review grants no acceptance and
changes no ticket.

Only this review file was written in this assignment. No compiler, proof,
algorithm, benchmark, cache/configuration/checkout/tracker/GitHub change or
chapter acceptance was performed. Root retains the running gate and checkpoint
ownership; the author's plan remains frozen at the identity above.

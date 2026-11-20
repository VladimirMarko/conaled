# VFA Redblack: source correspondence

## Scope and current boundary

This is the source-specific colored search-tree development for VFA 2.1
Redblack. The current increment implements the pure operations, their ordering
and map laws, the parent-color invariant, and the maximum/minimum-depth
theorems. Development checks and actual module exports support those pure
results; the frozen checkpoint records its separate validation and review gates.
The chapter is not yet source-qualified.
Its structural work model and an executed comparison with the ordinary-tree
driver remain required after the pure theory is accepted. VFA therefore
remains at 11 of 17 source-qualified units.

The canonical requirements are
[`1012-Redblack.md`](../history/textbooks/checkpoint-012/books/vfa/records/research/specifications/1012-Redblack.md).
They cover every source record, exercise, command and substantive claim;
the older planning-only label records that document's creation before Extract
was accepted, rather than a current prohibition on this development.
Extract's checked direct and standalone execution paths were accepted in
checkpoint 039. Redblack reuses their mathematical and execution interfaces.

The primary source is the complete 838-line, 27,066-byte `Redblack.v` from
[VFA 2.1](https://softwarefoundations.cis.upenn.edu/vfa-2.1/Redblack.html),
SHA-256 `f44255ba3d0235f6efa401b72f2fcf9a9551a7ebc065912202d6f33494891ce2`.
Its release archive has SHA-256
`f03296c763d78aa5bc18a545d848d398292575e5c8af4b5aa94dc25709e169b8`.
The mathematical and program descriptions are adapted from Software
Foundations, copyright its contributors, under its MIT license. Downloaded
primary texts are not copied into the contribution.

## Representation and source algorithm

The chapter presents Okasaki's functional red-black insertion algorithm
through the Coq `MSetRBT` development discussed by Appel. Its cited papers and
left-leaning variants explain that lineage; this development implements the
chapter's particular ordered matcher and insertion recurrence.

`Search.RedBlack.Tree κ ν` is the pinned Batteries raw `RBTree.RBNode (κ × ν)`.
It retains arbitrary trees, independent key/payload universes, both colors,
and malformed states. It neither wraps every input in an invariant nor orders
payloads. The source-specific owner is `Applications/Search/RedBlack`;
connected clients belong in `Examples`.

The pinned Batteries revision is
`66e469188fe07963e5cf666c7d4433f45b8131c5`. Its recycling RBTree API is a
bounded dependency for this source correspondence; the provider recommends
Std containers for general applications and marks this API for eventual
deprecation. The development uses its matching carrier, observations and
proved shape facts, with the missing source recurrence supplied explicitly.

| Operation | Exact source behavior |
| --- | --- |
| Empty | Nil, without a default value. |
| Optional lookup | The provider's `find?` with a cut that tests `ltb query key`, then `ltb key query`, and projects the returned payload. |
| Default lookup | Apply the caller's default to the optional result. A stored default remains present. |
| Balance | Red bypass, then black left-left, left-right, right-left, right-right, fallback, in that order. |
| Internal insertion | Recurse by the same two Boolean tests; invoke the full source balance after either recursive branch. Equality replaces both key and payload. |
| Root blackening | Nil stays nil; a node becomes black with unchanged entry and children. |
| Insertion | Unconditionally blacken the result of internal insertion. |
| Accumulator traversal | Traverse the right subtree into the suffix, cons the entry, then traverse the left subtree into that result. |
| All-node predicate | The provider's `All` over the original key/payload pair. |
| Color erasure | Fold to the accepted uncolored tree, retaining every original key and payload. |

The provider's insertion cannot replace the source operation. Its right-side
balancer tries right-right before right-left, its recursive insertion balances
only the changed side, and its public insertion conditionally blackens based
on the old root. The source differs on overlapping raw cases, on a pre-existing
violation opposite the recursive branch, and even on insertion into nil.
The counterexamples use constructor equality or root observations: the
provider's `BEq` compares inorder streams and ignores shape and colors.

Only the left-left rotation equation is unconditional among the four displayed
black rotation patterns. A later equation must exclude earlier matches.
The exact source recurrence also governs the later work instrumentation;
a proof for a side-specific library operation is not a work bound for this one.

## Hypotheses and observable meaning

Executable operations take a Boolean strict comparison. Decoding to `Int` is
a proof parameter. The accepted signed `Int`, `BitVec` and `Int64` comparison
realizations supply reflection; default unsigned word order does not substitute
for signed order. Finite words remain finite carriers.

| Claim family | Required hypotheses |
| --- | --- |
| Raw traversal, all-node predicates, nonemptiness, erasure, shape | No key ordering law or decoder injection. |
| Balance preserves BST | Both child BST proofs and full-descendant strict separators. Balance itself compares no keys. |
| Insertion preserves BST | Strict-comparison reflection and input BST, without an RB premise. |
| Balance lookup and same-key lookup | The stated BST/separator premises and strict-comparison reflection, without decoder injection or RB. |
| Distinct-original-key lookup | BST, reflection, original-key inequality and decoder injection. |
| Binding identification and original-key map models | Injection where required to identify an original key from decoded equality. |
| Strict decoded-key enumeration and original-key nodup | BST; no payload order or RB premise. |
| Balanced height bounds | The shape invariant; no BST premise. |

BST constrains every descendant of both subtrees. Checking only child roots
would be weaker. Color erasure transports this predicate to accepted
`DecodedKeys.BST`; it also transports lookup, arbitrary-suffix traversal,
all-node predicates, height and size. Rotating insertion does not structurally
commute with ordinary insertion. Equal lookup observations are a separate,
weaker statement.

For weak lookup laws, decoded-Int transport avoids introducing an injective
order on the original keys. The completed Models source retains partial-map
meaning, presence, caller defaults, update laws, canonical enumeration and
the direct structural model; final integration and statement validation remain
gates. `model_enum_laws` and `model_structural_laws` instantiate the accepted
`EnumeratedTable.ModelLaws`, and `table_laws` retains BST as its validity
predicate. `strong_elements` supplies the separate ordered-enumeration
contract. `partial_enum_laws` and `partial_structural_laws` instantiate the
existing partial-map laws on `validOps`, the accepted BST subtype adapter.
These packages use the actual source insertion. An unconditional raw
`EnumeratedTable.Laws` package would be too strong for this rotation algorithm.

The enumeration bridges preserve their asymmetric scopes. On a raw tree,
successful optional search gives an original enumerated pair when reflection
and original-key identification hold (`mem_elements_of_lookup?`). Under BST,
membership gives presence and the same payload for every caller default
(`elements_sound`), without decoder injection. `absent_no_entry` therefore
requires BST, while `no_entry_absent` applies to raw trees with the stated
identification assumptions. Independently of those order laws, `bound_value`
produces one value for all defaults: `∃ value, ∀ default`.

`elements_insert` connects actual source insertion to the accepted
replacement-aware `kvsInsert`. `listAbs` reuses head-winning list decoding;
`enumAbs` and `mapOfTree` retain the accepted enumeration and collision-removing
structural abstractions after color erasure. Their update and coherence laws
keep BST and original-key identification explicit. The three canonical-list
theorems `elements_eq_of_enumAbs_eq`, `elements_eq_of_lookup?_eq`, and
`elements_eq_of_mapOfTree_eq` use equal partial bindings. Equality of one
defaulted lookup view is insufficient.

## Parent colors and depth

The source `RB t parent n` indexes the hypothetical parent's color, whereas
the provider's `Balanced t root n` indexes the root's color. The exact bridge is
`RB t red n ↔ Balanced t black n` and
`RB t black n ↔ ∃ root, Balanced t root n`.
Nil has black height zero. Red nodes have black-rooted children of the same
black height; black nodes add one and allow either child root color.

`NearlyRB` is nonempty and permits a red-red violation only at the root.
Its provider presentation is `t ≠ nil ∧ RedRed True t n`; omitting nonemptiness
would admit a source-invalid nil case. Both simultaneous insertion conclusions
must hold for arbitrary Boolean comparisons. A NearlyRB red root can have
two red children, so this predicate does not justify changing rotation priority.

Parent-index weakening changes neither tree nor black height. Root blackening
changes the represented root and may change black height: a red singleton has
black height zero and its blackened form has black height one. Consequently
root blackening and final insertion state the new height existentially.

Height is zero on nil and one plus the maximum child height; minimum depth
uses the minimum instead. Size counts internal nodes. The intended source
bound is `height ≤ 2 * mindepth + 1` for either parent color, obtained from
black height at most minimum depth and height at most twice black height plus
one. The stronger black-root height bound is twice black height.

The separate provider size bound is `height ≤ 2 * (size + 1).log2`, after the
proved parent/root bridge. The `+1` covers nil and singleton, unlike the
unqualified source phrase “2 log N”. These are mathematical shape claims.
The provider's `depthLB` docstring mislabels its direction; its actual
`Balanced.le_size` statement supplies the lower size bound used here.

## All 45 lexical source records

This table retains each source ID exactly once, including repeated names at
abandoned proofs. Declaration names belong to `Search.RedBlack` unless an
example or provider is named. They identify the actual pure implementation;
the table itself is not an acceptance receipt. The checkpoint's frozen-source
statement inventory and validation identify the accepted candidate separately.

| Source record | Current obligation and owner |
| --- | --- |
| `Redblack.key@46` | Accepted signed comparison parameters and realizations; no new integer axioms. |
| `Redblack.color@48` | Existing `RBColor` constructor presentation in Basic. |
| `Redblack.tree@50` | Raw `Tree κ ν` in Basic. |
| `Redblack.empty_tree@57` | Nil-valued `empty` in Basic. |
| `Redblack.lookup@64` | `lookup?`, `lookup` and their nil/node equations; `eraseColors_lookup?` and `eraseColors_lookup`. |
| `Redblack.balance@83` | Exact ordered `balance` matcher and raw overlap cases in RedBlackTrees. |
| `Redblack.ins@103` | Complete source recurrence `ins` with `ins_nil` and `ins_node`. |
| `Redblack.make_black@111` | `makeBlack`, `makeBlack_nil`, `makeBlack_node` use the actual `setBlack` adapter. |
| `Redblack.insert@117` | `insert` and `insert_eq_makeBlack_ins` unconditionally blacken. |
| `Redblack.elements_aux@123` | `elementsAux`, its constructor equations, `elementsAux_eq` and `eraseColors_elementsAux`. |
| `Redblack.elements@130` | `elements`, exact balance inorder preservation and the complete relevant Models bridges. |
| `Redblack.ins_not_E@149` | Abandoned proof of a true claim; map to `ins_ne_nil` and the completed constructor reasoning. |
| `Redblack.ins_not_E@208` | Arbitrary-comparator `ins_ne_nil` and `insert_ne_nil` in Basic. |
| `Redblack.ForallT@237` | `ForallT`, `forallT_nil` and `forallT_node` present the provider's `All`. |
| `Redblack.BST@243` | `BST`, `bst_iff_eraseColors` and `bst_node_iff` retain full-descendant strict ordering. |
| `Redblack.empty_tree_BST@252` | `bst_nil` with an arbitrary payload universe. |
| `Redblack.insert_BST@259` | Abandoned preview mapped to `insert_bst`. |
| `Redblack.balance_BST@269` | Abandoned case-splitting attempt mapped to four-premise `balance_bst`. |
| `Redblack.balance_BST@331` | Abandoned attempt mapped to `balance_bst` and transitive all-subtree bounds. |
| `Redblack.ForallT_imp@368` | `forallT_imp` uses pointwise weakening via provider `All.imp`. |
| `Redblack.ForallT_greater@378` | `forallT_greater` weakens the lower separator by decoded transitivity. |
| `Redblack.ForallT_less@387` | `forallT_less` weakens the upper separator by decoded transitivity. |
| `Redblack.balance_BST@398` | `balance_bst` uses both child BST proofs and both strict bounds. |
| `Redblack.balanceP@428` | `balance_forallT` proves an exact arbitrary-predicate iff, without order assumptions. |
| `Redblack.insP@444` | `ins_forallT` preserves the predicate on old and newly written pairs. |
| `Redblack.ins_BST@458` | `ins_bst` under reflection and input BST. |
| `Redblack.insert_BST@471` | `insert_bst` through `makeBlack_bst`. |
| `Redblack.lookup_empty@490` | `lookup_nil` for every default and query. |
| `Redblack.balance_lookup@501` | `balance_lookup` and its optional form `lookup?_balance`, with weak premises. |
| `Redblack.lookup_ins_eq@528` | `lookup_ins_eq` and `lookup?_ins_eq` under BST and reflection. |
| `Redblack.lookup_ins_neq@541` | `lookup_ins_neq` and `lookup?_ins_neq`, additionally using injection. |
| `Redblack.lookup_insert_eq@556` | `lookup_insert_eq` and `lookup?_insert_eq`. |
| `Redblack.lookup_insert_neq@563` | `lookup_insert_neq` and `lookup?_insert_neq`. |
| `Redblack.RB@642` | `RB`, `RB.nil`, `RB.red`, `RB.black` and exact nil/red/black iff characterizations. |
| `Redblack.RB_blacken_parent@658` | `RB_blacken_parent`, unchanged tree and black height. |
| `Redblack.NearlyRB@669` | `NearlyRB`, its nonemptiness theorem and exact red/black characterizations. |
| `Redblack.prove_RB@692` | Actual private source-case repair proofs and structural insertion induction discharge the tactic admission. |
| `Redblack.ins_RB@694` | `ins_RB` retains both simultaneous conclusions at the same black height. |
| `Redblack.ins_red@725` | `ins_red`, the red-parent projection. |
| `Redblack.RB_blacken_root@738` | `RB_blacken_root`, with existential new black height. |
| `Redblack.insert_RB@751` | `insert_RB` preserves black-root RB existence. |
| `Redblack.height@777` | `height`, its constructor equations and actual provider/erasure bridges. |
| `Redblack.mindepth@780` | `mindepth`, `mindepth_nil` and `mindepth_node`. |
| `Redblack.redblack_balanced@783` | `redblack_balanced` uses the black-height path bounds for arbitrary parent color. |
| `Redblack.manual_grade_for_redblack_bound@790` | Grading data omitted; its definitions and advanced theorem remain required. |

## All exercises and commands

| Exercise | Source range | Required result |
| --- | --- | --- |
| balanceP | 423–437 | Arbitrary all-node predicate preservation. |
| insP | 439–451 | Induction over both branches and equality replacement. |
| ins_BST | 453–464 | BST preservation without an RB premise. |
| insert_BST | 466–476 | Recoloring consequence. |
| balance_lookup | 496–516 | Exact weak-premise lookup equation. |
| lookup_ins_eq | 518–534 | Same-key result under BST. |
| lookup_ins_neq | 536–549 | Distinct-key result with injection. |
| lookup_insert | 554–571 | Both public-insertion equations. |
| RB_blacken_parent | 653–663 | Parent weakening without mutation. |
| ins_RB | 679–721 | Both conclusions and removal of the tactic admission. |
| RB_blacken_root | 731–744 | Existential height and a height-change witness. |
| insert_RB | 746–757 | Compose internal insertion and blackening. |
| redblack_bound | 759–792 | Both depth definitions, auxiliary path bounds and the advanced theorem. |

The five `Check` commands at lines 576, 580, 584, 588 and 592 correspond to
the actual elaborated empty-validity, insertion-validity, empty-lookup,
same-key and distinct-key statements. The extraction command at line 799
requires actual execution of empty, insertion, lookup and enumeration in
both accepted Lean modes. Pure theorem exports do not discharge that command.

The four abandoned proofs are explanatory predecessors of true final
statements. Their incidental Rocq goal counts are not Lean obligations.
Source argument, warning and scope commands become appropriate Lean imports,
namespaces and explicit arguments. The references to alternative left-leaning
algorithms supply context, without replacing this algorithm or requiring a
separate implementation of every cited paper.

## Remaining work model and runtime comparison

These are still open canonical obligations, not consequences of a successful
pure build or a logarithmic height theorem:

| Structural observation | Required bound or exact equation |
| --- | --- |
| Lookup visits and Boolean calls | At most height and twice height. |
| Internal-insertion visits, comparisons, balance calls | At most height, twice height, and height. |
| Local balance pattern attempts | Exactly 1, 2, 3, 4, 5, 5 in source priority order. |
| Sequential datatype observations | At most 17 per balance call in the specified observation model. |
| Syntactic node constructions | Three per rotation, one per bypass/fallback; insertion at most `3*height+2`, including final blackening. |
| Enumeration invocations and cons operations | Exactly `2*size+1` calls and `size` cons operations, without traversing the supplied suffix. |
| Weighted work | Explicit primitive costs and affine-in-height bounds, then the qualified logarithmic family. |

Every instrumented result must erase to the actual source operation on raw
inputs. Syntactic constructor counts do not assert physical allocation or
sharing. Nested accumulator traversal does not assert constant stack space.
Unbounded integer comparisons retain their cost parameter; finite signed
carriers retain their capacity restriction in any asymptotic interpretation.

Canonical section 8 also controls the exact branch recurrences. Nil contributes
zero old-node visits and comparisons. A left descent makes one comparison;
a right descent or equality branch makes two. Nil and equality make no balance
call. Either recursive insertion branch adds one full balance call, including
a red-root bypass. Internal insertion has at most `3*height+1` syntactic node
constructions. Final blackening adds one root inspection and, because internal
insertion is nonempty, one node construction, giving `3*height+2`.

Weighted work must retain declared terminal costs and nonnegative primitive
prices before deriving an affine height bound and the formal
`1 + (N + 1).log2` family. Costs along histories use each actual current size;
repeated writes can replace a payload without increasing the distinct size.
Uniform comparison prices are model assumptions. A bit-cost interpretation
must keep its key-length parameter, and finite carriers require an appropriate
capacity or growing-width family.

The runtime extension must reuse the accepted Extract driver, with both
source-shaped RNG-in-query timing and a controlled comparison on identical
retained insertion/query lists. It must independently check optional answers,
presence, enumeration, distinct size, height and reported hit counts. Build,
validation and setup remain outside the stated query-only region.
Direct and standalone executions need actual retained identities, commands,
results and clocks; an elapsed observation is not a CPU-time measurement.

The source's construction precedes its clock, despite an inaccurate printed
insertion-and-lookup label. Random queries draw fresh keys, so their hit count
need not equal their count; repeated writes can reduce the distinct size.
Consecutive insertion makes the ordinary source tree a right chain. The
comparison must connect to the checked height distinction without turning
that theorem into a timing ratio. Positive benchmark keys also do not test
signed order: retain Extract's negative and finite-extreme correctness cases.

Each run must retain its execution mode, seed and generator, carrier and range
checks, conversions, warmup and repetition settings, available host information,
clock and unit, checked outputs, exit status and raw logs. The source's reports
of similar random performance, faster consecutive balanced performance, and
similar balanced random/consecutive times are historical observations. They
are not observations of these Lean programs.

The named random 1,000,000, random 20,000 and consecutive 20,000 recipes remain
source configurations unless actually executed. Bounded completed comparisons
must report their actual sizes. The current SESSION contract prohibits
agent-selected CPU, memory, thread, affinity and build-time caps; that standing
instruction overrides the older planning note's suggestion of such limits.
Published historical OCaml timing ratios are not Lean observations or universal
performance theorems.

## Validation boundary

Current development probes record exact source bytes, independent public
cases, commands, exits and outputs outside the contribution. Missing imports
are prerequisite failures, not missing mathematical theorems. Final acceptance
requires the frozen actual module imports, the guarded focused build and full
audit body, statement review, independent Standards and Spec reviews, exact
archive reconstruction and durable publication. Whole-library build, exhaustive
audit and receiving acceptance remain delegated and are not asserted here.

## Checkpoint 041: measured work and comparative execution

This section extends the retained checkpoint040 account above. The mathematical
work and runtime components listed there as remaining are now implemented by
the owners below. The checkpoint's final validation and independent review
records determine qualification; an implementation or a local probe alone does
not determine it. The complete 45-record, 13-exercise and six-command ledger
above remains the source inventory, with the following additional discharge
of its resource, extraction and performance obligations.

| Owner | Role |
| --- | --- |
| `Applications/Resources/RedBlackBalance.lean` | Eleven independent natural observations, measured recognition/construction, exact priority branches, raw erasure and constant local bounds. |
| `Applications/Resources/RedBlack.lean` | Actual measured lookup, internal insertion, blackening, public insertion and accumulator traversal; raw erasure and bounds. |
| `Applications/Resources/RedBlackWorkload.lean` | Natural primitive prices, affine and logarithmic bounds, explicit operation families, actual prefix histories, query sums and complete map-meaning connections. |
| `Examples/RedBlackBalanceWork.lean` | Isolated rotations, both-side/overlap priority, attained observation bound and output/allocation distinction. |
| `Examples/RedBlackWork.lean` | Comparison orientations and costs, default presence, raw suffix traversal, replacement, rotation, signed endpoints and independent payload universes. |
| `Examples/RedBlackWorkloads.lean` | Actual weighted histories, source workloads and growing integer families. |
| `scripts/ExtractSearchTree.lean` and `scripts/test-extract-searchtree.py` | One shared ordinary/red-black workload pipeline, actual executions and independent complete-output/invariant checks. |

### What each observation counts

`Resources.RedBlack.Cost` is the ordinary pointwise natural-valued function on
the finite `Metric` enumeration. Existing `Resources.Measured`, `bind`, `pure`,
`reweight` and `run` supply composition. Keys and payloads retain independent
universes. There is no replacement execution framework or invariant-wrapped
input carrier.

| Symbol | Source observation |
| --- | --- |
| L | Visited nonempty nodes on the original lookup/insertion descent. |
| Q | Actual Boolean-comparison invocations, regardless of their internal cost. |
| M | The natural work returned by those measured comparator invocations. |
| B | Calls to the complete source balancer. |
| P | Fresh complete-pattern attempts, including the initial root-color selection. |
| D | Actually performed tree-constructor/color observations in those attempts. |
| A | Syntactic tree-node constructions, including final root rebuilding. |
| T | Terminal-nil lookup/insertion calls. |
| R | Final root inspections by `makeBlackRun`. |
| E | Accumulator enumeration invocations, including nil. |
| C | List-cons constructions in enumeration. |

Every successful red-node recognizer returns the actual subtrees and binding
that its continuation consumes. A fresh pattern attempt stops at its first
failed constructor/color observation; later attempts do not inherit a free
cache of earlier failures. Rotation uses three actual measured node
constructions. These definitions do not attach guessed counters to a result
computed by an unmeasured balancer.

The six exact balance branches retain source priority. Red bypass has
`B1,P1,D1,A1`. The four black rotations have `P2,P3,P4,P5`, respectively,
and `A3`; black fallback has `P5,A1`. The datatype count is one plus the sum
of the actually attempted recognizer counts, each at most four. Thus
`1 <= P <= 5`, `D <= 1+4*(P-1) <= 17`, and `A = 1 or A = 3` on every raw
input. Later branch theorems include all earlier failure guards. The concrete
isolated LL/LR/RL/RR cases have D equal to 5, 8, 7 and 10; a separate fallback
attains 17. Overlap examples demonstrate that removing the guards would give
the wrong branch charge.

Measured operations bind their actual results. At a lookup node the first
true comparison descends left after one invocation; otherwise the reverse
comparison decides right descent or stored-payload return after two.
Insertion has exactly that original-input L/Q/M/T descent. Both recursive
branches balance the actual recursively returned tree. Nil and equality
construct one node without balancing; equality replaces the whole pair.
`insRun` is unconditionally nonempty, so public insertion adds exactly R1+A1,
even when the returned root was already black. Raw value-erasure theorems use
only the returned Boolean comparison; no ordering or shape premise is hidden
inside them.

The established ordinary measured-search and accumulator-traversal interfaces
are reused through exact projections. This gives, for every raw input tree:

| Operation | Proved bound or equality |
| --- | --- |
| Lookup | `L <= height`, `Q <= 2*L`, `T <= 1`; T is exactly the absence indicator. |
| Lookup/comparator | `M <= 2*K*height` when both orientations against actual input keys cost at most K. Unit-comparator work is exactly Q. |
| Internal insertion | `B <= L <= height`, `P <= 5*B`, `D <= 17*B`, `A <= 3*B+1`. |
| Public insertion | `R = 1`, `A = ins.A+1 <= 3*height+2`; the descent coordinates are unchanged. |
| Enumeration | `E = 2*size+1`, `C = size`, and all other coordinates are zero. The whole cost vector is independent of the supplied suffix. |

Accumulator evaluation follows right recursion, construction of the cons,
then left recursion on the actual returned suffix. A suffix may be nonempty,
unordered or contain duplicates; it is neither traversed nor copied by this
source recurrence. Source node/cons counts are not allocation bytes, native
instruction counts, a constant-stack claim, a sharing theorem or net growth.

### Prices, logarithms and families

For declared natural prices w, `weighted w cost` sums the eleven priced
coordinates, and `weightedHom` is an additive homomorphism. Q prices call
overhead and M prices the comparator's reported internal work. P and D offer
different observation granularities; pricing both is an explicit choice,
without an automatic identification with machine instructions.

Lookup has affine coefficients

```text
a = wL + 2*wQ + 2*K*wM,       b = wT.
```

Public insertion has

```text
a = wL + 2*wQ + 2*K*wM + wB + 5*wP + 17*wD + 3*wA,
b = 2*wA + wT + wR.
```

The actual weighted operations are bounded by `a*height+b`. A separately
supplied RB shape certificate gives
`2*a*(N+1).log2+b <= (2*a+b)*(1+(N+1).log2)`, where N is the actual tree
size. Nil and singleton are covered. Weighted enumeration is exactly
`wE*(2*N+1)+wC*N` on arbitrary raw trees and suffixes.

The lookup and insertion family theorems quantify over actual Nat-indexed
trees, inputs and measured comparators, with uniform primitive prices and a
finite-input comparator bound. They apply the accepted
`Resources.isBigO_of_nat_bound` to real casts of the actual natural costs and
the declared `1+(N(i)+1).log2` majorant. No premise identifies the family
index with distinct size. Separate varying-comparator theorems preserve
`(1+K(i))*(1+(N(i)+1).log2)` rather than discarding K(i). The connected
integer families use real prefix builds and prove their shape certificates.
A unit source comparator models invocation work; it does not prove native
constant time for arbitrary-size integers. A fixed signed width bounds the
number of representable distinct keys, so an unbounded size interpretation
requires a justified representation family.

### Histories and workload meaning

`buildRun` uses the existing measured `run`. Its actual return erases to
the existing `OrderedMap.bindAll`; standard `List.scanl` exposes all prefix
trees, with its ith state proved equal to the first i writes. The cost sum
zips each write with its actual preceding state, and its logarithmic bound
uses that state's size and that write/state's comparator bound. BST and
existential black-root RB preservation are separate theorems: the former
requires reflected comparison, and the latter works for arbitrary returned
Boolean comparisons.

For the accepted chronological writes
`[(3,303),(1,101),(3,333),(-2,202)]`, prefix sizes are `[0,1,2,2,3]` and
per-write node constructions are `[2,3,2,6]`. The whole vector has
`L4,Q5,M5,B3,P8,D15,A13,R4,T3,E0,C0` with unit comparison work. The final
balanced height is 2 and ordinary height is 3, with the same three complete
bindings. The third write replaces a payload without increasing size.

`buildRun_meaning` instantiates the accepted enumeration model laws on a valid
initial tree. `buildRun_meaning_agrees` and `buildRun_lookup_agrees` connect the
two actual measured realizations after arbitrary shared histories, including
all optional payloads. They require the reflected injective key model where
original-key meaning needs it; no RB assumption is added to these semantic
laws. Query cost is the sum of the actual lookups on the returned build tree,
independently of the changing hit accumulator. Its weighted logarithmic sum
retains query-specific comparator bounds and counts duplicate queries.

`sourceRun` uses `sourceWrites`, feeds its measured build result into query
execution, and retains the exact build/query cost split under repricing.
`sourceRun_independent_count` proves equality with the accepted
`expectedHits`, which inspects membership in the original insertion list.
The `sourceIndices` connection uses the proved descending-schedule to
consecutive-list equality. Empty, replacement, all-hit, missing, signed and
higher-payload-universe cases exercise the same public interfaces.

### Extraction and comparative observations

[The runtime correspondence](vfa-redblack-runtime.md) records the actual
driver, complete observation format, compiler/dependency identity, independent
checker, direct and standalone executions, generated-code inspection and raw
times. The existing driver selects an actual `OrderedMap.Ops` realization:
ordinary by default or the proved `Search.RedBlack.ops`. Its common workload
pipeline, signed adapters, checked conversions, independent Int-key finite
map and optional-result validation are reused.

The controlled comparison uses byte-identical retained insertion/query files
for each pair. A bounded consecutive 128-key case produces ordinary height128
and red-black height8, with 131 queries and 129 hits in both. Source-shaped
random and consecutive comparisons retain fresh generation inside the query
interval, with construction before the clock. Tree size/height, full ancestor
BST checks, root color, red-red exclusion, equal black height and the
logarithmic height inequality are observed after timing. The Python observer
independently reconstructs these observations from a flat preorder with nil
leaves, using an explicit stack rather than replaying insertion.

The six-command ledger is thereby connected to actual exported pure
statements and to both actual Lean launch modes. The line799 extraction
requirement is an execution/correspondence obligation, not a demand to reproduce
the Rocq extraction implementation. Historical schema1 observations retain
their format and historical candidate identity; current tree observations use
schema2. Large named source configurations remain documented recipes unless
an execution receipt says otherwise. The comparison does not promote a
height difference or one set of elapsed times into a universal speed ratio.

All final source declarations, private helpers and connected cases require
actual type/body assessment, focused kernel audit and the existing independent
Standards/Spec review. Whole-library build, exhaustive whole-library audit and
receiving acceptance remain delegated. The verified checkpoint is the durable
record of these gates and of whether CTB14 is source-qualified; Trie is the
next canonical unit after those Redblack gates pass.

# Complete bounded parser workloads

Issue [#304](https://github.com/VladimirMarko/conaled/issues/304) composes
[retained snapshots](retained-parser-snapshots.md) with
[transport normalization](derivative-transport-normalization.md). The result
supports conditional adoption: retaining a depth-two snapshot and normalizing
its transport spine pays for the repeated workload below. Eager retention loses
on a single query. Normalizing a parser with no outer transports adds work.

The [implementation](../../Applications/Languages/ParserWorkload.lean) separates
two contracts. `session_exact` proves exact native `Decision (P word)` agreement
for every native binary-alphabet parser. Complete cost accounting applies only
to the explicit `Spine` fragment. It does not extend that cost claim to native
concatenation, star, arbitrary functions, or arbitrary witness types.

## Frozen workload and observations

The cost fragment has a base parser `scale (yes xs) universal`, where `xs` is a
finite Boolean list, surrounded by finitely many transports. Its language is
`fun _ => List Bool × PUnit`. The explicit map syntax contains identity,
pointwise Boolean complement, ordered composition, and derivative prefix shift.
These are finite inspectable closures, not arbitrary functions with guessed
costs. `Map.iso` interprets every map as a native witness isomorphism;
`Map.run_result` proves exact application of that isomorphism.

All policies receive the same parser instance, depth bound and requests. A
request is a visible depth and Boolean word. Both its depth and word length must
fit, including when a larger requested view contains a short word. Invalid
requests return `none`; they do not invoke a fallback parser. Valid requests
return the exact selected decision. There is no recognition-based cache key,
state merging, or interning.

The four policies are ordinary parsing, retention alone, normalization alone,
and their combination. Normalization runs once at session creation, before
any derivatives or snapshot construction. It uses the existing outer-spine
packing order, retaining its final identity and composition closures. Retention
builds both branches of the existing depth-indexed binary snapshot once and
shares that instance for the whole request batch. Direct policies derive afresh
for each admitted request. Native direct clients and resource interfaces remain
unchanged.

The frozen comparisons use depth two. The repeated workload contains twenty
copies of `(2,[true,true])`. The short workload contains only `(1,[true])`.
The transported source has eight pointwise-complement transports and witness
`[true,false]`; the already-simple source has that witness and no transports.
The witness-heavy source has eight transports and one hundred true elements.
Each list is finite; no global finite-state claim is involved.

## Execution events and tariffs

Counters are projections of events emitted by the functions that compute the
results. `deriveRun`, `nullableRun`, `packRun`, `buildRun`, `directQuery` and
`retainedQuery` return their computed value and trace. They do not obtain a
reference output and attach an unrelated cost. Their erasure proofs connect
those values to native derivation, nullable evaluation, normalization and
snapshot construction. `setup_query_result` connects the composed execution to
`session`; `execute_exact` connects the entire observation transcript to native
parsing. `parse_category_cons` reuses `Resources.reweight` and `Resources.bind`
for exact sequential category composition. `execute_count_repeated` separates
setup from the repeated per-request count for every category.

The abstract machine charges one work unit per recorded operation or allocated
slot. This is an explicit tariff, not a fitted timing model. Natural numbers,
bound comparisons, Boolean operations and pointer reads are unit primitives.
List traversal is charged per cell. The categories are:

| Category | Charged execution |
|---|---|
| derivative | Each parser constructor visited, including scale and universal at the base |
| nullable | Each constructor visited at the final decision; no implicit free nullable calls |
| normalization | Each spine/base visit and the final output wrapper |
| map | Every explicit map node invoked; complement additionally visits every witness element |
| closure | Each constructed identity, composition or prefix-shift environment |
| snapshot | Each stored decision/tree node constructed |
| validation | Word-length traversal and two bound-comparison tariffs per request |
| traversal | Each stored snapshot edge followed |
| allocation | Every allocated slot described below |

Validation reserves both comparison tariffs even if an implementation can
short-circuit the second test. Thus this component is a fixed admission tariff,
not a claim about compiler evaluation order. Refused requests still pay
validation and one result-wrapper slot. Primitive function invocation and its
environment allocation are charged separately. The original complement maps
remain inside the normalized composition, so their application is never free.

## Representation and lifetimes

Storage means slots in the declared immutable arena representation. It does
not mean bytes, Lean heap cells, interpreter stack space, or minimum reachable
storage under garbage collection. The slot layout is:

| Record | Slots |
|---|---:|
| universal token; identity/primitive-map code; decision wrapper; result option | 1 |
| scale or transport parser record | 2 |
| scalar Boolean-list cons | 2 |
| list terminator | 1, shared with the source |
| payload product, whose unit component is erased | 1 |
| composition map, with code and two map references | 3 |
| prefix-shift map, with code, symbol and map reference | 3 |
| snapshot leaf / internal node | 2 / 4 |

Parser tags are packed with their references in this abstract representation;
map code fields occupy their own slot. These are declared layouts, not inferred
Lean layouts. A base derivative allocates a scale and universal record (three
slots), sharing the original scalar decision. A transport derivative allocates
a two-slot parser record and three-slot shift environment. Normalization shares
the base and original maps, allocating one identity, one composition per outer
transport, and one output wrapper. Complement allocates two slots per copied
list cell and one payload product. Shift application allocates a two-slot word
prefix cons before applying the child map. Nullable evaluation allocates its
product and decision wrappers; transporting it allocates the mapped decision.

The caller-owned source graph stays live throughout the session. `Spine.slots`
includes its parser records, map environments, scalar decision, list cells and
terminator. Its construction precedes the comparison and is common to all four
policies. Input request storage is borrowed. Input length traversal and newly
materialized shift prefixes are charged, but construction of the caller's
request list is outside the session.

All normalization and snapshot-build allocations enter one setup arena. This
arena retains *every* intermediate derivative, closure and witness until the
batch ends, even when it becomes unreachable. There is no unproved inference
about which closures a collector would release. Each direct or retained query
uses a separate arena, released after synchronous consumption of its answer.
The consumer may inspect the answer while that arena and setup arena are live;
it must copy any data it wants to retain. Consumer copying is outside this
contract. The returned Lean list of answers is a logical transcript of these
observations, not the machine's owned output buffer.

`Run.cumulative` sums new allocation across setup and all query arenas.
`Run.peak` adds the original source, setup allocation and largest query arena.
This is exact peak arena occupancy for the declared lifetime policy, including
unreachable allocations. It is not a lower bound on a better allocator. The
setup arena and original source are released after the last answer is consumed.
The host's evaluation stack, trace lists and accounting arithmetic are
instrumentation/control machinery outside represented heap storage. Constructor
visits and primitive tariffs account for their abstract execution work; there
is no theorem about their concrete Lean stack or allocation cost.

## Checked comparisons

Each entry is `(total work, cumulative new slots, peak slots)` under the tariffs
above. All setup costs are included. The corresponding equalities and strict
comparisons are kernel-checked in
[Examples/ParserWorkload.lean](../../Examples/ParserWorkload.lean).

| Workload | Ordinary | Retained | Normalized | Combined |
|---|---|---|---|---|
| Eight maps, twenty requests | (5180,3380,202) | (1361,808,822) | (2326,1307,124) | (868,436,450) |
| Eight maps, one short request | (173,110,143) | (1226,789,822) | (144,81,114) | (733,417,450) |
| No maps, twenty requests | (380,180,18) | (225,72,62) | (846,483,36) | (324,132,122) |
| Hundred-element witness, twenty requests | (52220,34740,1966) | (17825,11784,11994) | (49366,32667,1888) | (17332,11412,11622) |

The combined policy wins total work on the repeated transported workload, but
its peak exceeds the normalized direct policy. It loses to ordinary parsing on
the short workload. On the already-simple state, retention alone beats the
combined policy: the uniform normal form adds an identity wrapper.

Map-application counts on the heavy workload are respectively 16480, 5736,
16380 and 5729. Fewer parser wrappers do not eliminate witness work. Even the
combined policy retains 11412 newly allocated slots in total under the
conservative arena scheme. Closure-construction counts on the small repeated
workload are 320, 48, 49 and 15; normalization setup is included. Repeated
combined lookups perform no derivative, nullable or map evaluation after setup.
The connected `execute_count_repeated` application proves that its map work is
241 for any number of repetitions, including zero because setup is eager.

Semantic examples also run nullable star through the actual combined policy,
retain its chosen empty-star witness, cover nonempty words and both depth
rejection modes, and keep Boolean-equivalent parsers with different selected
witnesses distinct. These examples establish the broader semantic contract;
they do not extend the measured fragment to nullable-star costs.

## Caller decision and remaining boundary

Use combined retention for this fragment when the expected request batch is
known and its complete tariff comparison justifies setup and the peak arena
budget. Prefer retention alone for the already-simple repeated state. Reject
eager retention for the tested single-query workload. Use normalized direct
parsing when the retained peak is unaffordable even though the combined policy
has lower modeled work. The table supports these decisions only for its stated
workloads and tariffs. Different tariffs can be applied to the exposed category
counts without changing the semantic proof.

The caller chooses the parser instance, depth, lifetime and synchronous output
consumer. Native parsing imposes none of the retained-depth or lifetime
obligations. A future #263 adapter must preserve parser-instance identity,
indexed exact decisions, visible-depth validity, the snapshot build/lookup
contract and these ownership/cost observations. No accepted generic shared
interface was available at the starting revision; this remains a bounded client,
not a second memoization framework. #235 owns broader preservation-interface
adoption. Arbitrary witness closures, richer parser constructors, consumer
retention, alternative arena reclamation and concrete Lean performance need
separate cost/refinement evidence.

## Validation

The focused build is `direnv exec . lake build Examples.ParserWorkload`.
Executable checks run with
`direnv exec . lake env lean --run scripts/ParserWorkloadTest.lean` and exercise
all four policies, every table entry, explicit map/closure costs, selected
witness parity, rejected views, eager empty-batch setup and parser-free retained
queries. The integrated candidate still requires README's build and exhaustive
proof audit and independent Standards/Spec review.

# C03-080 actual halving policy — author source assessment

## Candidate and evidence boundary

Candidate **e40d1f7fa71e51946b29bf1415067240e7cc369a**, tree
**dee64caf8a031169777f42eb51ee8014dbb82fe8**, adds exactly
`Applications/Resources/HalvingSelection.lean`,
`Applications/Resources/MedianPolicy.lean`, and `Examples/MedianPolicy.lean`.
Their bytes are unchanged from the three drafts captured in checkpoint0130.
The worktree is `conaled-ch02-quicksort`, branch `work/fdsa-ch03-values`.

This is an **uncompiled source candidate**. The author ran no Lean, Lake,
dependency, cache, environment or acceptance command. Complete author source
readback is `100591`; root independently read the three drafts at `780ff9`.
The post-release preservation readback is `c07e9f`; the exact source commit and
successful staged whitespace check are `390772`. Static inspection and the
prepared explicit-argument program do not establish elaboration, actual emitted
types, a kernel audit, independent review or Chapter3 acceptance.

The C080 stage starts from d0479dd03371f1c1f0b41dff5f1882a36206f40a,
the actual focused-passing minimum-policy candidate. Parent
0f66bcf85ead843e1d6cf69c17f8e23fa6b84292 is only the authorized dependency
receiving commit. The full Chapter3 review base remains
2da5708478a1d943a9214b5b386ec2db16cd9eca. All 83 canonical requirements
remain in the existing implementation/review loop; this assessment addresses
C03-080 only. Root separately owns C03-055. No whole-chapter closure is claimed.

## Requirement and exact dependency provenance

The frozen `research/chapter03-obligations.md`, SHA256
eda51a6cd8bac41df1f97ab03386b003e1cae5ed0db5320414265027074360ed,
requires positive valid selection states, strict sides at most half, an actual
linear pivot constructor, an edge bound by the ceiling logarithm, scan volume
at most twice the initial size, and a linear lower and upper source tariff.
It explicitly requires the size-one distinction between one active invocation
and zero recursive edges. The pinned book text, printed p35, was read at
`d900ee`; it makes the linear-time conclusion conditional on finding the pivot
in linear time. Its following p36 convention selects the lower occurrence
median. The pre-source expectations and independent numeric calculations were
saved in `halving-policy-starting-state.json` before these three sources existed.

Root authorized exact minimal source copies from two immutable candidates:

- be8a5ab11040d61f5f2f8aef7abf02da333049fc supplies the absent resource
  modules Chunks, SelectionAuxiliary, SelectionMedians, Selection,
  RoundedRecurrence, RoundedRecurrenceBounds, SelectionRecurrence and
  SelectionBounds. Its actual book-bound pair passed, owned93118 CLOSED0,
  terminal10c0b5, complete closure14bebf. Full outer log6930 bytes has SHA256
  ae9c6fc34f00d5f3e5fb252e3af9e2adf1d2406a248c665cc9debe68f734f468.
- 45d120ce0f5bacbaac76cbceeca13ee3ff494dff supplies only the needed exact
  `Applications/Resources/HalvingTrace.lean`. Its core and examples passed,
  owned53358 CLOSED0, terminale8d513, complete closure21d240. Full outer
  log1510 bytes has SHA256
  1d4b574bd4bcc680ba7bc7b4377a320e206299657b480edcede531d422662767.

The nine source sizes, SHA256 values, Git blobs and origins are recorded in
`halving-policy-dependency-receipt.json` (6987 bytes, SHA256
ae01bee0f4cf7c7938398a761fdf2696f1d9571fb5c79f1bdebb0a54b80b0449).
All existing reachable sources already agreed with those donor files. No
existing source was replaced, no unrelated donor changes or example modules
were merged, and no output/cache file was copied. Those nine files are received
dependencies with their original attribution and review scope, not new
authorship counted among this stage's 60 names. Focused donor evidence remains
focused donor evidence.

## Architecture and actual resource meaning

The new generic module proves properties of the already checked
`Resources.SelectionPolicy.runWith`. It introduces only `HalvingPolicy`, a
predicate on an actual measured callback. It does not define a second selector
or a size sequence chosen to satisfy the conclusion. The actual returned trace
records input sizes observed by measured length traversals. The generic proof
follows the same lower, equal and upper branches as the source executor.

`PivotValid` is explicit: on each nonempty input the callback returns an input
occurrence. It is the existing value/termination interface and the exact
membership premise requested for this bridge. `HalvingPolicy` additionally
bounds both strict buckets of every successful callback result. It does not
assume distinct elements. Neither predicate assumes the desired trace or its
cost. The concrete measured lower median proves both predicates. The generic
interface is explicitly an input-occurrence policy interface; no claim is made
that it characterizes every mathematical pivot value between occurrences.

For current size n, strict-lower length l, equal length e and actual pivot
charge P, the outer executor's charge before recursion/lookup is

    c = (n+1) + P + (n+1) + (l+1) + (e+1) + 1
      = 2*n + P + l + e + 5.

These terms respectively pay for the actual input length, actual pivot
construction, one-pass partition, both actual bucket lengths, and outer entry.
Both bucket lengths are charged even on the lower branch, as specified by the
existing executor. An equal branch additionally pays `min (k-l) e + 1` for the
existing sequential lookup. A valid equal-branch rank makes this lookup charge
at most n. The tariff is therefore not the distinct branch tariff of the
median-of-medians worker or the probability executor. It is also not a count of
comparisons, random bits, machine instructions, allocation or wall-clock time.
Primitive comparisons/arithmetic and trace bookkeeping have the previously
declared zero source-call charge. Fuel is an administrative depth parameter;
its computation is not a new claimed runtime operation.

If the actual callback satisfies P <= A*n+B on every nonempty intermediate
input, partition length conservation gives c <= (A+3)*n+B+5. The terminal
lookup adds at most n. Following the actual recursive call therefore yields

    W <= T <= (A+4)*W + (B+5)*entries.

The lower inequality uses the actual charged input-size traversals, so it is
not inferred from the upper bound. This trace tariff does not require halving.
For a halving policy, the actual positive trace additionally gives

    n <= W <= 2*n,
    entries <= W,
    edges = entries-1 <= floor(log2 n) <= ceil(log2 n),
    n <= T <= (2*(A+4)+2*(B+5))*n.

This supplies explicit two-sided linear inequalities in the stated tariff.
No floor/ceiling rounding is omitted and no exact logarithmic depth is claimed:
the equal branch can stop early.

## Concrete measured median construction and quantifiers

`Resources.MedianPolicy.pivotRun` executes measured `lengthRun xs`, uses its
actual result to compute the zero-based lower-occurrence index `(n-1)/2`,
executes the existing measured `Selection.selectRun` at that index, then
charges one wrapper entry. Consequently its exact charge is

    P(xs) = n + 2 + selectRun((n-1)/2, xs).cost.

The outer selector, this pivot constructor and the nested selector each pay
their own actual length observations. No unstated sharing removes any of them.
The callback value is the canonical ordered-list index at `(n-1)/2`; the
duplicate-aware `RankedAt.count_bounds` implies `2*l <= n` and `2*r <= n`.
The actual selector's already proved uniform cost theorem supplies a constant
Cs before the payload type, order instance, list and rank. For n>0,
`P <= (Cs+3)*n`. The generic tariff then supplies a total coefficient that may
be chosen as `2*Cs+24`. The public theorem retains an existential positive Nat
coefficient; it does not hide an input-dependent coefficient.

The generic policy and concrete median statements use a universe-polymorphic
payload with `LinearOrder`, and no `Inhabited`, `Nodup`, positivity of elements,
bounded-element universe or pre-sorted input assumption. All ranks are the
existing zero-based book ranks. The public one-based selector is untouched.

Value correctness and `some`/`none` equivalences require only adequate fuel
`xs.length <= fuel`; invalid rank is allowed and corresponds exactly to
`xs.length <= k`. Complexity/positive-trace results additionally require
`k < xs.length`, which entails a nonempty input. The empty-input extension has
no active trace and one outer entry; it does not satisfy a false positive-size
complexity premise. Size one uses fuel+1 and rank zero, proving the actual
single entry and zero edges. Equal blocks may contain any number of repeated
occurrences and retain positional lookup rather than returning for free.

The two uniform theorems quantify their Nat constant before the arbitrary
payload type/order, input and (for the outer execution) fuel and rank. Unused
section variables may be omitted by Lean; `halving-policy-statements-inventory.json`
records raw lexical contexts honestly, while `HalvingPolicyStatements.lean`
requests actual complete explicit-argument types for all 60 names. Those types
have not yet been emitted and remain part of the final statement check.

## Exhaustive generic declaration assessment — 8 public names

All names in this table are in `Resources.HalvingSelection`. Raw complete
headers and their hashes are in the inventory; this table assesses each one.

| Name | Intended claim, assumptions and connected use |
|---|---|
| `HalvingPolicy` | Predicate on the actual measured callback; for each successful result both strict bucket sizes satisfy `2*size <= current length`. No trace/cost assumption. Constructed by `MedianPolicy.pivot_halving`. |
| `runWith_trace` | For an input-occurrence, halving callback, valid rank and fuel at least input length, the actual returned trace inhabits `Halves`. Follows actual branch rank transport and strict child size. Used by concrete `run_trace` and every subsequent generic bound. |
| `runWith_scan_bounds` | Actual scan sum lies between initial n and 2*n under the same domain. Consumes the constructed trace, not an assumed sequence; used by concrete and infinite-family bounds. |
| `runWith_edges_log` | Actual number of recursive edges is at most floor-log base2. Subtraction by1 is justified by positive trace. Used by the size-eight case through the concrete specialization. |
| `runWith_edges_clog` | Requested weaker ceiling-log bound follows for the actual edges. Used for every valid rank of the growing range family. |
| `runWith_singleton_trace` | Any valid halving policy on `[x]`, rank0 and positive fuel returns trace `[1]`. It does not claim zero active invocations. Used by concrete singleton trace and entry/edge case. |
| `runWith_tariff` | Valid input-occurrence callback and fixed A,B with actual cost bound on every nonempty list imply W<=T<=(A+4)W+(B+5)entries. Does not need halving. Charges terminal sequential lookup and every pivot construction; used by the final cost theorem. |
| `runWith_linear_cost` | Combines actual trace and actual tariff to obtain n<=T<=fixed_coefficient*n. It explicitly requires both valid/halving policy and callback cost, valid rank and adequate fuel. The concrete instance discharges every policy and cost premise. |

## Exhaustive concrete declaration assessment — 21 public names

All names in this table are in `Resources.MedianPolicy`.

| Name | Intended claim, assumptions and connected use |
|---|---|
| `pivotRun` | Actual length observation, actual measured selector at the observed lower-median rank, then one wrapper entry. No external pivot or arbitrary preselected value. Used by all execution and balance claims. |
| `pivotRun_value` | Exact optional canonical lower-occurrence index for every list, including empty input. Erases actual measured primitives via public value laws. Supports rank/failure equivalences. |
| `pivotRun_cost` | Exact n+2 plus actual nested selector charge. Includes the index-length observation; used in the uniform callback proof. |
| `pivotRun_some_iff` | Successful callback value iff duplicate-aware `RankedAt` at `(n-1)/2`. No distinctness or nonempty premise is concealed. Supplies actual membership and strict-count bounds. |
| `pivotRun_none` | Callback fails exactly on the empty list. Natural subtraction at zero and the valid nonempty median index are handled; supports `pivot_valid`. |
| `pivot_valid` | Constructs the existing occurrence-policy contract from actual callback success and ranked membership, rather than assuming it. Used by generic value and trace results. |
| `pivot_halving` | Constructs both strict-side inequalities from the actual callback's rank/count correspondence; repetitions are allowed. Used in every concrete scan/depth/cost theorem and duplicate case. |
| `pivotRun_small` | For a nonempty list of length<=20, expose the same execution through the checked selector's public small-input equation. Value is slowSelect's actual value; charge is 2*n+4 plus its actual charge. No alternate algorithm is substituted in the definition. Used by seven explicit pivot computations. |
| `pivotRun_singleton` | For every payload x, actual callback yields some x and charge10. Derives through the public small-input bridge. Used by exact singleton outer execution. |
| `pivotRun_exists_uniform_linear_bound` | A single Nat constant is chosen before payload type/order/list; on positive lengths it bounds actual callback cost. Discharges the generic callback tariff for every intermediate state. |
| `run` | Existing measured policy executor instantiated with `pivotRun`; preserves its fuel, optional values, trace and tariff. No second recursive selector is introduced. |
| `run_value` | For all ranks and lists at adequate fuel, actual optional result equals canonical ordered index. Used by `run_some_iff` and `run_none`. |
| `run_some_iff` | Actual successful selection iff the established duplicate-aware rank relation, under adequate fuel. A direct transport of `run_value` and existing rank equivalence; the same value contract underlies the concrete successful executions. |
| `run_none` | Actual result is none exactly when length<=rank, under adequate fuel. Consumed by the invalid-rank example. |
| `run_trace` | Concrete actual valid execution has `Halves` trace; actual policy validity and halving are supplied. Consumed at size8 and on duplicates. |
| `run_scan_bounds` | Concrete n<=W<=2n under valid rank/adequate fuel; consumed at size7 and for every rank in the growing range family. |
| `run_edges_log` | Concrete actual edges<=floor-log2 n; consumed at size8. It does not count the terminal entry as an edge. |
| `run_edges_clog` | Concrete requested ceiling-log edge bound; consumed on the infinite range family. |
| `run_singleton_trace` | Actual singleton trace `[1]` for any payload and positive fuel; consumed by the Int singleton and active/edge distinction. |
| `run_singleton` | Actual singleton result `(some x,[1])` costs19, including callback cost10, partition, observed lengths, entry and lookup. Consumed directly and as the base of the longer exact paths. |
| `run_exists_uniform_linear_bound` | Positive Nat D chosen before arbitrary payload/order, fuel, rank and input; every valid adequate execution has n<=T<=D*n. This is a concrete discharged instance, not a theorem with an assumed pivot-cost oracle. Consumed by the uniform integer application. |

## Independent worked calculations and exhaustive cases — 31 public names

These expectations were saved before source writing. For an already sorted
nonempty list of size n and median index j, insertion sort costs2*n+1 and
sequential lookup costs j+1. The checked small branch therefore makes the
new actual pivot cost `4*n+j+6`. The outer local formula above then predicts
each continuing charge; the terminal lookup is added separately. The proofs
connect these expected results through public `pivotRun_small`,
`SelectionPolicy.runWith_step`, `run_singleton` and public general bounds.
Finite reduction is restricted to concrete measured insertion/lookup values
after the public bridge, rather than asking reduction to unfold the private
proof-carrying well-founded selector.

All names in the following table are in `Examples.MedianPolicy`.

| Name | Independent expectation and connection |
|---|---|
| `pivot_two` | `[6,7]` has lower median6, j0 and actual pivot charge14; consumes `pivotRun_small`. |
| `pivot_four` | `[4,5,6,7]` has lower median5, j1 and pivot charge23; consumes the same bridge. |
| `pivot_eight` | `range8` has lower median3, j3 and pivot charge41; consumes the same bridge. |
| `pivot_three` | `[4,5,6]` has median5, j1 and pivot charge19; consumes the same bridge. |
| `pivot_seven` | `range7` has median3, j3 and pivot charge37; consumes the same bridge. |
| `pivot_four_initial` | `range4` has lower median1 and pivot charge23; preserves the lower occurrence convention on even size. |
| `pivot_duplicates` | `[4,4,4,4]` has median4 and actual pivot charge23, including selecting occurrence index1. No Nodup premise. |
| `two_execution` | Largest rank1 on `[6,7]`, fuel+2: trace[2,1], result7 and charge24+19=43. Public outer step plus actual singleton. |
| `four_tail_execution` | Largest rank3 on `[4,5,6,7]`, fuel+3: trace[4,2,1], result7 and charge38+43=81. Public step plus two-element execution. |
| `eight_execution` | Largest rank7 on range8: pivots3,5,6,7; trace[8,4,2,1], result7; charge66+38+24+19=147. Public step plus established tail. |
| `eight_trace_connected` | The actual size-eight execution satisfies the generic Halves relation via `run_trace`, independently of simply reducing a chosen list of sizes. |
| `eight_scan` | Scan8+4+2+1=15 follows from the exact actual execution. |
| `eight_edges` | Four active entries give exactly three recursive edges. |
| `eight_edges_bound` | The actual three edges satisfy floor-log2(8); consumes the universal depth theorem. |
| `three_tail_execution` | Largest rank2 on `[4,5,6]`: trace[3,1], result6 and charge32+19=51. Public step plus singleton. |
| `seven_execution` | Largest rank6 on range7: trace[7,3,1], result6, charge60+32+19=111. Public step plus odd tail. |
| `seven_scan_bounds` | The actual odd-size trace satisfies7<=W<=14 via the universal scan theorem. |
| `seven_edges_strict_clog` | This path has two edges, strictly below ceiling-log2(7)=3; the upper bound is not asserted to be exact. |
| `early_equal_execution` | Rank1 on range4 equals the first lower median; trace[4], result1 and calls38+1=39. Public actual step terminates immediately. |
| `early_equal_edges` | That early equal stop has zero edges despite input size4. |
| `lower_branch_execution` | Rank0 on range4 takes the actual lower bucket `[0]`; trace[4,1], result0, charge38+19=57. Exercises a branch unavailable to a minimum-pivot policy. |
| `duplicate_execution` | Rank3 on four repeated4s terminates with trace[4], result4 and calls40+4=44; positional equal-block lookup costs4. |
| `duplicate_trace_connected` | The actual duplicate execution satisfies the generic trace theorem without a distinctness assumption. |
| `singleton_execution` | Int payload-4, rank0: actual result, trace[1] and charge19 via the generic payload singleton theorem. |
| `singleton_trace_connected` | The Int singleton consumes `run_singleton_trace` rather than only finite reduction. |
| `singleton_active_and_edges` | Explicitly one active invocation and zero recursive edges from that actual trace. |
| `empty_execution` | Positive administrative fuel still produces none, empty trace and one outer entry on the empty input. No pivot is executed there. |
| `invalid_value` | Rank4 on length4 returns none via the public `run_none` equivalence. No valid-path cost bound is applied to this case. |
| `range_scan_bound` | Every n and k<n+1 give n+1<=W<=2*(n+1) on actual range(n+1), an infinite growing family and all valid ranks. |
| `range_edge_bound` | The same infinite family consumes the universal ceiling-log edge theorem with its rank and adequate-fuel premises established. |
| `all_integer_inputs_linear` | One positive coefficient precedes every integer list and valid rank, including unsorted inputs and duplicates. Uses the full concrete uniform theorem at fuel=length. |

No case expectation was weakened to obtain compilation success: no compilation
has yet run. The seven finite pivot computations and the exact outer paths are
not substitutes for the general trace, tariff, quantifier or uniform-cost
proofs. Conversely, the uniform theorems are not used to fabricate exact
finite charges. Existing checked rank, count, partition and measured-resource
interfaces connect these two kinds of evidence.

## Inventory, preservation, findings and next gates

There are exactly60 new public lexical declarations: three definitions and
57 theorems, split8/21/31 across the generic/core/example modules. There are
zero new named private declarations or new structures/inductive types. Full
generated proof auxiliaries and transitive dependencies remain in the later
exhaustive audit scope. The prior authored inventory402 public and7 named
private helpers is preserved, making462 authored public names across21 files;
the nine separately attributed received dependency modules are excluded from
that authorship total. These are source inventory counts, not checked kernel
declaration counts or whole-book totals.

All prior18 authored sources and all nine received dependencies are
byte-identical to their recorded origins. The branch's original failure and
correction histories, statement inputs, provenance and checkpoint records are
unchanged. No root entrypoint, shared reconstruction map, canonical control,
ticket, independent review record or other agent source was edited. No new
statement-review mathematical finding was identified in this static author
assessment. Actual elaboration may identify proof/API/linter corrections;
record those under this same candidate/finding loop without altering the
mathematical statements, definitions or independent case expectations merely
to obtain a pass.

The inventory stores every raw public header, namespace/universe/variable
context, whole-source identity, definition body identity and imports. The
prepared input has exactly60 unchanged full names, each in explicit
`#check @name` form, with supported pinned printing options including
`pp.deepTerms`, `pp.proofs` and `pp.maxSteps`; it has no unsupported
`pp.maxDepth`. Its candidate comment identifies this new candidate honestly.

Root's next focused targets are exactly:

- `Applications.Resources.HalvingSelection`
- `Applications.Resources.MedianPolicy`
- `Examples.MedianPolicy`

Root remains the sole serial qualified compiler owner. Focus success, if
obtained, is development evidence only. Actual complete type capture, whole
Chapter3 integration/import coverage, full immutable-candidate check and
exhaustive audit, both independent Standards and Spec axes, matching terminal
records, immediate `--verify-candidate HEAD` and approved local integration
remain mandatory. The normal/fresh distinction follows the actual repository
README; this source-only stage adds no independent fresh-check trigger.

For the receiving integration, root should import these three new modules in
the normal root/coverage process and retain the nine dependencies under their
original owners' exact inventories. This is a reported integration requirement,
not an edit to a shared map or permission to drop their original examples.
There were no GitHub mutations, pushes, compiler actions or cache copies.

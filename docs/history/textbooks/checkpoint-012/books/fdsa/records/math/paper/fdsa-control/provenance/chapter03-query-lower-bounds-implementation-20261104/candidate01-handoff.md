# Coordinate sensitivity and adaptive-query candidate 01

**HELD for root-owned serial compilation.** Candidate
`6c66b545f7f7e2e15a274a67a867d8ddc7f980c3`, tree
`3eb772753cd1188982c588c1ca96f64f34d41260`, is the single child of accepted
Chapter 2 `2da5708478a1d943a9214b5b386ec2db16cd9eca` on
`work/fdsa-ch03-query-lower-bounds`. The allocated `conaled-ordinary-merge`
worktree is clean. Its old `work/fdsa-ordinary-merge` branch remains at
`72a0951aee406f7db67998d2a3bf8810f4e1bccc`.

The actual staged whitespace check and local commit both exited zero; the
commit command's actual tool chunk is `905888`. No Lean/Lake, toolchain,
dependency, cache, runtime, output-capture or process-polling command was run
by this author. All statements and examples below are **uncompiled proposed
source**, with zero actual elaborated-type, audit, review or acceptance credit.

## Exact scope and requested checks

Only four new source paths were committed:

| Module | Public names | Private helpers |
| --- | ---: | ---: |
| `Applications.Selection.CoordinateSensitivity` | 7 | 2 |
| `Applications.Selection.CoordinateQueries` | 24 | 0 |
| `Examples.CoordinateSensitivity` | 13 | 0 |
| `Examples.CoordinateQueries` | 24 | 0 |

There are **68 authored public names and two private proof helpers**, with no
anonymous declarations. The public count includes the inductive predicate
`Runs` and both explicitly authored constructors, `Runs.done` and `Runs.query`.
Compiler-generated declarations remain subject to the whole-project audit;
this inventory does not assert that they are absent.

Compile the sensitivity core and examples first, then the query core and
examples. `Statements68-candidate01.lean` imports the two example modules and
contains exactly one explicit-`@` check for each public name. The bound
preparation manifest lists every source file, name, header and program identity.
It uses the supported detailed printer options with `pp.maxSteps 1000000`.
The actual output still requires inspection for omissions and diagnostics.

## Intended mathematics and statement assessment

**C03-052:** the main source theorem quantifies over every integer list with no
duplicates and every valid zero-based rank and coordinate. It constructs a
replacement rather than assuming sensitivity or a suitable witness. A fresh
value above or below all entries changes the count strictly above the original
selected value. The standard `List.countP_set` law and accepted
`ranked_strict_counts` make preservation of that value contradictory. Freshness
also proves the updated list remains distinct for that internal argument.
The externally requested existential sensitivity theorem is a direct
corollary. No extra hypothesis on the replacement is imposed on callers.

Valid-index injectivity is restricted to `Fin xs.length`; invalid indices all
returning `none` are explicitly excluded. Value-only adapters connect the book's
zero-based observation to `sortSelect (k+1)` and any valid pivot selector.
`ofFn_update` proves the standard finite-function/list update correspondence;
`exists_update_changes` consumes it for the protocol input representation.

**C03-081:** the protocol operation receives only a history of previous valid
coordinate requests and returned values. It returns either a result or a next
coordinate. `Runs` gets each recorded answer only from that requested input
coordinate. Completed traces are chronological, while the operation's history
is newest first. No hidden input parameter, answer oracle, input-dependent
advice, or uncharged full-list argument is available to the operation.

`Total` explicitly requires a finite execution for every input. `Selects`
requires each finite execution to satisfy the existing `RankedAt` contract for
every integer input, including inputs with duplicates. These are separate laws;
the theory does not claim every arbitrary protocol terminates or is correct.
Replay and determinism are proved from the actual inductive execution. The
lower-bound results always start with empty history, so the generalized replay
lemma for a fixed initial history cannot introduce advice into those results.

**C03-082:** if a coordinate were absent from a correct terminating trace on a
distinct input, the proved sensitivity theorem supplies a changed input. Replay
preserves the entire trace and returned value, while correctness on both inputs
would identify two different selected values. Thus every coordinate occurs.

**C03-083, partial source preparation:** coverage implies trace length at least
n through `List.finRange` and the standard nodup subset-length theorem. Every
query occurrence is counted, including repeated indices. An actual trace tariff
charging at least one unit per query yields the same lower bound on its sum.
Transfer to another resource observation has an explicit `coversQueries`
contract and does not pretend that an arbitrary source-call count already
satisfies it.

For each valid size and rank, all-input total correctness supplies an actual
execution on the distinct increasing integer input, with at least n queries.
For a protocol family, every uniform worst-case query bound is consequently
at least n at positive sizes. The standard `Resources.isBigO_of_nat_bound`
bridge states the usual Ω(n) consequence as the identity size function being O
of that bound. No finite supremum over all integer inputs is assumed.

The actual median-of-medians algorithm's coordinate-read observation and
declared source-tariff bridge are **still outstanding**. Neither a correctness
equality nor the generic `coversQueries` hypothesis discharges that obligation.
There is no physical-runtime, free-bulk-primitive, or randomized-algorithm
lower-bound claim. This candidate does not close C03-083 or Chapter 3.

## Connected cases retained in source

The sensitivity consumers apply the public theorem to all three positions of
`[8,1,5]`, its middle rank, singleton input, the one-based sort selector and the
last-pivot selector. Independently calculated concrete replacements cover a
coordinate above, below and equal to the selected value. The finite-function
update example and the increasing-input family consume their public adapters.
The invalid-index example demonstrates why injection is bounded to valid ranks.

Three actual protocol operations demonstrate satisfiable totality and correctness:
the one-coordinate ask/return operation, an adaptive operation that repeats a
query only for a negative answer, and the two-coordinate minimum operation.
Their complete finite runs and correctness are connected through determinism
and `RankedAt`. Negative repetition produces two charged queries and work six
at tariff three; a nonnegative input produces one query and work three. The
pair example consumes the public coverage, query-count and resource-contract
theorems. Additional consumers retain replay and the uniform asymptotic bound.

## Integration and next gates

The shared entrypoint and reconstruction documentation remain untouched.
Eventual root integration should import `Examples.CoordinateSensitivity` and
`Examples.CoordinateQueries` and map the precise remaining upper-bridge gap.
The parent worktree retains the qualified compiler exclusively. First actual
checks may expose elaboration issues in dependent `Runs` induction cases,
finite-index/list update coercions, or simplification of the small protocols;
any such diagnostics must be preserved and corrected without changing the
mathematical requirements or validation profile.

The existing original-scope review loop, full Chapter 3 candidate validation
and exhaustive audit, both independent axes, immediate candidate verification,
and acceptance checkpoint remain mandatory. These source and preparation
records are held after the saved readback until the coordinator releases them.

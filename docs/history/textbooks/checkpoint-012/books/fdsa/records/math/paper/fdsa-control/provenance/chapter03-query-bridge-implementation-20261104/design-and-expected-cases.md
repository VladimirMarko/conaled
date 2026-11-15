# Read-plan frontend: bounded design and independently expected cases

This author continues the existing FDSA implementation/review loop. The fixed
slice base is 591ecdd855bc2fab3f788e6b134cc18aa80a3b6a; the full query branch base
remains 2da5708478a1d943a9214b5b386ec2db16cd9eca. Root alone owns compilation.
No Lean or Lake command has been run by this author.

## Operation and proof target

Use the existing CoordinateQueries.Protocol and Runs. The only arguments to
readPlan are a fixed finite list of valid indices, a pure computation on a list
of observed values, and the supplied history. At history length j, request the
plan's jth index if present. Otherwise return the pure computation on the
newest-first history reversed and projected to its answers. In particular, the
operation has no hidden-input argument or input-dependent oracle/advice.

A private induction on the remaining plan starts from the reverse chronological
transcript of an arbitrary already-read prefix. It constructs a Runs derivation
for exactly the remaining indices and the computation on all prefix+remaining
answers. No length bounds or distinctness premise is needed. The public empty-
history run is the prefix=[] specialization. Determinism gives the same exact
trace/output for every terminating empty-history run. Totality is constructive.

The full-read plan is List.finRange n. Its chronological trace is List.ofFn of
(index,input index) pairs; the output is compute (List.ofFn input). It has n
queries and queryWork under constant c is c*n, including c=0 and n=0. A generic
correctness transfer concerns the chosen pure computation only; it does not
close the missing actual median-of-medians source-cost bridge in C03-083.

## Cases chosen before implementation

* Empty Fin 0 input: zero queries, empty observation, result compute [], zero
  tariff. No inhabitant of the payload type is required.
* Arbitrary n/input/compute: all coordinates in order, actual total run, output
  compute (List.ofFn input), exact length n and constant tariff c*n.
* Coordinates [8,3,5]: full read has trace [(0,8),(1,3),(2,5)], sum output 16.
  This distinguishes input-coordinate order and summation from returned traces.
* Duplicate coordinates [4,4,4]: still three reads and sum 12. Equal values do
  not justify dropping a charged coordinate query.
* Plan [0,1,0]: for arbitrary two-coordinate input, the resulting list is
  [input 0,input 1,input 0]. The trace has three entries and charges 3*c even
  though it has only two distinct coordinate indices.
* Supplied exhausted history [(0,99),(1,7)] for plan [0,1] returns [7,99]. This
  is an operational equation on an arbitrary history, NOT an assertion that
  the history is reachable from [] under this plan or any asserted input.

All cases must consume the public run/uniqueness/cost interfaces. Actual kernel
checking, full audit, detailed printed types and both independent review axes
remain root-owned gates; source inspection alone gives no passing credit.

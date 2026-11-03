# Measured random-access lookup and ordered updates

Issue #181 reconstructs all 47 declarations of checkpoint 233's
`RandomAccessLookupCosts`, plus `perfectTree` and `perfectTree_valid` from
`TreeFlatteningCosts`. The [ledger](adwh-random-access-costs-ledger.json) records
all 49 selected declarations and the 124 explicitly deferred declarations in
the inspected neighboring modules. Historical archive bytes are unchanged.

## Implementation and shared contracts

`Applications/Resources/RandomAccess/Lookup` instruments the accepted #171
list, cached-tree and digit algorithms. It proves raw algorithm erasure and
independent List indexing/update refinement under the original `Perfect` and
`Valid` premises. Cached sizes are selected directly. Neither lookup nor update
flattens a tree or computes its structural size while executing.

`Bulk` executes ordered updates with `Resources.run`. `bulkStep` adds one loop
visit to the actual update count; `bulkRun_cons` proves the exact source
recurrence `nextCost + restCost + 1`. Regrouping the extra unit into the step is
valid for these natural counts. It is not a statement about event order in a
noncommutative trace. Shared `run_state`, `run_invariant` and `run_value_fusion`
provide the value, validity and ordinary List.set fold contracts. No second
generic executor, square structure or validity predicate is introduced.

`Families` supplies concrete worst-case and counterexample representations.
The zero-index cost and unbounded-cost claims specialize the arbitrary-index
results, avoiding the source's repeated proof arguments. Both public source
contracts remain available. The two helper declarations build cached perfect
trees using the accepted smart constructor and perfection predicate; importing
the rest of the flattening-cost framework is unnecessary.

Standard Nat.log2 laws establish the numerical logarithmic bounds.
`LogarithmicScales` is not an actual local proof dependency. No custom logarithm,
square-root, asymptotic class or general potential is needed for these results.

`Observation` uses the accepted valid `Carrier` and existing square composition.
The first consumer performs measured update followed by measured lookup, retaining
and adding both actual counts. Its value is `(xs.set k x)[query]?`; its bound is
`4*log2(length xs)+6`, since update preserves represented length. The second
consumer composes the measured bulk square with sequence observation, retaining
the update count. The observation's traversal is not counted as an update and no
flattening-time result is claimed. Its value is the ordered List.set fold.

`bulkRun_append` is shared measured bind composition. `bulkRun_reweight` applies
an additive tariff to every actual step, following the same updated states. The
checked double-tariff example obtains cost44 from the exact cost22 family. Value
erasure and resource bounds are separate theorems throughout. All operations and
consumer types retain universe-generic elements; existing square carriers stay
within their same-universe interface.

## Statement review and EDD

The initial obligations were to connect instrumented source branches to accepted
random-access semantics, bulk recursion to shared measured execution, and concrete
counterexamples to the quantified claims. Public refinement, exact-count,
composition and family theorems discharge those obligations in
`Examples/RandomAccessCosts.lean`. Computed branch checks complement those uses.

- List/tree/digit runners return actual source values, including Option failure
  and the existing out-of-range update totalization. Raw erasure has no validity
  premise; ordinary List meaning does. A cached node of size zero with two leaves
  returns the second leaf at index zero, demonstrating why these domains differ.
- One branch visit is one composite unit, covering comparison, subtraction,
  cached-size access and one path-constructor rebuild. Empty list/digit lookup
  costs one. Successful ordinary-list index k costs k+1. A perfect rank-p tree
  costs p+1 for every index, including failed lookup. A four-element tree checks
  both left and right routes. Update cost equals lookup cost on raw inputs.
- `Valid r` ensures perfection at each rank and excludes trailing zero digits.
  The digit bound is `r+2*digitLength+1`. Lower and upper represented-length
  inequalities give exact digit length `log2 N+1` for nonempty rank-zero valid
  inputs. The general upper bound also covers empty inputs with Nat.log2 zero.
  Four raw zero digits violate the numerical logarithmic bound, showing the
  validity premise has content. No stronger cached or balanced predicate is
  substituted for the accepted one.
- Lookup and update have count at most `2*log2 N+3` for represented length N,
  including out-of-range requests. The last successful index costs exactly
  `r+2*digitLength`. Concrete failed update/query examples check both unchanged
  ordinary values and nonzero traversal counts. The composed failed query on
  four elements costs eight; same-index and other-index value cases are retained.
- Bulk update uses the actual previous result for every next update. The source
  updates `[(1,7),(2,3),(3,4),(2,8)]` on `[0,1,2,3]` produce `[0,7,8,4]` through
  the independent fold specification. The final write at index2 is retained.
  Empty and appended workloads exercise public execution laws. No intermediate
  state trace is claimed as bulkRun output.
- Bulk bounds are `m*(r+2*digitLength+2)` and `m*(2*log2 N+4)` at rank zero.
  Repeated last-index updates on any nonempty valid input cost exactly
  `m*(2*log2 N+3)`. The nonempty premise belongs to this exact worst-case formula,
  not to the general upper bound. Two updates on a four-element input cost14;
  an empty update list checks the zero multiplier.
- A sparse representation with p zero digits and a perfect rank-p tree has
  successful lookup cost `2*p+2`. At p=4 the cost is10, including index zero and
  a nonzero index. Two index-zero updates cost22, including loop visits. The
  generic `no_index_only_bound` quantifies every fixed index and proposed bound,
  and `no_eventual_index_function_bound` allows any bound function and threshold.
  These statements vary represented length and preserve successful return of
  the selected value. They do not contradict the bound in N.
- Worst-case logarithmic cost is not a pointwise logarithmic lower bound.
  A rank-zero leading leaf allows index-zero bulk updates at exactly three units
  each, even with an arbitrarily large valid suffix. Both validity and exact
  constant cost are checked. The quantified counterexample retains
  `C*cost < log2 N` with cost3; no claim of uniform Theta(log N) for every input
  or request is made.
- The first composed consumer adds actual update and subsequent lookup costs,
  rather than querying the original representation. The second preserves the
  resource field through decoding. Tariff reweighting changes counts without
  changing actual states. The cost bounds require validity through the carrier;
  the public raw branch equalities retain their broader domains.

These are exact finite modeled counts. They establish no machine-integer bit
complexity, cache-validation cost, allocation, sharing, compiled runtime,
hardware timing or Haskell lazy behavior. Independent review, full fresh build
and exhaustive transitive proof audit remain integration gates.

Targeted validation passed with 776 build jobs: `Examples.RandomAccessCosts`,
`Examples.RandomAccessLists`, `Examples.Resources`, and
`Examples.PotentialAccounting`. Only module-system import warnings remain.

## Provenance and remaining scope

The archive SHA-256 is
`8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63`.
Before implementation, actual ZIP member bytes were compared with the inspected
extraction; archive and member hashes were rechecked during ledger generation.
All selected source names and destination names were validated with a parser
that preserves identifier punctuation, including ? and !.

| Member under project/adwh-lean/ADWH/ | Selected / total | SHA-256 |
| --- | ---: | --- |
| Chapter03/RandomAccessLookupCosts.lean | 47 / 47 | `c1df20833c4dd42ce1ae64a584a4b63596b29e3202e24fd14c10104d5e3e0568` |
| Chapter03/TreeFlatteningCosts.lean | 2 / 24 | `1d3b29808ce0d6e2c6b2f48d91cddccd0ec307fda47d53b8144282277e512641` |
| Chapter03/RandomAccessEndCosts.lean | 0 / 80 | `26bdb3a5f21959ffa672adf502b020d20f05d1a9449a2904ca26b710e016fb7c` |
| Chapter02/LogarithmicScales.lean | 0 / 22 | `e816b3cefe8e48732a786f7210de682143a9d246e3b75019e6520b01ef264090` |

All 80 end-operation declarations remain deferred to their separately scoped
client. That includes cache-size work comparison, carry and borrow costs, binary
decrement, push/drain bounds, error wrappers, printed intermediate-state examples,
and the mixed push/pop impossibility result. Their later implementation must use
accepted `RandomAccess.erase` into `Bracketing.Tree` and existing structural-size
semantics rather than introducing the source's duplicate UncachedTree.

The later push and pop bounds use different potentials. Successful draining
starts from an existing valid representation and retains initial zero-digit
potential; an empty failed removal is charged and stops. Exact return cycles
show why separate amortized bounds cannot be combined: repeated push/pop on p
full digits returns to the same state at cost `n*(2*p+2)`. The source quantifies
an arbitrary state potential in `no_uniform_mixed_charge`, so this is a required
negative result, not an optional qualification.

The other 22 TreeFlatteningCosts declarations and all 22 LogarithmicScales
declarations remain preserved reference under #149. No flattening Theta bound,
square-root scale, interpolation or asymptotic-growth framework is claimed by
this issue. The ledger names every deferred declaration individually.

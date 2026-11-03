# Measured random-access end operations

Issue #182 reconstructs all 80 named declarations of checkpoint 233's
`project/adwh-lean/ADWH/Chapter03/RandomAccessEndCosts.lean`. The
[declaration ledger](adwh-random-access-end-costs-ledger.json) records exact
source names, line numbers, destinations and dispositions. The preserved ZIP
has SHA256 `8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63`;
the selected member has SHA256
`26bdb3a5f21959ffa672adf502b020d20f05d1a9449a2904ca26b710e016fb7c`.
Both hashes and equality with the inspected extraction were checked. No archive
bytes changed. No other historical module becomes whole-module scope.

## Shared implementations

`RandomAccess/CacheCosts` evaluates structural size on accepted
`Bracketing.Tree`, using `RandomAccess.erase`. The existing cached-size erasure
law replaces the source duplicate. `Cached` suffices for equal answers; an
unbalanced three-leaf example establishes that perfection is unnecessary.
Structural evaluation counts every tree constructor. Cached evaluation reads
one installed size, even when that size is wrong.

`RandomAccess/End` instruments the accepted carry and borrow branches. Each
visited digit costs one composite unit, including bounded smart-node creation
or splitting. Execution neither flattens a tree nor recomputes cached sizes.
`bits` maps the actual digits into the shared binary-counter representation;
`consTRun_count_bits` connects branch visits to the accepted counter write
count. Their meanings differ, but their natural-number totals agree.
The shared counter potential and bounds then prove the carry accounting laws.
`BinaryCounter/Decrement` owns the total optional decrement and its canonical
nonzero predecessor theorem; borrowing uses this shared operation.

`pushManyRun` uses `Resources.run`, `run_state` and `run_potential_exact`.
`toRARun` runs reversed input, and `toRARun_cons` proves the exact source
foldr recurrence, including accumulated work. These preserve the different
orders: pushing `[8,9]` onto `[1]` produces `[9,8,1]`, while construction preserves
the input list order. `Drain` retains bounded partial recursion because a failed
removal stops execution and is charged. `Cycles` uses `Measured.bind` for the
actual push/pop pair and retains the source's bounded partial mixed execution.
Neither is a second generic workload framework.

`EndObservation` uses the accepted valid carrier, shared measured values and
square composition. Construction feeds its actual state to bounded draining;
only then are removed and residual lists decoded. Push feeds its actual state
to pop. `popMeasured_execution` connects the invariant-bearing pop result and
its cost to `unconsRARun`, including failure. Erasure followed by structural-size
evaluation is composed through squares and compared with direct cached-size
evaluation. The numerical observation uses `ULift` to admit arbitrary value
universes. Decoding is an observation; its traversal is not included in these
end-operation counts. Square commutation states value refinement; separate laws
state exact costs and bounds.

## Statement review

All source signatures and new public claims were reviewed against their
operations and independent list/binary/tree meanings. Grouped results below
cover the declarations in the ledger and the added correspondence/consumer
claims. Value types remain universe-polymorphic. Costs are finite abstract
composite-unit counts, not hardware time, allocation or arithmetic bit costs.

- Structural size value/work and erasure hold for every tree. Cached selection
  always returns the installed size with work one. Only the equal-answer law
  requires `Cached`; no balance or rank hypothesis was added. Smart-node cache
  preservation requires the two child caches to be correct.
- Carry value, prepending refinement, counts, one-digit potential, skeleton
  increment/length/count/ones correspondence, and push telescoping are raw
  contracts. They include malformed states and retain the initial potential.
  The upper logarithmic bound requires `Inv` at rank zero and is in represented
  element length. No index-only bound or lower logarithmic bound is claimed.
- Skeleton canonicality requires `Valid r`. Its independent numeric value
  represents chunks of size `2^r`; it equals element length only at rank zero.
  Decrement is defined on every bit list, failing on zero and not normalizing
  arbitrary noncanonical inputs. Its canonical predecessor and numeric theorem
  require canonical nonempty input. `bits_unconsT` requires validity and the
  actual successful borrow equality. The checked numeric example combines that
  equality with the shared predecessor theorem for the same returned state.
- Borrow erasure and digit-visit bounds hold on raw input, including malformed
  tree shapes and empty failure. Head/tail project the same result and retain
  its count. The zero-digit potential bound requires validity and success;
  it is an inequality, distinct from the exact one-digit push identity.
- `drainRun_spec` covers every fuel value and valid input. It preserves residual
  validity and proves ordered `take`/`drop`, with both boundary potentials.
  Zero fuel performs no work. Failure charges one attempted borrow and stops,
  leaving the current raw state. Full drain uses exactly the initial represented
  length, returns an actually empty digit list, and costs between N and 3N.
  Empty full drain costs zero; an attempted removal from empty costs one.
- `borrowCost_consT` needs a valid digit tail at arbitrary rank, but imposes no
  extra perfection assumption on the inserted tree. The value-returning
  push/pop identity uses a leaf and rank-zero validity. Repeated valid cycles
  return the identical representation, with exactly n times the pair cost.
  `fullDigits` is valid at arbitrary starting rank; its carry depth is p+1.
  `no_uniform_mixed_charge` quantifies over every Nat-valued state potential and
  constant C, then constructs a valid costly return cycle. It does not merely
  refute the two displayed potentials. Separate push and pop amortized bounds
  cannot establish a constant bound for unrestricted mixed sequences.
- Explicit lookup errors retain the exact string `index too large`. Error and
  success iff statements require valid input and use independent list indexing.
  The generic `bulk_scan_refinement` preserves every reachable state and the
  seed via `SquareKit.ListFusion.scanl_reachable`; source trace and final-state
  examples now derive from scan and fold refinement instead of stand-alone
  numeral reduction. Four-element tree and borrow states preserve the source
  constructor/order/cache distinctions.
- Consumer representations decode the actual carrier results. Construction
  and bounded/full drain preserve order and accumulate both costs. The full
  composed bound is the valid sum bound 5N. Push/pop observes the returned value
  and original ordinary sequence and separately proves twice the carry cost.
  Cached/structural comparison retains one selector event versus all structural
  constructor visits. No cost claim follows merely from forgetting observations.

## Checked applications and validation

`Examples/RandomAccessEndCosts.lean` exercises the public contracts. The initial
source bulk trace was reducible but lacked a connection to a general trace
refinement; the shared reachable scan theorem supplies that missing connection.
The composed consumers supply the missing link between measured operations and
ordinary observations, with cost checked independently of value commutation.

Cases cover empty/singleton states; zero, insufficient, exact and excess drain
fuel; four-element construction cost seven and drain cost seven; the one extra
failed attempt during over-draining; nonempty initial potentials; malformed
cache and borrow shapes; correct unbalanced caches; nonzero-rank skeletons;
binary zero and noncanonical boundaries; carry/borrow correspondence and numeric
decrement; actual composed push/pop; three depth-three cycles costing 24; and
the impossibility theorem specialized to an arbitrary potential and constant.
Source lookup errors, four-element borrow intermediates and the ordered bulk
trace are also consumed through public results.

Targeted validation: `lake build Examples.RandomAccessEndCosts
Examples.RandomAccessCosts Examples.RandomAccessLists Examples.PotentialAccounting
Examples.Resources` passed through direnv (784 jobs). All 80 ledger destinations
also elaborated with `#check`; selected consumer and impossibility signatures
were inspected with universes displayed. This checks the new client, accepted
random-access clients and shared counter/resource regressions. Independent
reviews, full fresh build and exhaustive axiom audit remain the integration gate.
Tree-flattening costs, asymptotic helper modules, lazy semantics and other
textbook clients remain outside this issue.

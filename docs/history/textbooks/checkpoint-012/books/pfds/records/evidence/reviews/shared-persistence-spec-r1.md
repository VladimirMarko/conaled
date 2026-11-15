# Shared persistence — independent Spec review, round 1

Date: 2026-11-02.
Reviewer: `/root/architecture_inventory/chapter01_spec`.

## Scope and outcome

- Base/merge base: `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`.
- Candidate: `ad730010ab1929bbd7a16a035c7990a6f328b178`.
- Isolated checkout: `/workspace/scratch/ca9a61d0bf30/validation-persistence`.
- Diff: `git diff BASE...CANDIDATE`; sole commit `ad73001`, eight changed files,
  no exclusions.
- Requirements: `session/requirements/REQUEST.md` and
  `session/requirements/shared-persistence.md`, version 2.
- Acceptance scope: cross-cutting local ticket 10013 only. This review cannot
  accept any chapter or resolve the missing book-source gates.
- **Current outcome: Blocked pending required exact-candidate validation.**
- Static Spec review is complete with **zero implementation findings**.

I read the complete candidate changes: four shared-list semantic modules,
the resource module, checked examples, entrypoint changes and implementation
note. I also inspected the primary excerpt's list material, printed pages 7–11,
against the stated bounded scope. The earlier statement-check note was used as
context and its reported correction was independently inspected; that note was
not treated as an acceptance review.

## Statement review

### Allocation, meanings and persistence

`Store.vacant` guarantees that the frontier address is free, rather than
assuming freshness without a usable instance. `allocate_extends` applies the
existing generic fresh-write theorem; `allocate_retains` transports an arbitrary
old represented root, not only the new cell's tail. `allocate_represents` separately
requires a valid tail and derives the interpretation of the new root.

`Represents` carries finite ordered values and the strict address-decrease
condition. Its uniqueness theorem concerns observation at one root; it does not
assert unique representations of a value. The frontier bound is derived from
occupied-cell vacancy, and the chain-length bound is derived from strict descent.
`load_represents` constructs a valid instance for every finite list, establishing
that the validity/fuel premises are satisfiable.

The retained old/new example invokes the public generic retention theorem and
uses head correctness for both roots. This checks persistence independently of
simple literal evaluation. The general one-allocation frontier increment also
applies twice to its two allocations.

### Actual path copying

The append implementation reads the original heap and recurses through actual
tail roots before allocating the copied prefix. It neither decodes and rebuilds
the entire output nor copies the right argument. The result theorem retains
heap extension, `xs ++ ys`, the exact left-length frontier increase, the
left-length-plus-one structural visits, and equality with the exact right root
after that many prefix links. Existing old roots remain represented by monotonicity.
The concrete append example establishes all these conclusions and uses the
composed head observation.

Indexed replacement copies exactly the path through the replaced cell. The
success theorem's domain is `i < xs.length`, and its conclusion uses ordinary
`List.set` only within that domain. It proves the exact `i+1` allocation and
visit counts, retains the entire old heap, and identifies the untouched suffix
root reached after `i+1` links. The example's sharing equality is not vacuous:
validity plus `advance_prefix` establishes successful traversal on both sides.

The failure theorem covers `xs.length ≤ i`, including equality, and returns
`none` after `length+1` visits. Since recursive allocations are mapped over the
successful result only, no output store is manufactured when traversal fails.
This faithfully distinguishes failure from the totalized `List.set` no-op.
These contracts use natural indices, matching the bounded specification;
they are not a complete model of every Standard ML integer input.

### Fuel, malformed inputs and optional observations

Public fuel is the existing frontier. The proofs establish that it suffices
for every represented input rather than assuming successful evaluation. Raw
operations fail on encountered missing cells and on fuel exhaustion at a
non-null root. A null case needs no link-read fuel but is still charged one
visit. Neither append nor update is claimed to validate an untraversed root.

Empty tail failure and successful singleton removal are distinct `Option Root`
values. `optionalRepresentation` preserves failure versus successful results;
the subsequent head observation can deliberately forget that distinction.
The `RelSquare` adapters derive append/update client correctness by composition.
Their cases exercise these public contracts, including the explicit failed
update and non-null zero-fuel case.

### Suffixes and shared storage

The suffix operation returns the actual roots encountered along the original
chain, including null; it takes no mutable/output store and does not copy element
cells. Its represented-input theorem retains the independent standard
`List.tails` observation, order, exact visits, outer-list length, non-null root
count and root distinctness. Strict address decrease prevents duplicate roots
without imposing payload distinctness.

The formerly missing graph connection is now substantive:

- `suffixesRunFuel_chain` extracts an actual-tail `SuffixChain` from successful
  execution.
- `SuffixChain.closed` proves no read tail is omitted.
- Independent `Reaches` and `ReachableFrom`, together with closure, equate
  reachable addresses with the listed non-null roots.
- `nonnull_nodup` turns valid-input distinctness into a duplicate-free address
  enumeration.
- `suffixes_storage` combines actual execution, reachability, distinctness and
  the exact cell count in a checked application.

The retained counterexample correctly demonstrates why equal suffix values
and distinct roots would not suffice: an extra element cell is reachable but
not listed, and the proposed roots fail closure. `Reaches.here` counts an
address without separately asserting occupancy, but successful `SuffixChain`
and represented-input premises guarantee occupancy in the reviewed storage use.
No unjustified generic live-cell claim is made from bare `Reaches` alone.

`sharedSpace` is explicitly a count requiring these graph/distinctness premises,
not an arbitrary-root storage theorem. In the valid suffix result it gives
`n` reachable element cells plus `n+1` outer root-list cells. The derived
standard `IsBigO` theorems concern the exact `n+1` visits and `2*n+1` count
functions. They neither count all unrelated cells in the original store nor
establish an actual Lean allocation or timing bound.

## Scope and assumptions

The fixed-cell model excludes payload size, allocator metadata, traversal-stack
space, finite-capacity failure, garbage collection and compiler/runtime costs;
these limits are explicit. Abstract heap reads and frontier arithmetic are not
silently identified with constant-time Lean evaluation. The prerequisite does
not assert arbitrary branching amortization or crash persistence. The full
stack-interface/custom-stack correspondence and unseen BST material remain
chapter obligations. These boundaries match version 2 rather than narrowing
its acceptance scope.

## Validation gate

At static review time the exact candidate checkout was clean and resolved to
`ad730010ab1929bbd7a16a035c7990a6f328b178`. The running isolated Nix command is
`env LEAN_NUM_THREADS=1 ./check.sh --candidate HEAD`, logged at
`session/validation/persistence-ad73001-check.log`. The observed log shows the
source-policy check passing and a normal cold build beginning; it does not yet
supply full successful compilation or the exhaustive axiom audit.

No compilation was run by this reviewer and no completed approval is inferred
from partial logs or the earlier focused builds. Successful full candidate
validation, its recorded identity and the immediate final
`./check.sh --verify-candidate HEAD` remain required before this axis may pass.

**Current Spec result:** Blocked on validation; no implementation findings.
Base `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`, candidate
`ad730010ab1929bbd7a16a035c7990a6f328b178`.

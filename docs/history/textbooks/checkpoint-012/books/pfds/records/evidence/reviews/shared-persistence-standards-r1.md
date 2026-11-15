# Shared persistence prerequisite — Standards review, round 1

Outcome at static-review completion: **Blocked pending required validation**.
Code/prose findings: **0**. This is not approval and does not accept a chapter.

## Pinned scope

- Local ticket: #10013, a cross-cutting prerequisite explicitly permitted by
  the original user request.
- Fixed base and confirmed merge base:
  `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`.
- Candidate: `ad730010ab1929bbd7a16a035c7990a6f328b178`.
- Isolated checkout: `/workspace/scratch/ca9a61d0bf30/validation-persistence`.
- Diff: `git diff cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833...ad730010ab1929bbd7a16a035c7990a6f328b178`.
- Commit: `ad73001 feat(persistence): model shared lists and path copying (#10013)`.
- Eight changed files: the four `Applications/Sequences/SharedList` modules,
  `Applications/Resources/SharedList.lean`, `Examples/SharedList.lean`,
  `SquareApplications.lean`, and `docs/research/pfds-shared-persistence.md`.
- No exclusions or unrelated changes. Observed checkout HEAD matches candidate;
  working-tree status was clean when inspected.
- Requirements: `session/requirements/REQUEST.md` and
  `shared-persistence.md`, version 2. The raw traversals are not validators of
  untraversed roots; this explicit scope is retained throughout the review.

## Applicable standards and evidence

Read AGENTS and the applicable architectural/domain, glossary and ADR 0001/0010
rules, README build/candidate validation requirements, example-driven development
and statement-review guidance, and code-review heuristics. Reused previously
read unchanged standards within this review role and inspected the current
candidate's applicable text and dependencies.

Read every changed Lean module and the implementation note. Inspected reused
heap-extension primitives in `Applications/Durability/Storage.lean`, measured
results in `Applications/Resources/Measured.lean`, asymptotic conversion in
`Applications/Resources/Growth.lean`, and relational composition in
`SquareKit/Relations.lean`. The prior source-to-statement assessment is useful
background; this review independently checked its corrected reachability
contract and does not treat that earlier assessment as approval.

## Architectural review

The candidate reuses `Durability.Heap`, `Extends`, `put`, and `extends_put`
rather than introducing competing fresh-write algebra. A store frontier
supplies freshness, while the separate `Represents` relation describes a valid
finite list rooted in the heap. The relation places no validity requirements
on unrelated cells. Operations, observations, validity and resource quantities
remain distinct.

Actual heap-link traversal is preserved by append, indexed update and suffix
enumeration. The implementations do not discharge sharing claims by decoding
and rebuilding list values. `Resources.Measured` is reused for observation pairs;
frontier growth records modeled allocations independently of structural visits.
The ordinary relational-square adapters compose existing preservation laws
without a new mandatory container abstraction or proof language.

The bounded model and remaining obligations are accurately documented. Natural
addresses and function-valued heaps are abstract memory; no compiler, allocator,
machine-time, capacity, garbage-collection, durable-write or arbitrary persistent
amortization guarantee is claimed. Reuse of a primitive housed in `Durability`
does not import its later crash/record assumptions into these theorem premises.
The implementation also avoids claiming transport of list induction into a
different mathematical setting.

Existing modules remain unchanged apart from the public import additions.
`Examples.SharedList` imports `Observation` and `Suffixes`; `Observation` imports
`Copy`, and `Copy` imports `Basic`. The separate resource module is directly
imported by `SquareApplications`, so the new modules are within the stated
public build/audit closure. No incompatible ADR or public interface change was
identified.

## Statement and connected-case review

| Family | Inspected contract and application evidence |
| --- | --- |
| Heap representation | `Represents.unique` establishes unique list observation, not unique roots. `Represents.mono` preserves arbitrary old represented roots under actual heap extension. `length_le_next` bounds valid-chain length using backward live links and the store frontier. |
| Allocation | `allocate_extends` uses the existing fresh-write theorem and `Store.vacant`; `allocate_retains` covers old roots independent of the supplied tail. `allocate_represents`, `prepend_correct`, and `load_represents` construct usable validity instances. `old_version_retained`, `new_version_correct`, and `both_heads` consume these public contracts. |
| Append | The returned measured result, exact left-length allocation, global old-cell extension, concatenated list value, and equality with the original right root after the copied prefix occur in one correctness statement. `append_shares` retains both inputs, checks two copied cells, and exercises exact-root sharing. |
| Partial update | Success requires `i < length` and proves `List.set` agreement plus exact allocation and untouched-tail equality. Failure requires `length ≤ i` and returns `none`, with its exact visit count. `update_shares`, `update_past_end`, and the composed failure client check the semantic boundary at index equal to length. |
| Head/tail and traversal | `head_correct`, `tail_cons`, and `tail_empty` retain the distinction between empty failure and a successful null tail. `advance_prefix`, `advance_mono`, and `advance_end` concern actual reads rather than a list-level proxy. The singleton tail and insufficient-fuel cases expose the consequential Option distinctions. |
| Suffix semantics | `suffixesRun_correct` relates the actual returned root list to standard `List.tails` in order, including null, and proves root counts and distinctness. Payload equality is never assumed; duplicate payloads do not collapse distinct addresses. |
| Suffix storage | Independent `Reaches`/`ReachableFrom`, actual-tail `SuffixChain`, closure and `nonnull_nodup` justify the root-entry count as a duplicate-free enumeration of reachable element addresses in the successful application. `suffixes_storage` connects these results, and the retained unshared-equal-values counterexample demonstrates why observation equality and distinct roots alone are insufficient. |
| Composition | `appendSquare`, `updateSquare`, and `headSquare` preserve optional failure/success representations. `appendHeadSquare` and `updateHead_correct` reuse `Relational.compose`; the examples use their public claims. Head observation may forget distinctions, as documented, without equating the underlying results. |
| Asymptotics | `visits_linear` and `space_linear` are explicit specializations of existing `Resources.isBigO_of_nat_bound` for the proven count expressions. Constants and eventual lower threshold are supplied; these claims do not assert machine running time. |

The definitions and theorem hypotheses were checked for circularity, vacuity,
quantifier/domain mistakes and hidden equality assumptions. No such defect was
identified. Fuel correctness uses represented inputs with sufficient frontier
fuel; raw missing reads/non-null fuel exhaustion remain explicit failures.
Untraversed right roots/tails need not be validated, matching requirements v2.

`Reaches.here` denotes zero-edge address reachability without proving occupancy.
This is not misused as a generic validity theorem: successful suffix traversal
provides the actual chain, and represented inputs establish the occupied cells
in the reviewed storage application. `sharedSpace` is documented as an entry
count whose storage interpretation additionally requires reachability and
distinctness evidence; the connected example supplies them.

The examples use the new public results and construct their premises; they are
not merely disconnected concrete reductions. The implementation record states
the original missing graph obligation and its correction. No new proof
placeholder, assumed application axiom, unsafe implementation, or claimed
native-evaluation shortcut was found in source inspection. This observation
does not replace the exhaustive kernel/axiom check.

## Findings

No Standards code/prose findings were identified. No heuristic-only change is
requested. No `PERSIST-STD` identifier has been allocated because there is no
defect to track.

## Validation status and remaining gate

The root's required isolated Nix command is still running:

`env LEAN_NUM_THREADS=1 ./check.sh --candidate HEAD`

Log: `session/validation/persistence-ad73001-check.log`.
At inspection, the log showed the normal cold-checkout invalidation of 957
project modules and the beginning of compilation; it did not yet establish a
complete build or exhaustive proof audit. Missing initial traces in a new
checkout are normal under the repository runbook and are not an incident.

The reviewer has not compiled, mutated source, or launched another validation
process. Focused development results are not substituted for exact-candidate
acceptance. Before a pass, the coordinator must supply successful completion
for this candidate, its `.lake/verification.json`, and the required immediate
`./check.sh --verify-candidate HEAD` result. Any changed candidate requires
review of the full change against the stable base again.

## Result

Base `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`; candidate
`ad730010ab1929bbd7a16a035c7990a6f328b178`.

**Standards: Blocked pending exact-candidate build, exhaustive proof audit and
final verification evidence; 0 unresolved code/prose findings.** This review is
limited to local #10013 and neither accepts a PFDS chapter nor resolves its
independent source-coverage gates.

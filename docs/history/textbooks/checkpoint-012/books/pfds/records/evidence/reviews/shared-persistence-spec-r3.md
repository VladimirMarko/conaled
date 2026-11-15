# Shared persistence and import prerequisite — independent Spec review, round 3

Date: 2026-11-02.
Reviewer: `/root/prerequisite_review/spec`.

## Outcome and immutable scope

**Spec: Blocked pending exact-candidate integrated validation.** Static review
is complete with **0 unresolved implementation findings**. This result covers
local #10013 round 3 and the linked import-only #10018 round 1; it accepts no
chapter and does not approve the concurrently edited Chapter 2 implementation.

- #10013 fixed base and independently confirmed merge base:
  `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`.
- Candidate: `226ebaef53b9eba97bef4b3b6ca364fdea488c69`.
- Full diff:
  `git diff cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833...226ebaef53b9eba97bef4b3b6ca364fdea488c69`.
- #10018 fixed base and independently confirmed merge base:
  `70a1477d822efd4fdcec2007280f650bb4695eda`.
- Narrow import diff:
  `git diff 70a1477d822efd4fdcec2007280f650bb4695eda...226ebaef53b9eba97bef4b3b6ca364fdea488c69`.
- Full commits: `ad73001` SharedList implementation, `70a1477` redundant
  adapter-tactic correction, and `226ebae` direct FRP imports.
- Ten changed files, 951 insertions and 2 deletions, no exclusions. All eight
  SharedList/integration/documentation files are unchanged from round 2; the
  only new changes are import lines in `Applications/FRP/Spec.lean` and
  `Applications/FRP/Equivalence.lean`.
- Read-only isolated checkout:
  `/workspace/scratch/ca9a61d0bf30/validation-imports`. Observed `HEAD` matches
  the candidate and porcelain status was empty at initial and final inspection.

The ticket-specific import result is also recorded in
[`import-footprint-spec-r1.md`](import-footprint-spec-r1.md). Both reports belong
to this one independent Spec assessment; they do not create a second review axis.

## Requirements, guidance and retained evidence

The acceptance requirements are the saved original `REQUEST.md`, the
`REQUEST-union-v2.md` clarification, unchanged `shared-persistence.md` version 2,
and `import-footprint.md` version 1 in `session/requirements`. The union of the
complete book and thesis is the whole task's scope. The full sources are now
available, but availability is not inspection, formalization or chapter
acceptance. The bounded prerequisites neither replace the chapter work nor
claim coverage of the union by themselves.

I retained all four prior round-1/round-2 axis reports and the coordinator's
finding record. Their static analysis is useful for unchanged content; neither
round passed validation, so no prior approval is reused. The saved
source-to-statement assessment is background evidence, not an acceptance axis.
I independently reread the candidate's four semantic SharedList modules,
resource module, connected examples, public-entrypoint additions and complete
implementation note. I also read both affected FRP modules, their actual
import providers and relevant unchanged consumers.

The applicable candidate guidance is AGENTS, the code-review and shared
review-loop procedures, example-driven development's statement review,
architectural/domain/glossary guidance, relevant ADRs 0001/0002/0010 and README's
candidate validation rules. Reused interfaces inspected include
`Durability.Heap`/`Extends`/`put`/`extends_put`, `Resources.Measured`,
`Resources.isBigO_of_nat_bound`, and `Relational.RelRep`/`RelSquare`/`compose`.
The scope and statements below were assessed for intended meaning, usable
hypotheses, quantifiers, domains, vacuity and actual connections to examples.

## Full SharedList statement review

### Allocation and retained versions

`Store.vacant` means every occupied address lies below the frontier; it supplies
the fresh address used by `allocate`. `allocate_extends` invokes the existing
fresh-write theorem, while `allocate_retains` quantifies over an arbitrary old
represented root. The old-root guarantee is not restricted to the new cell's
tail. `allocate_represents` separately requires a represented tail and
constructs the new represented list.

`Represents` follows occupied cells and strictly decreasing tail addresses.
Its uniqueness theorem is uniqueness of the list observation at a given root,
not uniqueness of roots for a list value. The frontier bound follows from
vacancy and actual occupancy. The chain-length bound follows from strict
descent, and `load_represents` constructs a valid store/root for every finite
list. These facts make the validity and fuel premises usable.

The retained `[3]`/`[2,3]` example invokes generic allocation preservation and
head correctness for both roots. The one-allocation frontier theorem applies
to each of its two allocations. This is the requested persistence case, with
the value relation, fresh allocation and old-version retention kept distinct.

### Append and indexed replacement

Append reads cells in the original store, follows actual tail roots and then
allocates the copied left prefix. It does not decode the whole represented
list and rebuild the result. `appendRun_correct` simultaneously establishes
the actual returned result, `xs ++ ys`, all-old-cell heap extension, exactly
`xs.length` allocations, `xs.length + 1` structural visits, and equality with
the original right root after the copied prefix. The `[1,2]`/`[3,4]` example
uses this theorem, retains both inputs, gets six total cells from four original
cells and checks the exact right-root equality. Its head client uses the
composed public observation theorem.

Update reads the prefix through the selected cell, replaces that cell and
copies the earlier prefix. The success domain is `i < xs.length`; only within
that domain is the result related to `List.set`. The theorem proves `i + 1`
allocations and visits, all-old-cell retention, and equality of the actually
traversed untouched-tail roots. `advance_prefix` with valid input ensures the
sharing equality is not an equality of two failed traversals. The retained
index-1 example uses these results to obtain `[1,9,3]`, preserve `[1,2,3]` and
allocate exactly two cells.

Failure covers `xs.length ≤ i`, including equality. It returns `none` after
`length + 1` visits. Recursive allocations occur only through mapping a
successful result, so a failed traversal returns no new store. The explicit
index-equals-length case and its composed failure client therefore do not
silently become `List.set`'s totalized out-of-range no-op. Indices are natural
numbers, as in the bounded prerequisite; this is not a claim about every
Standard ML signed-index behavior.

### Fuel, failure and observations

The public fuel is `s.next`; the valid-input theorems derive sufficiency using
`Represents.length_le_next`. Encountered missing reads and non-null zero-fuel
cases fail explicitly. Null append/suffix cases need no link-read fuel and
still count one structural visit; null update fails with one visit. An
untraversed right root or retained tail is not claimed to be validated by the
raw operation. These distinctions match requirements version 2.

Empty tail failure and a successful singleton's null tail remain distinct
values, `none` and `some none`. `optionalRepresentation` also distinguishes
failed output from successful represented output. `appendSquare` and
`updateSquare` use the public traversal theorems; the independent head contract
is composed through `Relational.compose`. Subsequent head observation can
forget a distinction without identifying the underlying optional states.

### Suffix roots, reachability and modeled resource counts

The suffix operation returns the actual root at each recursive step and ends
with the null root. It returns no changed store and performs no element-cell
allocation. Its correctness theorem connects the returned root list to
standard `List.tails` in order, with `n + 1` visits/root-list entries, `n`
non-null roots and distinct roots. Distinctness follows from address order and
does not require distinct payloads.

The previously identified storage gap remains corrected. Successful execution
produces an actual-tail `SuffixChain`; the chain is closed under tail reads;
independent `Reaches`/`ReachableFrom` and closure establish that reachable
addresses are exactly the enumerated non-null addresses; `nonnull_nodup`
prevents overcounting. `suffixes_storage` consumes those public results and the
actual successful run. The retained counterexample still demonstrates that
distinct roots with equal suffix values alone can omit a reachable element
cell and fail closure.

`Reaches.here` denotes zero-edge address reachability without separately proving
occupancy. Successful suffix chains and the represented-input contracts supply
occupancy in the reviewed storage use; no generic live-cell theorem is inferred
from bare reachability. `sharedSpace` is explicitly an entry-count function
whose shared-storage reading needs the graph and distinctness evidence. Its
valid suffix result counts `n` reachable element cells plus `n + 1` outer
root-list cells. It does not count unrelated cells in the store.

The `IsBigO` results are standard asymptotic statements for the proved count
expressions `n + 1` and `2*n + 1`, using explicit eventual bounds. Abstract
heap access, natural-address arithmetic and fixed-cell counting are not
identified with Lean allocation, elapsed time, allocator metadata, payload
size, stack space, garbage collection, finite capacity, crash durability or
branch-safe amortization. These limitations remain explicit in the frozen
implementation note and match the bounded requirements.

## Import-only prerequisite assessment

I compared the exact Git objects at `70a1477` and `226ebae`. Removing only lines
beginning `import ` from each affected file leaves byte-identical content:

| File | SHA-256 of all non-import bytes, equal at both commits |
| --- | --- |
| `Applications/FRP/Spec.lean` | `1d59e171221416cb3eabc47bc74b788d347a3f2456379228d5101bb64632e35a` |
| `Applications/FRP/Equivalence.lean` | `063f840af1065f9af828204d4c56dd6a314a49aa59a2f193332b175fd3f22188` |

The only removed source is the two aggregate `Mathlib` import lines. `Spec`
retains its existing local category/map imports and directly names real-number,
finite-set sorting and finite-set evidence providers. `Equivalence` directly
names real-number, finite-set extrema/cardinality, finite-set range,
lexicographic product, natural interval, linear-arithmetic, numeric-normalization
and positivity providers. Each path exists in the pinned Mathlib source; the
selected facilities correspond to uses in the affected modules.

Both FRP modules retain their declarations, proof bodies, examples and
assumptions, including finite-predecessor versus finite-history distinctions,
ordered simultaneous occurrences and strict switching. I inspected the direct
consumers `Applications.FRP.Finite`, `Applications.FRP.Frontier` and
`Examples.FRP`, including finite-batch correspondence, prefix behavior and
connected square examples. They remain in the public integration closure.
No missing import is established by static inspection; complete compilation
of all affected consumers is still required to establish compatibility with
the narrower elaboration environment.

The import delta does not change `SquareApplications`, `ProofAudit`, verification
scripts, toolchain/dependency configuration, guard behavior, source policy or
axiom allowlist. All project declaration sources and the exhaustive root-selection
logic are preserved. This is not a claim that an unrun exhaustive audit has
already passed. No matched memory or timing benchmark has been supplied, so I
make no performance-improvement claim from the import reduction.

## Prior finding disposition and current findings

**PERSIST-VAL-001 remains fixed with compiler evidence.** The candidate retains
`70a1477`'s removal of the redundant `change` tactic in `updateSquare`'s success
branch. The failure-branch tactic remains, and the operation, theorem type,
premises and proof meaning are unchanged. The focused round-2 log explicitly
records `Observation` and `Examples.SharedList` compiling and ends with
`Build completed successfully (664 jobs)`. That establishes the specific lint
correction; it is not this candidate's integrated acceptance result.

There are **0 unresolved Spec implementation findings** for either #10013 or
#10018, and no new Spec finding identifier is allocated. Historical rounds
remain Blocked and are not retroactively promoted. No requirement change,
source correction or additional implementation is requested by this static
assessment.

## Exact validation status and continuation

At final inspection, `session/validation/import-footprint-226ebae-full.json`
still identifies the exact candidate, reports `status: running` and
`acceptance: false`, and points to
`active-validation/import-footprint-226ebae-full.log`. The logged command uses
the pinned offline Nix environment and
`env LEAN_NUM_THREADS=1 ./check.sh --candidate HEAD`. The log explicitly says
`Building 957 project modules with Lake (incremental)` and shows continuing
compilation, but does not establish terminal full-build/audit success.
`validation-imports/.lake/verification.json` was absent.

The exact missing evidence is:

1. Successful terminal completion of the full candidate check, including every
   integrated project module and the exhaustive proof audit.
2. Its matching `.lake/verification.json` for
   `226ebaef53b9eba97bef4b3b6ca364fdea488c69`, with the required input identity.
3. Immediate final `./check.sh --verify-candidate HEAD` evidence resolving to
   that same candidate.

I did not compile, mutate source/dependencies/build outputs, start a competing
validation process, or treat focused compilation or partial logs as acceptance.
Once those three evidence items are supplied on the unchanged candidate, this
axis can continue by assessing them while retaining the completed static
review. Any new source candidate requires review of the whole fixed-base scope
again and retention of every prior finding.

## Result

| Ticket | Fixed base | Candidate | Findings / worst severity | Spec outcome |
| --- | --- | --- | --- | --- |
| #10013, round 3 | `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833` | `226ebaef53b9eba97bef4b3b6ca364fdea488c69` | 0 unresolved implementation findings; no severity | **Blocked on exact validation** |
| #10018, round 1 | `70a1477d822efd4fdcec2007280f650bb4695eda` | `226ebaef53b9eba97bef4b3b6ca364fdea488c69` | 0 unresolved implementation findings; no severity | **Blocked on exact validation** |

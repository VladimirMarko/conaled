# Shared persistence and import prerequisite — independent Standards review, round 3

Date: 2026-11-02.
Reviewer: `/root/prerequisite_review/standards`.

## Outcome and immutable scope

**Standards: Blocked pending exact-candidate integrated validation.** Static
review is complete with **0 unresolved code/prose findings**, no worst severity
and no heuristic-only change request. This is the independent Standards axis
for local #10013 round 3 and linked import-only #10018 round 1. It accepts no
chapter and does not approve the concurrent Chapter 2 implementation.

- #10013 fixed base and independently confirmed merge base:
  `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`.
- Candidate: `226ebaef53b9eba97bef4b3b6ca364fdea488c69`.
- Full review diff:
  `git diff cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833...226ebaef53b9eba97bef4b3b6ca364fdea488c69`.
- #10018 fixed base and independently confirmed merge base:
  `70a1477d822efd4fdcec2007280f650bb4695eda`.
- Narrow import diff:
  `git diff 70a1477d822efd4fdcec2007280f650bb4695eda...226ebaef53b9eba97bef4b3b6ca364fdea488c69`.
- Full commit list: `ad73001` SharedList implementation, `70a1477` redundant
  adapter-tactic correction, and `226ebae` direct FRP imports. Their messages
  follow the applicable Conventional Commits form with local ticket numbers.
- Ten changed files, 951 insertions and 2 deletions, no exclusions. The original
  eight #10013 files are unchanged from round 2. The candidate-to-candidate
  diff changes only the import lists in the two FRP files.
- Read-only isolated checkout:
  `/workspace/scratch/ca9a61d0bf30/validation-imports`. Initial and final
  inspections resolved `HEAD` to the candidate and returned empty porcelain status.

The separate ticket-specific report is
[`import-footprint-standards-r1.md`](import-footprint-standards-r1.md). It links
this complete full-scope assessment and does not create another review axis.

## Requirements and standards used

The saved original `REQUEST.md`, union clarification `REQUEST-union-v2.md`,
unchanged `shared-persistence.md` version 2, and `import-footprint.md` version 1
are the requirements. Their fingerprints are preserved in the coordinator
record. The whole task now covers the full book and thesis; both sources are
available. These bounded prerequisites do not claim complete inspection,
formalization, or acceptance of either source or a chapter.

I read the frozen candidate's AGENTS, code-review and shared review-loop
procedures, example-driven-development statement-review guidance,
architectural/domain/glossary rules, ADR index and relevant ADRs 0001, 0002
and 0010, the applicable language-direction criteria, README environment and
build/audit requirements, and subordinate code-review heuristics. No additional
scoped AGENTS, CODING_STANDARDS or CONTRIBUTING file applies to these paths.
The user's local-tracking and no-GitHub-publication instructions override the
repository's default issue destination.

All four historical round-1/round-2 reports and the existing finding record
remain retained. Their analysis guides unchanged content; their Blocked
outcomes are not approval of this candidate. I independently reread all four
SharedList semantic modules, the resource module, connected examples,
entrypoint additions, frozen implementation note, and both complete affected
FRP modules. I inspected the reused heap, measurement, asymptotic and relational
interfaces and the direct FRP consumers. The source-to-statement assessment is
background evidence, not a substitute review.

## Architecture and methodology

The development uses the existing `Durability.Heap`, `Extends`, `put` and
`extends_put` definitions. The reused fresh-write theorem requires only a
vacant address; it does not introduce the storage module's later crash or
record protocol assumptions. `Store.vacant` supplies that vacancy, while
`Represents` separately expresses finite list observation and strict address
descent. Unrelated cells need not form lists. Root identity, observation
equality, validity, retained cells and resource quantities remain distinct.

Append and replacement follow actual heap links. Their public contracts
include both ordinary list semantics and exact root-sharing conclusions.
`Resources.Measured` remains an ordinary value/observation pair; frontier
increments count modeled allocations separately from structural visits.
The observation layer specializes existing `RelRep` and `RelSquare` and uses
`Relational.compose`. It does not impose a new container hierarchy, a total
decoder for malformed heaps, or representation injectivity.

This meets the applicable architectural and ADR requirements for local reuse,
weak relevant assumptions, separate observations and reusable composition.
The candidate does not claim a general setting-transport mechanism, Felix
capability parity, or a runtime refinement. There is no competing shared
interface or retrofit that silently changes existing clients' contracts.

The implementation record states the missing sharing obligation and the
substantive correction exposed by the source-to-statement assessment. Its
retained counterexample distinguishes value-level suffix observations from
actual reachable storage. The checked applications construct their premises
and use the public results; they are not disconnected literal reductions.
The general fresh-allocation theorem also establishes the two successive
frontier increments in the old/new-root case.

The new modules retain explicit `autoImplicit false` and `warningAsError true`.
No added proof placeholder, assumed application axiom, unsafe declaration or
native-evaluation proof shortcut was found in the changed source. This source
inspection does not replace the mandatory exhaustive axiom audit.

## Statement and connected-case assessment

| Family | Standards assessment and retained applications |
| --- | --- |
| Representation and allocation | `Represents.unique` proves unique list observation at one root, without claiming unique representation. `allocate_retains` preserves arbitrary old represented roots through actual heap extension. `allocate_represents`, `prepend_correct` and `load_represents` construct satisfiable validity instances. The old/new versions and both-heads case consume these results. |
| Fuel and root traversal | `Represents.length_le_next` derives sufficient public fuel from occupied-cell vacancy and strict descent. `advance_prefix`, `advance_mono` and `advance_end` concern actual reads. Encountered missing cells and non-null exhaustion fail, while null cases retain their documented one-visit behavior. No untraversed root is silently claimed to be validated. |
| Append | `appendRun_correct` connects the actual result to concatenation, all-old-cell retention, exact left-length allocation, left-length-plus-one visits and the original right root. `append_shares` retains both inputs and exposes two copied cells; the head client uses composed correctness. |
| Replacement | Success requires a strict in-range index and establishes `List.set`, exact prefix-copy counts and untouched-tail equality. Validity and `advance_prefix` make that equality nonvacuous. Failure covers index equal to length and beyond, returns no output store and is kept distinct from a totalized out-of-range no-op. Both success and failure clients are retained. |
| Optional observations | Empty-tail failure and successful singleton removal remain `none` versus `some none`. `optionalRepresentation` retains the failure/success distinction. Composed head observation can forget a distinction without identifying the underlying representations. |
| Suffix values | `suffixesRun_correct` relates actual roots to standard `List.tails` in order, including the null suffix, with exact visits, root-list length and non-null counts. Address descent supplies root distinctness without payload equality or ordering. |
| Suffix storage | Successful execution yields an actual-tail `SuffixChain`; closure and independent `Reaches`/`ReachableFrom` identify reachable addresses with the non-null enumeration. `nonnull_nodup` prevents overcounting. `suffixes_storage` connects these public facts to the count, and the equal-valued unshared-root counterexample remains meaningful. |
| Asymptotics | The linear bounds specialize `Resources.isBigO_of_nat_bound` with explicit constants and eventual thresholds for the proved count expressions. They retain the standard asymptotic interface without asserting machine time or actual Lean allocation. |

I checked the statements and relevant definitions for vacuity, circular
assumptions, quantifier/domain mismatches and concealed equality claims. No
such defect was identified. `Reaches.here` is zero-edge address reachability,
not occupancy in an arbitrary heap; the successful chain and represented-input
premises supply occupancy for the reviewed storage interpretation. The model
does not count unrelated cells, payload size, allocator metadata, stack space,
reclamation, finite capacity, or arbitrary branching amortization.

The module placement follows ADR 0001. `SquareApplications` imports
`Examples.SharedList` and `Applications.Resources.SharedList`; the semantic
modules are reachable through their ordinary imports. Existing entrypoint
imports are retained. The candidate therefore preserves the intended public
integration route without excluding the new declarations from validation.

## Import-only prerequisite and integration surface

An independent comparison of the exact base/candidate Git objects found that
removing only lines beginning `import ` leaves identical bytes in each FRP
file. The resulting SHA-256 values at both commits are:

| File | SHA-256 of all non-import bytes |
| --- | --- |
| `Applications/FRP/Spec.lean` | `1d59e171221416cb3eabc47bc74b788d347a3f2456379228d5101bb64632e35a` |
| `Applications/FRP/Equivalence.lean` | `063f840af1065f9af828204d4c56dd6a314a49aa59a2f193332b175fd3f22188` |

Every named provider exists in the pinned Mathlib source. `Spec` names the
real-number, finite-set sorting and finite-set evidence facilities it uses,
and retains its existing local category/map imports. `Equivalence` names
real-number arithmetic, finite-set extrema/cardinality, finite-set range,
lexicographic product order, natural intervals, linear arithmetic, numeric
normalization and positivity. These correspond to its actual definitions,
order-enumeration proofs and counterexamples; no new all-library substitute
or local shim was introduced.

The direct consumers are `Applications.FRP.Finite`,
`Applications.FRP.Frontier` and `Examples.FRP`. I inspected their unchanged
finite-batch bridge, prefix/complete-window protocol and connected square
examples. The import narrowing leaves their source contracts and the original
FRP finite-predecessor/finite-history distinctions intact. No concrete missing
provider or changed meaning was found by static review. Compilation of the
complete affected closure remains necessary because the elaboration environment
has changed; byte preservation alone does not establish that gate.

The #10018 delta does not change any declaration source outside the two import
lists. Toolchain/dependency pins, `check.sh`, proof-audit code, source policy,
guard logic, axiom allowlist and public entrypoint remain identical to its
fixed base. No narrower audit root set or integration exclusion was added.
The import-history note correctly distinguishes focused development evidence
from acceptance and from a matched performance benchmark. This review makes
no memory or timing improvement claim.

## Prior finding and current findings

**PERSIST-VAL-001 remains fixed with compiler evidence.** The current candidate
retains only the removal of the unused success-branch `change` tactic from
`updateSquare`; the failure branch, theorem type, operation, hypotheses and
public clients are unchanged. The source still enforces its warning policy.
`session/validation/persistence-focused-r2.log` explicitly records compilation
of `Applications.Sequences.SharedList.Observation` and `Examples.SharedList`
and ends with `Build completed successfully (664 jobs)`. That evidence verifies
the particular linter correction, not this candidate's full acceptance.

There are **0 unresolved Standards code/prose findings** for either ticket.
No `PERSIST-STD` or `IMPORT-STD` identifier is allocated, and no heuristic-only
rewrite is requested. The earlier Blocked outcomes and validation history
remain preserved rather than retroactively promoted.

## Validation gate and continuation

At final inspection, the execution record
`session/validation/import-footprint-226ebae-full.json` still reported
`status: running` and `acceptance: false` for the exact candidate. Its argv
uses the pinned offline Nix closure and
`env LEAN_NUM_THREADS=1 ./check.sh --candidate HEAD`. The live log
`active-validation/import-footprint-226ebae-full.log` reports successful
source/coverage/version checks and explicitly says
`Building 957 project modules with Lake (incremental)`. It shows continued
compilation rather than terminal full build/audit success.
`validation-imports/.lake/verification.json` was absent.

The required remaining evidence is:

1. Successful terminal completion of the exact full candidate check, including
   all integrated project modules and the exhaustive proof audit.
2. Matching `.lake/verification.json` identifying
   `226ebaef53b9eba97bef4b3b6ca364fdea488c69` and the applicable input identities.
3. Final `./check.sh --verify-candidate HEAD` evidence resolving to that same
   candidate immediately before acceptance.

No compilation or source/dependency/build-output mutation was performed by
this reviewer. The checkpoint capture hold was respected; these two assigned
reports were written only after the coordinator relayed its release. Earlier
focused or interrupted builds and partial current logs are not substitutes
for the missing gate.

On the unchanged candidate, this axis can retain the completed static review
and assess the three new evidence items when supplied. A changed candidate
requires another full-scope review and retained finding dispositions. Neither
this outcome nor a later prerequisite pass accepts Chapter 2 or a later
integration tip.

## Result

| Ticket | Fixed base | Candidate | Findings / worst severity | Standards outcome |
| --- | --- | --- | --- | --- |
| #10013, round 3 | `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833` | `226ebaef53b9eba97bef4b3b6ca364fdea488c69` | 0 unresolved code/prose findings; no severity | **Blocked on exact validation** |
| #10018, round 1 | `70a1477d822efd4fdcec2007280f650bb4695eda` | `226ebaef53b9eba97bef4b3b6ca364fdea488c69` | 0 unresolved code/prose findings; no severity | **Blocked on exact validation** |

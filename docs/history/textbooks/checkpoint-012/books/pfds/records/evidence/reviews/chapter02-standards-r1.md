# Chapter 2 Standards review — round 1

**Outcome: Blocked pending exact-candidate validation.** Full-scope static
Standards review is complete. There are **zero unresolved implementation or
prose findings** and no heuristic change requests. The existing mandatory
validation gate CH02-PRE-005 remains open. This report does not accept Chapter 2,
SharedList prerequisite 10013, import prerequisite 10018, or any later chapter.

## Pinned review scope

- Reviewer: `/root/chapter02_review/standards`, independent Standards axis.
- Fixed base: `82501d108f33c62d21b5e0d0f7d2376b902d8d49`.
- Candidate: `69f6f00de204617fdd7feefd5b9ee5b80fc0d9f4`.
- Checkout: `/workspace/scratch/ca9a61d0bf30/validation-chapter02`.
- Observed HEAD equals the candidate. `git status --porcelain=v1` produced no
  entries. The confirmed merge base is the fixed base above.
- Full review diff: `git diff 82501d108f33c62d21b5e0d0f7d2376b902d8d49...69f6f00de204617fdd7feefd5b9ee5b80fc0d9f4`.
- Scope: 38 files, 35 Lean files, 4,464 insertions and 4 deletions, across 31
  commits. All changed files were inspected, including all definitions and
  proofs in the added Lean files, examples, source mapping, public entrypoint
  and the two FRP import changes. No exclusions or unrelated changes.
- The complete commit sequence is the fixed `git log` range from the base to
  the candidate, headed by `69f6f00 refactor(frp): import only the required
  mathematics and tactics (#10018)` and beginning with `8e894aa feat(sequences):
  add abstract stacks and integer update refinement (#10002)`.
- A read-only SHA256 comparison against
  `../validation/chapter02-candidate-r1.json` found **zero mismatches across all
  38 recorded inputs**. No source, ref, configuration, dependency or build
  artifact was changed by this reviewer. No compiler or acceptance check ran.

## Requirements and applicable standards

The review uses the complete saved user requirements in `../requirements/REQUEST.md`,
the union clarification `../requirements/REQUEST-union-v2.md`, Chapter 2
specification `../requirements/chapter02.md` version 1, and the narrow import
requirement in `../requirements/import-footprint.md` version 1. The user's
local-ticket and no-GitHub-write instructions override the repository tracker
destination. Both source identities, complete Chapter 2 inventory and thesis
ownership crosswalk are available in the supplied research records.

Applicable candidate guidance was read: `AGENTS.md`, architectural quality and
domain guidance, `GLOSSARY.md`, the ADR index and ADRs 0001/0010, the shared
review-and-fix procedure, `code-review` and its heuristics,
`example-driven-development` including statement review and its worked example,
and README development environment/build-and-audit requirements. The assigned
review continues the existing implementation loop; it does not start another
implementation or ordinary review loop.

The relevant standards require reuse of local and Mathlib constructions,
separation of operations from laws and observations, explicit assumptions,
meaningful checked specializations and composed clients, stable module
boundaries, public import/audit coverage, and exact isolated formal validation.
Judgment heuristics were considered as investigation prompts; repetitive
inductive proof branches and intentional distinct algorithm realizations were
not treated as automatic duplication defects.

## Architecture and statement review

The following findings are positive scope assessments, not a substitute for
Lean's pending integrated check or the independent Spec review.

| Area | Standards assessment and evidence |
| --- | --- |
| Abstract stacks | `AbstractStack.Ops` contains only the five source operations, while `Laws` carries the list observation relation. It permits invariants without demanding a total decoder. `appendRun_correct` derives actual successful execution and `4*n+1` primitive calls from sufficient fuel, rather than assuming output success. Both List and the distinct custom inductive stack realize the laws. `appendHead_correct` uses `Relational.compose`; examples exercise both realizations, empty versus successful-empty tail, empty append and surplus fuel. |
| Source integer update | `updateIntegerValue` is independent direct list recursion. `updateIntegerRunFuel_ofNat` is full measured execution equality, including raw fuel behavior. Negative execution follows the links and has the separately proved terminal-inclusive visit count. The nonnegative success theorem reuses SharedList's original path-copy result. Examples consume the public theorems for negative indices and retained suffix identity. No finite-machine arithmetic or runtime-cost claim is introduced. |
| Pure sets and ordering | Mathlib `BinaryTree` is reused. Whole-tree `Contains`, inorder `entries`, descendant-wide `All`, and key-specific `OrderedBy` are distinct from directed search. `AbstractSet` separates operators, validity and membership laws and reuses `SquareKit.ListFusion.foldl_reachable`. Baseline/candidate instances discharge those laws. `finite_contents` gives an independent finite enumeration and duplicate freedom from strict ordering. |
| Comparison optimizations | Actual `<` tests and final equality are charged by the corresponding recurrences. `LowerBound` records the candidate invariant. One combined candidate/abort algorithm has its own correctness and bound; the result is not assembled by conflating two distinct implementations. The ordered right-spine family establishes sharp counts on satisfiable inputs. Empty, absent, duplicate, bad-descendant and abstract insertion-word clients connect to public results. |
| Shared representation | `SharedTree.Store` reuses the existing fresh allocator and `Durability.Extends`; no crash/durable-write semantics is assumed. Tree `Represents` is independent of the list invariant and allows repeated labels and shared children. Backwards references justify sufficient frontier fuel by height, not unfolded size. New physical executions traverse stored references; they do not decode and rebuild values while calling the result a heap traversal. |
| Baseline copying and paths | `Rebuilds` distinguishes copied ancestors from an unconstrained focus. `off_path` compares addresses in the same final heap; `follow_mono` separately preserves successful old-heap observations. `insertRun_correct` derives success, exact comparison/visit/cell profile, frontier increase, pure-result representation and rebuilt route. Concrete examples retain old versions and actual opposite-child addresses, and exhibit the baseline duplicate ancestor allocation. |
| Matched endpoint | `insertRunFuel_duplicate_endpoint` proves an identical old nonempty endpoint. The public `insertRun_duplicate_subtree` derives directed membership from independent content under `Ordered`, produces the run, retains the old tree and exact strict-ancestor count, then uses `follow_descendants` for all further probes. Examples use a match with a nonempty child and a deeper failed observation; the premise is not the desired endpoint equality. |
| Physical abort/combined insertion | Nested options separate invalid/fuel failure from duplicate abort and successful insertion. The allocator is called only after recursive success; `handleAbort` occurs at the outer wrapper. `Option.Rel` connects actual outcomes to pure optional traversals, with extension/representation/frontier/route obligations on success. Duplicate results preserve the exact original store/root and report zero cells. Combined retention includes the comparison bound on that same run. The different candidate path and visit count remain explicit. |
| Complete and paired constructors | Independent `Fits` requires exact unfolded size, uniform labels and size balance at every node. Complete execution recurses once per level and stores identical child roots. Paired construction shares a recursively obtained pair and proves its exact logarithmic frontier/visit formulas. No strict-set ordering is imposed on repeated-label trees. Resource statements reuse the existing standard asymptotic adapter. Examples cover sharing, size zero with its allocated companion, unequal children and retained old trees. |
| Pure finite maps | Minimal operators and functional observation laws use the existing `Squares` interface. `OrderedBy Prod.fst` imposes no payload equality or order. Independent whole-tree `observe` is related to directed lookup under ordering; arbitrary directed lookup/update algebra is stated separately. The invariant subtype supplies lawful operators and an explicit finite-domain witness. Rebinding, function payloads, optional-none values and composed update order are checked through public laws. |
| Physical finite maps | Actual key-directed bind/lookup execution has sufficient-fuel and exact-profile proofs. `WrittenAt` adds the endpoint binding and both unchanged child addresses beyond `Rebuilds`' ancestor scope. Its root-replacement application uses two nonempty children and keeps old/new lookup results distinct. `bind_lookup` quantifies every query. Existing relational composition preserves bind failure, missing lookup and stored optional-none at their specified boundaries. |
| Source/proof boundary | The chapter record maps these contracts and their intended domains without equating tree-value equality, address identity, allocated cells, reclaimed live space and Lean runtime behavior. Thesis streams, operational history and later cost obligations retain separate chapter owners. Historical material and suggested unspecified extensions are identified as context. No manuscript copy or new foundational dependency enters the source change. |

The unchanged allocator, copy/update laws, observation adapters, resource pair
type and relational composition definitions were inspected where needed to
establish the new contracts' meaning. None supplies the intended conclusion
as an unexplained assumption. Concrete represented nonempty stores and ordered
trees demonstrate satisfiability; the examples are connected public-theorem
applications, not merely independent numeral calculations. Helper results are
exercised through those public paths, without an artificial example quota.

## Public integration and import prerequisite

`SquareApplications.lean` imports the nine new example modules. Their explicit
imports cover the new stack, signed update, ordered-set/map, shared-tree,
resource, observation and path/terminal modules. `Examples.SharedTree` imports
the resource module directly. There is no added standalone source family left
outside the intended entrypoint closure. The stock coverage check remains a
required integrated validation step; static import inspection is not its result.

The two FRP files are the only existing mathematical implementation files
changed by the prerequisite. A read-only byte comparison confirmed:

- For each file, removing import lines from candidate and
  `70a1477d822efd4fdcec2007280f650bb4695eda` yields byte-identical remainder.
- Each complete candidate file is byte-identical to its counterpart in
  prerequisite `226ebaef53b9eba97bef4b3b6ca364fdea488c69`.

Thus this scope changes neither FRP declarations/proofs nor the toolchain,
dependency pins, audit roots, source policy or acceptance commands. Provider
completeness for affected transitive consumers remains part of full build
validation. No measured performance improvement is asserted by this review.

## Retained preparatory findings

| Stable ID | Standards disposition on this candidate |
| --- | --- |
| CH02-PRE-001 | **Static implementation closure verified.** `PathEndpoint`, `OrderedTerminal` and both connected terminal cases establish the missing matched-root/descendant statement. `Rebuilds.here` was not weakened or misrepresented. Exact-candidate validation remains pending. |
| CH02-PRE-002 | **Static implementation closure verified.** Actual abort and combined traversals, single handler, exact original-state duplicate equations, successful-result relation, retention, same-run comparison bound and concrete cases are present. |
| CH02-PRE-003 | **Static implementation closure verified.** `Map.WrittenAt`, its preservation/prefix laws, `nil_children`, the execution theorem and two-nonempty-child replacement example cover the endpoint obligation separately from ancestor divergence. |
| CH02-PRE-004 | **Static implementation closure verified.** Baseline/optimized/map squares use the existing shared representations and compose with optional root or lookup observations. Retained applications consume those composed contracts. |
| CH02-PRE-005 | **Open mandatory gate.** Complete integrated sources are frozen and match the manifest, but no successful full build/audit record or final candidate verification exists for this candidate. Neither focused builds nor the running prerequisite check close this finding. |

These are this axis's assessments. The coordinator retains the independent
Spec disposition and final validation requirements; this reviewer does not
erase historical preparatory findings or approve other candidate SHAs.

## Validation evidence and limitation

The preserved focused records and terminal logs were inspected. They report
successful pinned-Nix focused closures: pure ordered sets 598 jobs, general
shared constructors 1,587 jobs, signed update/baseline 669 jobs, optimized
physical insertion 672 jobs, pure maps 592 jobs, physical maps 666 jobs, and
terminal retention 665 jobs. AbstractStack's earlier compilation is documented
separately. The JSON records explicitly deny integrated acceptance and retain
the prior failed attempts/corrections; the final log tails agree with the
reported successes. The older constructor observation hash predates the later
shared optional observer; the later signed-update/baseline and optimized
records identify that final observer version. It is not silently treated as
unchanged from the older constructor run.

At inspection, `validation-chapter02/.lake/verification.json` does not exist.
The root-owned full check of `226ebae` is a different prerequisite candidate.
Its eventual success cannot itself approve `69f6f00`. Formal acceptance still
requires the stock exact-candidate complete build, source/coverage and output
guards, exhaustive proof audit, matching success record, and final
`./check.sh --verify-candidate HEAD`, with stable sources, configuration and
dependencies in the isolated checkout.

No build/audit was repeated or launched by this reviewer. Source inspection
found no admissions, newly introduced axioms, unchecked native shortcuts,
unsafe definitions or disabled lint policy, but that is a static assessment;
the exhaustive audit remains mandatory.

## Continuation

For unchanged candidate `69f6f00de204617fdd7feefd5b9ee5b80fc0d9f4`, supply the
successful complete validation log, terminal status, exact verification record
and final verification evidence through the existing coordinator. This axis
can reuse the completed static assessment while reviewing that new evidence.
Any correction requires a new immutable candidate and full-scope reassessment
against the same fixed base, retaining the stable finding record.

**Final Standards status:** Blocked. **Unresolved code/prose findings:** 0.
**Worst outstanding issue:** required exact-candidate validation is incomplete
(retained CH02-PRE-005). **Base:** `82501d108f33c62d21b5e0d0f7d2376b902d8d49`.
**Candidate:** `69f6f00de204617fdd7feefd5b9ee5b80fc0d9f4`.

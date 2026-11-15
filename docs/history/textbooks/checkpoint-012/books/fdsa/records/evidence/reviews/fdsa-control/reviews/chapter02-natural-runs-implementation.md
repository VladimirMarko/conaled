# Chapter 2 natural-run value implementation handoff

## Current state: focused modules and statement review passed; acceptance pending

This component remains inside the existing active Chapter 2 implementation
loop. Both owned modules passed the coordinated one-thread focused build at
`ff9749d1ccbcb0949486f67d6273e28c262280e0`. The same unchanged source then
passed elaborated public-type inspection for the author's statement review.
**Complete candidate validation, independent reviews, acceptance and public
integration remain pending.** There are no admissions or proof placeholders.

The intermediate drafts were saved before checkpoint 0082 and checkpoint
0083. Root then requested an immutable scoped draft commit, transferred the
idle private dependency tree, and released this worker's focused build slot
after the full doctor passed and a device/inode comparison confirmed that
writable artifacts differ from the foundation build's artifacts. The supplied
kit, exact pins, native profile and one-thread setting were preserved.

- Worktree: `conaled-ch02-natural-runs`.
- Branch: `work/fdsa-ch02-natural-runs`.
- Accepted base: `07e480f6ec9958d4975bb90151005b84f2907614`.
- Initial draft, directly above that base: `d1c6a3a314ae772c48ba9ea8acd42624ce913b53`.
- Current checked draft HEAD: `ff9749d1ccbcb0949486f67d6273e28c262280e0`.
- Subsequent commits correct proof elaboration and example syntax only; no
  intended mathematical statement or independently expected output was weakened.
- Owned repository paths: `Applications/Sorting/NaturalRuns.lean` and
  `Examples/NaturalRuns.lean`; both are committed; repository status is clean.
- This handoff is the only control-file path owned by the worker.
- No import roots, pins, coverage, tickets, foundation checkout or other
  implementation worktrees were changed. No GitHub mutation or push occurred.

The first commit command failed with exit 128 because this fresh host had no
configured author identity. An unpublished draft was then made using the
accepted base's historical identity and immediately amended, with the same
tree and parent, when root supplied the current per-command task identity
`ChatGPT <chatgpt@openai.com>`. No shared or global Git configuration changed.
This tooling event supplies no validation or acceptance evidence.

### Closed validation records

The private environment evidence is
`provenance/chapter02-natural-runs-private-environment-20261104/qualified.json`
and `provenance/chapter02-natural-runs-private-doctor-20261104/`. Focused
attempts each preserve the immutable commit, pin/source SHA-256 identities,
actual exit, closed complete log, native start/result records, unchanged-source
confirmation and clean terminal Git status.

| Attempt | Candidate | Actual exit | Concrete outcome |
| --- | --- | --- | --- |
| 1 | `d1c6a3a314ae772c48ba9ea8acd42624ce913b53` | 1 | Found redundant termination tactics and unavailable `Transitive` notation. |
| 2 | `ed6dca0a46da01fa6985b2f2822a2e60226d32e6` | 1 | Explicit transitivity elaborated; remaining failures identified solved-goal fallbacks and dependent ordering case-split indices. |
| 3 | `16865e830d86d6cb980f10e0c7a65e7c2875cdca` | 1 | The full implementation module passed. Examples exposed one tuple annotation syntax error and unused simp arguments. |
| 4 | `ff9749d1ccbcb0949486f67d6273e28c262280e0` | 0 | Both owned modules passed, with every intended connected case intact. |

These are `provenance/chapter02-natural-runs-focused-20261104-attemptN/`.
Attempt 4 completed at `2026-11-04T04:26:28.930418+00:00`; its native elapsed
time was 10.001 seconds. Its full-log SHA-256 is
`96a4eb0e28f302521d3974ac4add552739593d58ad2d01c8dedf5e0a476eddce`.
The only remaining build messages are module-system import advisories; no
linter, proof-checking or warning policy was disabled.

Elaborated public signatures, small adapter definitions and every example
binding were subsequently inspected through `lake env lean --stdin` using the
same qualified one-thread launcher. That command exited 0 with unchanged
sources. Its input, full log and native/terminal records are in
`provenance/chapter02-natural-runs-statements-20261104/`. The inspection
confirms the arbitrary raw function's actual `apply := f`, exact scanner
branch orientation, arbitrary accumulator quantifiers, chronological reverse
in the descending permutation law, absence of payload typeclasses, explicit
worker order premises and explicit nonempty hypotheses for one-run equations.
This is the implementation author's statement review, not an independent
Standards or Spec review and not an exhaustive candidate axiom audit.

## Source and specification read

The exact supplied book was inspected at
`/workspace/scratch/b4a17a285e23/research-source/functional_data_structures_algorithms.pdf`.
Its SHA-256 is
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`,
and its Chapter 2 text is in the adjacent `chapter02.txt`. The natural-run
scanner and D-law source appear on printed pages 21–25 (PDF pages 27–31).

The worker read the repository `AGENTS.md`, architecture/domain/glossary and
relevant ADR guidance, example-driven-development plus worked-example,
implementation and review-loop instructions, and the active Chapter 2 scope,
requirements, obligation/reuse/scanner plans and scope reconciliation.
The exact pinned Batteries DList Basic/Lemmas source was inspected read-only
in the primary environment, along with the actual Lean List APIs. No draft
bottom-up module is imported.

## Draft public surface and statement assessment

The actual source recursion is represented by the mutual `runsBy`, `ascBy`
and `descBy` definitions. For current `a` and next `b`, they test `lt b a`.
An ascending failed boundary emits its current prefix and restarts at
`b :: bs`; a descending failed boundary does the same. Strict keyed descent
uses `fun x y => decide (key x < key y)`, so ties continue ascending and stop
descending. The measures are input length and worker-tail length plus one.

`DListLaw f` is the source law for every raw function
`f (xs ++ ys) = f xs ++ ys`. `dListOfLaw` wraps the actual supplied function
in Batteries.DList; its application is definitionally `f`, and push is the
source composition with cons. It does not evaluate `f []` to manufacture a
replacement executable function. `ascSourceBy` and its equations expose the
source worker for every lawful raw function.

The following proof families passed focused compilation and statement review:

| Family | Intended mathematical statement |
| --- | --- |
| Mutual permutation | Flattened scanner output permutes the input; ascending output permutes `d.toList ++ a :: ys`; descending output permutes `acc.reverse ++ a :: ys`. |
| Multiset | Those permutation laws give complete occurrence equality, including multiplicity; the descending law removes the chronological reversal only after applying reverse-permutation. |
| Flattened length | Input length is preserved; arbitrary workers have prefix/accumulator length plus one plus remaining-tail length. |
| Inner nonemptiness | Every emitted run is nonempty, without comparator order laws. |
| Outer nonemptiness | Worker results are nonempty; scanner output is empty exactly when its input is empty. |
| Run count | Scanner run count is at most input length; worker count is at most remaining-tail length plus one, independently of the supplied prefix size. |
| Sorted blocks | For an arbitrary transitive observation relation, comparator compatibility is required only on the elements currently being scanned. Ascending prefixes retain pairwise order and their upper bound by the current element; descending accumulators retain pairwise order and the current element's lower bound. |
| Keyed wrappers | The generic ordering statements specialize to existing `KeySorted`, then to strict comparisons under a linear order on keys. No order, equality or default value is required on payloads. |
| Raw-builder transfer | Permutation, flattened length and ordering statements transfer to every raw lawful source function, retaining its arbitrary prefix. |
| One-run values | Adjacent false comparisons give a single ascending output; adjacent true comparisons give a single descending output, retaining arbitrary worker accumulators. Initial scanner laws explicitly require nonempty input. Sorted keyed input and strictly descending keyed input specialize these chain laws. |

The worker premises are genuinely arbitrary accumulator premises; they are
not restricted to states reachable from an initial scanner call. Sortedness
is only within individual emitted runs, not of the whole flattened output.
The source's weak descending order invariant is insufficient for stability;
no such stability theorem has been asserted.

## Expected connected cases authored so far

These cases invoke public equations or general results, specify independently
expected outputs, and all passed the focused build.

| Case | Expected output or observation |
| --- | --- |
| Empty payload type | Empty input scans to no runs; no default value or payload equality instance is needed. |
| Singleton `[7]` | Exactly `[[7]]`. |
| Restart `[1,3,2,4]` | Exactly `[[1,3],[2,4]]`, retaining the restart element. |
| Ascending ties `[1,1,2,3]` | Exactly one unchanged run. |
| Strict descent `[4,3,2,1]` | Exactly `[[1,2,3,4]]`, distinguishing permutation from chronological equality. |
| Arbitrary raw builder `[1,3] ++ suffix` | Starting at 5 on `[4,6]` yields `[[1,3,5],[4,6]]`, with no reachability premise on the supplied builder. |
| Arbitrary payload type | Two equal Nat keys retain arbitrary payloads `p` then `q`, without equality, order or default instances on payloads. |
| Mixed records `(3,A),(2,B),(2,C),(1,D)` | Runs are `[(2,B),(3,A)]` and `[(1,D),(2,C)]`; both key-2 records survive in their original relative order. The case connects the multiset, flattened length, nonempty and sorted-block APIs. |
| Weak descent with ties `(3,A),(3,B),(2,C)` | Two runs, not one reversed run. |
| Input-local comparator | A comparator that behaves correctly only on nonnegative keys satisfies the actual input contract and yields sorted blocks; a negative-key example refutes global compatibility. |
| Lawful unsorted prefix `[2,1]` | The output with current element 3 is `[[2,1,3]]`: full occurrences are preserved but it is unsorted. |
| Missing ascending upper bound | Sorted prefix `[2]` with current element 1 produces an unsorted run. |
| Weak descending tie invariant | Arbitrary accumulator `[(2,earlier)]` with current `(2,later)` emits `[(2,later),(2,earlier)]`; the generic sortedness and permutation laws apply, while a direct key-filter observation refutes stability. |

The source statement review has checked the comparator orientation, D-law
quantification, arbitrary prefix semantics, strict/tie boundary, distinction
between per-run order and global order, satisfiability of the worker order
premises and the necessity of their missing-premise counterexamples. The new
one-run laws use the standard `List.IsChain` interface, so the generic value
theorem assumes only the comparisons actually made between adjacent elements;
no transitivity or comparator law is needed for it. The strictly descending
keyed corollary requires only a decidable strict relation and its supplied
pairwise input fact, not global order axioms. The sorted corollary uses the
existing keyed-order contract. Empty input retains zero runs and an explicit
case refutes the one-run equation there. The recorded elaborated-type
inspection confirms these source-level statements.

## Pending work and gates

1. Preserve this clean checked draft and its complete focused/statement
   evidence. The worker is ready for root's durability capture and build-slot
   reassignment; no further optional build or source change is planned.
2. Root owns reconciliation, public imports, complete candidate check/audit,
   independent Standards/Spec reviews, immutable-candidate verification and
   local acceptance. Focused compilation cannot replace those gates.

C02-108–112 construction, invocation and operational bounds remain separate
mandatory followups. Comparison counts, measured scanner correspondence,
composition with the independently validated bottom-up merger, logarithmic
comparison bounds and source runtime transfer are not supplied by these
value proofs. No complete Chapter 2 or component acceptance follows from
this draft. The accepted Chapter 1 state and pending foundation candidate
are unaffected.

# Chapter 2 natural-run value implementation handoff

## Current state: checkpoint 0082 draft, not validated

This is an intermediate source draft in the existing active Chapter 2
implementation loop. It is **not compiled, accepted, integrated, or committed**.
Root requested a safe write hold while the qualified native environment is
hydrated and checkpoint 0082 is captured. No compiler has been invoked by this
worker. Supplied proof scripts are drafts, not evidence that the declarations
elaborate. There are no admissions or deliberate proof placeholders.

- Worktree: `conaled-ch02-natural-runs`.
- Branch: `work/fdsa-ch02-natural-runs`.
- Saved base/HEAD: `07e480f6ec9958d4975bb90151005b84f2907614`.
- Owned repository paths: `Applications/Sorting/NaturalRuns.lean` and
  `Examples/NaturalRuns.lean`; both are currently untracked draft files.
- This handoff is the only control-file path owned by the worker.
- No import roots, pins, coverage, tickets, foundation checkout or other
  implementation worktrees were changed. No GitHub mutation or push occurred.

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

The following proof families are authored but uncompiled:

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

The worker premises are genuinely arbitrary accumulator premises; they are
not restricted to states reachable from an initial scanner call. Sortedness
is only within individual emitted runs, not of the whole flattened output.
The source's weak descending order invariant is insufficient for stability;
no such stability theorem has been asserted.

## Expected connected cases authored so far

These cases invoke the public equations and specify independently expected
outputs. They too are uncompiled.

| Case | Expected output or observation |
| --- | --- |
| Empty payload type | Empty input scans to no runs; no default value or payload equality instance is needed. |
| Singleton `[7]` | Exactly `[[7]]`. |
| Restart `[1,3,2,4]` | Exactly `[[1,3],[2,4]]`, retaining the restart element. |
| Ascending ties `[1,1,2,3]` | Exactly one unchanged run. |
| Strict descent `[4,3,2,1]` | Exactly `[[1,2,3,4]]`, distinguishing permutation from chronological equality. |
| Arbitrary raw builder `[1,3] ++ suffix` | Starting at 5 on `[4,6]` yields `[[1,3,5],[4,6]]`, with no reachability premise on the supplied builder. |

The source statement review has checked the comparator orientation, D-law
quantification, arbitrary prefix semantics, strict/tie boundary and the
distinction between per-run order and global order. Full connected-case
coverage is unfinished: add keyed-record ties, unsorted lawful prefix,
missing-prefix-bound and weak-descending stability counterexamples; connect
the occurrence, length, count and input-local order APIs to those cases.
General one-run laws for nonempty sorted and strictly descending inputs are
also still to be authored. Empty input must retain zero runs.

## Pending work and gates

1. After root releases the write hold, finish connected examples and the
   remaining one-run value laws, without broadening into another component.
2. Use only the coordinated qualified native environment and private project
   outputs. Compile both modules, correct any elaboration/termination/proof
   failures, and record the actual focused build outcome. No output from an
   unqualified or concurrently shared build may be used as acceptance.
3. Reassess all theorem statements after compilation. Preserve full
   occurrence conservation, arbitrary accumulator quantification and minimal
   payload assumptions.
4. Notify root before a scoped local commit and stop promptly for durability
   capture. Root owns reconciliation, public imports, complete candidate
   check/audit, independent Standards/Spec reviews, immutable-candidate
   verification and local acceptance.

C02-108–112 construction, invocation and operational bounds remain separate
mandatory followups. Comparison counts, measured scanner correspondence,
composition with the independently validated bottom-up merger, logarithmic
comparison bounds and source runtime transfer are not supplied by these
value proofs. No complete Chapter 2 or component acceptance follows from
this draft. The accepted Chapter 1 state and pending foundation candidate
are unaffected.

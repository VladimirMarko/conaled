# Bottom-up and tail-pass value implementation

Worker handoff within the existing active Chapter 2 implementation loop,
4 November 2026. The two owned Lean files are a source draft pending actual
Lean elaboration. This report is a static statement review, not an independent
Standards or Spec approval, a complete candidate check, or accepted coverage.

Worktree: `conaled-ch02-bottom-up`, branch `work/fdsa-ch02-bottom-up`.
Accepted starting base: `07e480f6ec9958d4975bb90151005b84f2907614`.
The draft uses only existing accepted sorting modules and pinned standard
dependencies. It does not import other Chapter 2 drafts or the unaccepted
shared-foundation candidate. Ownership is limited to
`Applications/Sorting/BottomUp.lean`, `Examples/BottomUpSorting.lean` and this
handoff. Public root imports, chapter coverage and acceptance remain with root.

## Source and implementation decisions

The worker read the actual pinned PDF's extracted Chapter 2, section 2.5
(printed pp.19–21) and Exercise 2.6 (printed p.29), together with the 112-item
obligation inventory, requirements, mergesort proof/reuse plans and scope
reconciliation. The recovered PDF hash was checked as
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The external source is at `research-source/functional_data_structures_algorithms.pdf`
beside the restored workspace; no extra copy is introduced into the repository.

The worker read `AGENTS.md`, the implementation and review-loop instructions,
the example-driven-development skill including its worked example, architectural
quality/domain guidance, `GLOSSARY.md`, the ADR index and applicable module/audit
ADRs. This is continuation of the assigned implementation subset, with no new
shared unit or enclosing review workflow.

`mergePairsBy` is the literal three-case adjacent-pass recurrence. It keeps
an unpaired final run and combines pairs with canonical `List.merge`.
`mergeAllBy` returns the empty list or sole run at its two base cases and
otherwise recurses on that actual adjacent pass. Its decreasing measure is
the outer run count. `sortBottomUpBy` passes the singleton-run initialization
to `mergeAllBy`.

`mergePairsRevBy` is the permitted append-free tail recurrence. Its empty case
returns the arbitrary accumulator; its singleton case conses that last run;
its two-run case tail-calls itself with the completed merge consed onto the
accumulator. The operation itself contains no append or reverse. Its exact
proposed invariant is:

```
mergePairsRevBy cmp acc xss = (mergePairsBy cmp xss).reverse ++ acc
```

This reverses the outer list of completed runs, not the elements of individual
runs. `mergeAllRevBy` repeatedly calls the tail pass with an empty accumulator;
`sortBottomUpRevBy` initializes it with singleton runs. Their separate value
recurrences are retained. No equality between either pair of whole algorithms
is asserted for arbitrary payloads.

## Proposed source-obligation coverage

These are proposed theorem connections, all still awaiting focused compilation
and the later full chapter gates; they are not tracker closure claims.

| Source obligations | Draft connection |
| --- | --- |
| C02-040–043 | Literal ordinary pass, repeated-pass and singleton-run definitions; public base/step equations; exact ceil-half run count and strict decrease for at least two runs. |
| C02-044 | `multiset_flatten_eq_sum` connects the standard multiset of flattened runs to the standard list sum of inner multisets. No new multiset carrier or accounting foundation. |
| C02-045–047 | Comparator-generic flattened permutation, multiset and length laws for pass, repeated pass and initialized sorter. |
| C02-048–050 | Each-run sortedness preserved by the pass; sorted result from sorted input runs; sorted singleton-initialized result, all with input-local comparator compatibility. |
| C02-054 | `mergePairsBy_uniform_length` retains `Even xss.length` and uniform input length `m`, concluding output lengths `2*m`. Empty runs and `m=0` are allowed. |
| C02-074 | Flattened total length preserved; `mergePairsBy_sum_lengths` also exposes the equal sum of run lengths. |
| C02-105 value/termination part | Actual tail pass/repeated pass/sorter, arbitrary accumulator value law, strict run-count decrease, permutation/multiset and sortedness. The comparison-complexity part remains pending. |
| C02-106 value/support part | Exact arbitrary-accumulator run count, additive flattened multiset and flattened total length; repeated tail pass multiset. Its resource comparison remains pending. |

## Static statement review

The permutation, multiset, run-count and total-length theorems take an arbitrary
Boolean comparator and no order, payload equality decision, injective key map
or inhabitance hypotheses. They compose the actual `List.merge_perm_append`
law through adjacent recursion and repeated passes. The standard multiset
observation retains all occurrence multiplicities.

The pass sortedness theorem observes keys through `[LE κ]` and
`[Std.IsPreorder κ]`, assumes every original run is sorted, and requires the
two comparator branch implications only on members of the original flattened
input. For a recursive pass those membership hypotheses are recovered from
the actual permutation. No global comparator law is added implicitly. The
ordinary keyed specializations require decidable key comparison and
`Std.IsLinearPreorder` on keys. They package sortedness and permutation;
neither is mislabeled as a stable-sort contract.

The arbitrary accumulator value/permutation/multiset equations require no
sortedness at all. The tail-pass each-run sortedness statement separately
requires sorted accumulator runs because they are retained unchanged; it
does not impose cross-run ordering or comparator assumptions on accumulator
members that are never compared by this pass.

The run-count proof counts empty inner lists as runs, preserving the source
termination measure. The uniform-length proof retains the evenness premise.
A single unsorted run remains unchanged by the repeated-pass base case, so
the each-run sortedness premise cannot be removed. No comparison-count,
allocation, stack-space or asymptotic fact follows from these value and length
statements.

## Connected cases and counterexamples

The examples use the public recurrences and laws, with independent expected
data or observations:

- A five-run ragged input includes an empty run, unequal run lengths, two
  occurrences of 2 and an unpaired final run. Its expected adjacent-pass value
  is `[[1,2,3],[0,4],[2,5]]`; law clients separately observe three output runs,
  seven flattened elements and multiplicity two for 2.
- Four equally sized runs exercise the evenness-dependent doubling law.
  Three singleton runs refute the version without evenness. Four empty
  runs have two output runs and zero elements, distinguishing the measures.
- The single unsorted run `[2,1]` refutes sortedness without the source premise.
  The five-element duplicate sorter cases use independent expected sorted
  lists plus permutation uniqueness, for both ordinary and tail variants.
- The accepted nonnegative-domain comparator and its existing local evidence
  exercise both new input-local sortedness laws. Existing signed-key records
  exercise the tail sort correctness contract. Arbitrary payload and constant
  false-comparator clients retain permutation and length without order laws.
- A nonempty accumulator `[[99],[],[42,43]]` checks its exact final position
  after reversed merged runs, six outer runs and ten total elements. An
  unsorted accumulator `[[9,0],[],[7]]` uses the unconditional multiset law.
- Arbitrary payloads at equal key 0 give ordinary output `first,middle,last`
  and tail output `last,first,middle`, by the actual recurrence equations.
  Distinct string payloads then refute stability of the tail sorter using
  the complete equal-key filter observation. A separate three-run example
  refutes equality of the ordinary pass and empty-accumulator tail pass.
- Empty payload type and arbitrary singleton payload clients show that no
  default value, payload order or payload equality decision is required.

## Validation and outstanding work

No Lean compiler or builder has been invoked by this worker. Root is recovering
the pinned native environment and has retained the build hold. The full source
was read back and the statements checked against the pinned obligations. Static
search found no admissions, axioms, unsafe declarations, external implementations
or native decision procedures in the two files. Elaboration, dependency/import
closure and the complete candidate audit are still unestablished.

The draft is deliberately uncommitted while root serializes another worker's
commit and captures the next durability checkpoint. The worker is write-held
after this handoff until root releases edits, a scoped commit or focused builds.

The following remain explicit: C02-051–053 and C02-055–057 comparison formulas
and bounds; the comparison-equivalence/additive formula and same-complexity
part of Exercise 2.6/C02-105–106; integration with the actual measured merge
after that shared dependency passes; subsequent natural-run composition and
its separately required operational claims; complete chapter validation,
independent Standards and Spec reviews, immediate immutable-candidate
verification, and accepted-branch integration. No stability theorem for either
new sorter is claimed from value agreement. The selected C02-107 top-down
stability work is a separate component.
